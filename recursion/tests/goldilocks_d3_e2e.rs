//! End-to-end gate for Goldilocks D3 / Poseidon2 width-12 recursion: two proved layers.
//!
//! The inner proof is a native batch-STARK proof in lrup's config shape (cubic trinomial
//! challenges, W12 hashing, cap height 0, `max_log_arity` 3, `log_final_poly_len` 0, a query proof
//! of work, no batch proof of work) of three toy AIRs:
//!
//! - `Squares` (2^3 rows): a preprocessed column and a public value; sends `(x, x^2 + k)`.
//! - `Cubes` (2^5 rows): a degree-3 constraint `z = x^3`, so its quotient has two chunks; sends
//!   `(x, z)`.
//! - `Lookup` (2^7 rows): receives both, on two global buses.
//!
//! Layer 1 verifies the inner proof in-circuit (`verify_batch_circuit`) and proves that circuit at
//! `D = 3`. Layer 2 verifies the layer-1 proof in-circuit (the D3 backend's
//! `build_next_layer_circuit`) and proves that circuit at `D = 3`. Both layer proofs are verified
//! natively.
//!
//! Negatives: a changed opened value, a changed Merkle sibling and a bad query PoW witness in the
//! inner proof; an inner proof of an invalid trace (honest FRI, failing constraint), rejected by
//! both verifiers at the out-of-domain check; and a tampered layer-1 proof fed to layer 2.
//!
//! The fast tests use `D3FriParams::test_params()`. The ignored
//! `two_layers_at_lrup_parameters` runs the inner proof at lrup's exact parameters and both
//! layers at a 128-bit recursion config, and prints each layer's table heights, times and peak
//! memory.

#[path = "common/goldilocks_d3_config.rs"]
mod goldilocks_d3_config;

use std::time::{Duration, Instant};

use goldilocks_d3_config::{
    Commitment, D, D3FriParams, D3RecursionConfig, DIGEST, EF, F, InputProof, OpeningProof, PERM,
    ProvedLayer, RATE, WIDTH, backend, layer_input, prove_layer_with_stats,
};
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_batch_stark::{
    BatchProof, BatchVerificationError, CommonData, ProverData, StarkInstance, VerificationError,
    prove_batch, verify_batch,
};
use p3_circuit::ops::{NpoTypeId, Poseidon2Trace};
use p3_circuit::tables::Traces;
use p3_circuit::{Circuit, CircuitBuilder, CircuitError, NonPrimitiveOpId};
use p3_circuit_prover::BatchStarkProof;
use p3_field::PrimeCharacteristicRing;
use p3_lookup::logup::LogUpGadget;
use p3_lookup::{Count, InteractionBuilder};
use p3_matrix::dense::RowMajorMatrix;
use p3_recursion::pcs::{FriQueryPaths, set_fri_mmcs_private_data};
use p3_recursion::{
    BatchOnly, BatchStarkVerifierInputsBuilder, FriRecursionConfig, OpeningTranscript,
    PcsRecursionBackend, Poseidon2Config, VerifierCircuitResult, build_next_layer_circuit,
    replay_batch_stark_transcript, verify_batch_circuit,
};

// ---------------------------------------------------------------------------------------------
// Toy AIRs
// ---------------------------------------------------------------------------------------------

const SQUARES_ROWS: usize = 1 << 3;
const CUBES_ROWS: usize = 1 << 5;
const LOOKUP_ROWS: usize = 1 << 7;
const SQUARES_BUS: &str = "d3-e2e-squares";
const CUBES_BUS: &str = "d3-e2e-cubes";
/// `Squares`' first `x`, its public value.
const X0: u64 = 5;
/// `Cubes`' first `x`, fixed by its AIR.
const C0: u64 = 11;
/// The index of `Cubes` among the AIRs.
const CUBES: usize = 1;

#[derive(Clone, Copy)]
enum ToyAir {
    /// Main `(x, y)`, preprocessed `k_i = 3i + 1`, public value `x_0`. Constraints:
    /// `x_0 = pv[0]`, `x' = x + 1`, `y = x^2 + k`. Sends `(x, y)` on every row.
    Squares,
    /// Main `(x, z)`. Constraints: `x_0 = C0`, `x' = x + 1`, `z = x^3` (degree 3). Sends `(x, z)`
    /// on every row.
    Cubes,
    /// Main `(a, b, s, c, e, t)` with `s`, `t` boolean. Receives `(a, b)` from `Squares` with
    /// multiplicity `s` and `(c, e)` from `Cubes` with multiplicity `t`.
    Lookup,
}

impl<Fl: p3_field::Field> BaseAir<Fl> for ToyAir {
    fn width(&self) -> usize {
        match self {
            Self::Squares | Self::Cubes => 2,
            Self::Lookup => 6,
        }
    }

    fn num_public_values(&self) -> usize {
        match self {
            Self::Squares => 1,
            Self::Cubes | Self::Lookup => 0,
        }
    }

    fn preprocessed_width(&self) -> usize {
        match self {
            Self::Squares => 1,
            Self::Cubes | Self::Lookup => 0,
        }
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<Fl>> {
        match self {
            Self::Squares => Some(RowMajorMatrix::new_col(
                (0..SQUARES_ROWS)
                    .map(|i| Fl::from_usize(3 * i + 1))
                    .collect(),
            )),
            Self::Cubes | Self::Lookup => None,
        }
    }
}

impl<AB: AirBuilder + InteractionBuilder> Air<AB> for ToyAir
where
    AB::F: p3_field::Field,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        match self {
            Self::Squares => {
                let x = main.current(0).unwrap();
                let y = main.current(1).unwrap();
                let x_next = main.next(0).unwrap();
                let k = builder.preprocessed().clone().current(0).unwrap();
                let x0 = builder.public_values()[0];
                builder.when_first_row().assert_eq(x, x0);
                builder
                    .when_transition()
                    .assert_eq(x_next, x.into() + AB::Expr::ONE);
                builder.assert_eq(y, x.into() * x.into() + k.into());
                builder.push_interaction(SQUARES_BUS, [x.into(), y.into()], -1);
            }
            Self::Cubes => {
                let x = main.current(0).unwrap();
                let z = main.current(1).unwrap();
                let x_next = main.next(0).unwrap();
                builder
                    .when_first_row()
                    .assert_eq(x, AB::Expr::from_u64(C0));
                builder
                    .when_transition()
                    .assert_eq(x_next, x.into() + AB::Expr::ONE);
                builder.assert_eq(z, x.into() * x.into() * x.into());
                builder.push_interaction(CUBES_BUS, [x.into(), z.into()], -1);
            }
            Self::Lookup => {
                let a = main.current(0).unwrap();
                let b = main.current(1).unwrap();
                let s = main.current(2).unwrap();
                let c = main.current(3).unwrap();
                let e = main.current(4).unwrap();
                let t = main.current(5).unwrap();
                builder.assert_bool(s);
                builder.assert_bool(t);
                builder.push_interaction(
                    SQUARES_BUS,
                    [a.into(), b.into()],
                    Count::bounded(s.into(), 1),
                );
                builder.push_interaction(
                    CUBES_BUS,
                    [c.into(), e.into()],
                    Count::bounded(t.into(), 1),
                );
            }
        }
    }
}

fn squares_row(i: usize) -> (F, F) {
    let x = F::from_u64(X0 + i as u64);
    (x, x * x + F::from_usize(3 * i + 1))
}

fn cubes_row(i: usize) -> (F, F) {
    let x = F::from_u64(C0 + i as u64);
    (x, x * x * x)
}

/// The toy traces. With `broken_cube = Some(i)`, `Cubes` row `i` has `z = x^3 + 1`, and `Lookup`
/// receives that changed message: the buses still balance, but `z = x^3` fails on that row.
fn toy_traces(broken_cube: Option<usize>) -> [RowMajorMatrix<F>; 3] {
    let cube = |i: usize| {
        let (x, z) = cubes_row(i);
        (
            x,
            if broken_cube == Some(i) {
                z + F::ONE
            } else {
                z
            },
        )
    };
    let squares = (0..SQUARES_ROWS)
        .flat_map(|i| {
            let (x, y) = squares_row(i);
            [x, y]
        })
        .collect();
    let cubes = (0..CUBES_ROWS)
        .flat_map(|i| {
            let (x, z) = cube(i);
            [x, z]
        })
        .collect();
    // Every `Squares` and `Cubes` row once (in reverse order), then unused rows.
    let lookup = (0..LOOKUP_ROWS)
        .flat_map(|i| {
            let (a, b, s) = if i < SQUARES_ROWS {
                let (x, y) = squares_row(SQUARES_ROWS - 1 - i);
                (x, y, F::ONE)
            } else {
                (F::from_usize(i), F::from_usize(7 * i + 2), F::ZERO)
            };
            let (c, e, t) = if i < CUBES_ROWS {
                let (x, z) = cube(CUBES_ROWS - 1 - i);
                (x, z, F::ONE)
            } else {
                (F::from_usize(2 * i), F::from_usize(5 * i + 1), F::ZERO)
            };
            [a, b, s, c, e, t]
        })
        .collect();
    [
        RowMajorMatrix::new(squares, 2),
        RowMajorMatrix::new(cubes, 2),
        RowMajorMatrix::new(lookup, 6),
    ]
}

struct ToyProof {
    config: D3RecursionConfig,
    airs: [ToyAir; 3],
    public_values: Vec<Vec<F>>,
    prover_data: ProverData<D3RecursionConfig>,
    proof: BatchProof<D3RecursionConfig>,
}

impl ToyProof {
    /// The honest toy proof; the native verifier accepts it.
    fn new(params: D3FriParams) -> Self {
        let toy = Self::prove(params, None);
        verify_batch(
            &toy.config,
            &toy.airs,
            &toy.proof,
            &toy.public_values,
            toy.common(),
        )
        .expect("the native D3 toy proof verifies");
        toy
    }

    fn prove(params: D3FriParams, broken_cube: Option<usize>) -> Self {
        let config = D3RecursionConfig::new(params);
        let airs = [ToyAir::Squares, ToyAir::Cubes, ToyAir::Lookup];
        let traces = toy_traces(broken_cube);
        let public_values = vec![vec![F::from_u64(X0)], vec![], vec![]];
        let instances: Vec<_> = airs
            .iter()
            .zip(&traces)
            .zip(&public_values)
            .map(|((air, trace), pv)| StarkInstance {
                air,
                trace,
                public_values: pv.clone(),
            })
            .collect();
        let prover_data = ProverData::from_instances(&config, &instances).unwrap();
        let proof = prove_batch(&config, &instances, &prover_data).unwrap();
        // Mixed heights, every AIR on a global bus, and a multi-chunk quotient for `Cubes`.
        assert_eq!(proof.degree_bits, vec![3, 5, 7]);
        assert!(proof.lookup_terminals.iter().all(Option::is_some));
        let quotient_chunks: Vec<_> = proof
            .opened_values
            .instances
            .iter()
            .map(|instance| instance.base_opened_values.quotient_chunks.len())
            .collect();
        assert!(
            quotient_chunks[CUBES] > 1,
            "quotient chunks {quotient_chunks:?}"
        );
        assert!(
            proof.opened_values.instances[0]
                .base_opened_values
                .preprocessed
                .is_some()
        );
        Self {
            config,
            airs,
            public_values,
            prover_data,
            proof,
        }
    }

    const fn common(&self) -> &CommonData<D3RecursionConfig> {
        &self.prover_data.common
    }

    fn verify_natively(
        &self,
        proof: &BatchProof<D3RecursionConfig>,
    ) -> Result<(), BatchVerificationError<impl core::fmt::Debug>> {
        verify_batch(
            &self.config,
            &self.airs,
            proof,
            &self.public_values,
            self.common(),
        )
    }

    /// The native transcript of `proof` (this toy's proof or a changed copy), replayed up to
    /// the PCS verification.
    fn transcript(
        &self,
        proof: &BatchProof<D3RecursionConfig>,
    ) -> OpeningTranscript<D3RecursionConfig> {
        replay_batch_stark_transcript(
            &self.airs,
            &self.config,
            proof,
            &self.public_values,
            self.common(),
            &LogUpGadget,
        )
        .expect("the native transcript replays")
        .0
    }

    fn query_paths(&self) -> Vec<FriQueryPaths<F, DIGEST>> {
        self.config
            .query_paths(&self.proof.opening_proof, self.transcript(&self.proof))
    }
}

// ---------------------------------------------------------------------------------------------
// Layer 1: the inner proof's verifier circuit
// ---------------------------------------------------------------------------------------------

struct VerifierCircuit {
    circuit: Circuit<EF>,
    mmcs_op_ids: Vec<NonPrimitiveOpId>,
    public_inputs: Vec<EF>,
    private_inputs: Vec<EF>,
}

/// Build the verifier circuit for `toy` and pack the circuit inputs from `proof` (the toy's own
/// proof, or a changed copy of it).
fn verifier_circuit(toy: &ToyProof, proof: &BatchProof<D3RecursionConfig>) -> VerifierCircuit {
    let mut builder = CircuitBuilder::<EF>::new();
    toy.config
        .prepare_circuit_for_verification(&mut builder)
        .unwrap();
    let inputs =
        BatchStarkVerifierInputsBuilder::<D3RecursionConfig, Commitment, OpeningProof>::allocate(
            &mut builder,
            proof,
            toy.common(),
            &[1, 0, 0],
        )
        .expect("verifier inputs allocate");
    let mmcs_op_ids = verify_batch_circuit::<
        ToyAir,
        D3RecursionConfig,
        Commitment,
        InputProof,
        OpeningProof,
        LogUpGadget,
        Poseidon2Config,
        WIDTH,
        RATE,
    >(
        &toy.config,
        &toy.airs,
        &mut builder,
        &inputs.proof_targets,
        &inputs.air_public_targets,
        toy.config.pcs_verifier_params(),
        &inputs.common_data,
        &LogUpGadget,
        PERM,
    )
    .expect("the D3 verifier circuit builds");
    let circuit = builder.build().expect("the D3 verifier circuit compiles");
    let (public_inputs, private_inputs) =
        inputs.pack_values(&toy.public_values, proof, toy.common());
    VerifierCircuit {
        circuit,
        mmcs_op_ids,
        public_inputs,
        private_inputs,
    }
}

impl VerifierCircuit {
    fn run(&self, query_paths: &[FriQueryPaths<F, DIGEST>]) -> Result<Traces<EF>, CircuitError> {
        let mut runner = self.circuit.runner();
        runner.set_public_inputs(&self.public_inputs)?;
        runner.set_private_inputs(&self.private_inputs)?;
        set_fri_mmcs_private_data::<F, EF, DIGEST>(
            &mut runner,
            &self.mmcs_op_ids,
            query_paths,
            PERM,
        )
        .expect("the query paths fit the circuit's MMCS operations");
        runner.run()
    }
}

// ---------------------------------------------------------------------------------------------
// Layer 2: the layer-1 proof's verifier circuit, built by the D3 backend
// ---------------------------------------------------------------------------------------------

/// The layer-2 verifier circuit and the outcome of running it.
struct NextLayerRun {
    circuit: Circuit<EF>,
    build: Duration,
    run: Duration,
    traces: Result<Traces<EF>, String>,
}

/// Build the next-layer verifier circuit of `layer` (proved under `config`) and run it. The
/// circuit inputs come from `inputs_from` and the FRI Merkle paths from `paths_from`; both are
/// `layer` for an honest run.
fn run_next_layer(
    config: &D3RecursionConfig,
    layer: &BatchStarkProof<D3RecursionConfig>,
    inputs_from: &BatchStarkProof<D3RecursionConfig>,
    paths_from: &BatchStarkProof<D3RecursionConfig>,
) -> NextLayerRun {
    let backend = backend();
    let prev = layer_input(layer);
    let start = Instant::now();
    let (circuit, result) = build_next_layer_circuit::<_, _, _, D>(&prev, config, &backend)
        .expect("the D3 backend builds the layer verifier circuit");
    let build = start.elapsed();
    let inputs = layer_input(inputs_from);
    let paths = layer_input(paths_from);
    let start = Instant::now();
    let traces = (|| {
        let mut runner = circuit.runner();
        runner
            .set_public_inputs(&result.pack_public_inputs(&inputs).unwrap())
            .map_err(|e| format!("public inputs: {e}"))?;
        runner
            .set_private_inputs(&result.pack_private_inputs(&inputs).unwrap())
            .map_err(|e| format!("private inputs: {e}"))?;
        PcsRecursionBackend::<D3RecursionConfig, BatchOnly, D>::set_private_data_for_result(
            &backend,
            config,
            &mut runner,
            &result,
            &paths,
        )
        .map_err(|e| format!("private data: {e}"))?;
        runner.run().map_err(|e| format!("execution: {e}"))
    })();
    NextLayerRun {
        circuit,
        build,
        run: start.elapsed(),
        traces,
    }
}

// ---------------------------------------------------------------------------------------------
// Measurements
// ---------------------------------------------------------------------------------------------

/// Reset this process's peak resident set size (Linux `clear_refs` 5); a no-op elsewhere.
fn reset_peak_rss() {
    let _ = std::fs::write("/proc/self/clear_refs", "5");
}

/// This process's peak resident set size since the last reset, in MiB (Linux `VmHWM`).
fn peak_rss_mib() -> Option<u64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    let line = status.lines().find(|line| line.starts_with("VmHWM:"))?;
    let kib: u64 = line.split_whitespace().nth(1)?.parse().ok()?;
    Some(kib / 1024)
}

fn permutations(traces: &Traces<EF>) -> [usize; 2] {
    [PERM.for_challenger(), PERM].map(|config| {
        traces
            .non_primitive_trace::<Poseidon2Trace<F>>(&NpoTypeId::poseidon2_perm(config))
            .map_or(0, |trace| trace.operations.len())
    })
}

fn report(
    name: &str,
    params: D3FriParams,
    build: Duration,
    run: Duration,
    traces: &Traces<EF>,
    layer: &ProvedLayer,
) {
    let proof = &layer.proof;
    let [challenger, ordinary] = permutations(traces);
    let rows: Vec<usize> = proof.rows.iter().collect();
    eprintln!("== {name} (proved with {params:?})");
    eprintln!(
        "   circuit build {build:.2?}, execution {run:.2?}, prepare {:.2?}, prove {:.2?}, \
         native verify {:.2?}, peak RSS {} MiB",
        layer.prepare,
        layer.prove,
        layer.verify,
        peak_rss_mib().map_or_else(|| "n/a".to_string(), |mib| mib.to_string()),
    );
    eprintln!("   permutations: challenger {challenger}, ordinary {ordinary}");
    eprintln!("   primitive rows (Const, Public, ALU): {rows:?}");
    for entry in &proof.non_primitives {
        eprintln!(
            "   non-primitive {}: {} rows, {} lanes",
            entry.op_type, entry.rows, entry.lanes
        );
    }
    eprintln!(
        "   committed degree bits per table: {:?}",
        proof.proof.degree_bits
    );
}

/// Both proved layers.
struct TwoLayers {
    layer1: ProvedLayer,
    layer2: ProvedLayer,
}

/// The inner proof under `inner`, then layers 1 and 2, each proved under `layer` and verified
/// natively. Prints each layer's measurements.
fn two_layers(inner: D3FriParams, layer: D3FriParams) -> TwoLayers {
    reset_peak_rss();
    let start = Instant::now();
    let toy = ToyProof::new(inner);
    eprintln!(
        "== inner native proof ({inner:?}): prove + verify {:.2?}, peak RSS {} MiB",
        start.elapsed(),
        peak_rss_mib().map_or_else(|| "n/a".to_string(), |mib| mib.to_string()),
    );

    // Layer 1: verify the inner proof in-circuit and prove that circuit.
    reset_peak_rss();
    let layer1_config = D3RecursionConfig::new(layer);
    let (layer1, layer1_circuit_size) = {
        let start = Instant::now();
        let verifier = verifier_circuit(&toy, &toy.proof);
        let build = start.elapsed();
        let query_paths = toy.query_paths();
        let start = Instant::now();
        let traces = verifier
            .run(&query_paths)
            .expect("the inner proof's verifier circuit runs");
        let run = start.elapsed();
        let proved = prove_layer_with_stats(&layer1_config, &verifier.circuit, &traces);
        report("layer 1", layer, build, run, &traces, &proved);
        (proved, permutations(&traces))
    };

    // Layer 2: verify the layer-1 proof in-circuit and prove that circuit.
    reset_peak_rss();
    let layer2_config = D3RecursionConfig::new(layer);
    let layer2 = {
        let NextLayerRun {
            circuit,
            build,
            run,
            traces,
        } = run_next_layer(&layer1_config, &layer1.proof, &layer1.proof, &layer1.proof);
        let traces = traces.expect("the layer-1 proof's verifier circuit runs");
        let proved = prove_layer_with_stats(&layer2_config, &circuit, &traces);
        report("layer 2", layer, build, run, &traces, &proved);
        assert!(
            permutations(&traces)[1] > layer1_circuit_size[1],
            "layer 2 verifies a larger proof than layer 1"
        );
        proved
    };
    TwoLayers { layer1, layer2 }
}

// ---------------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------------

#[test]
fn two_layers_prove_and_verify() {
    let layers = two_layers(D3FriParams::test_params(), D3FriParams::test_params());
    assert_eq!(layers.layer1.proof.ext_degree, D);
    assert_eq!(layers.layer2.proof.ext_degree, D);
}

/// Layers 1 and 2 over an inner proof at lrup's exact parameters, each layer at a 128-bit
/// recursion config (rate 1/4, 157 queries, 22-bit query PoW). Run explicitly, on one thread,
/// to record the per-layer table heights, times and peak memory.
#[test]
#[ignore = "slow: lrup's inner parameters and 128-bit recursion layers; run with --ignored"]
fn two_layers_at_lrup_parameters() {
    let inner = D3FriParams::lrup_inner_params();
    let config = D3RecursionConfig::new(inner);
    let fri = config.fri_params();
    // lrup-backend-p3 `make_config`.
    assert_eq!(
        (
            fri.log_blowup,
            fri.num_queries,
            fri.query_proof_of_work_bits,
            fri.max_log_arity,
            fri.log_final_poly_len,
            fri.commit_proof_of_work_bits,
            fri.batch_proof_of_work_bits,
        ),
        (1, 256, 22, 3, 0, 0, 0)
    );
    two_layers(inner, D3FriParams::recursion_layer_params());
}

/// A changed opened value changes the transcript the circuit replays, so the query PoW check or
/// the Merkle checks of the moved query indices fail at execution. The native verifier rejects
/// the same proof.
#[test]
fn changed_opened_value_is_rejected() {
    let toy = ToyProof::new(D3FriParams::test_params());
    let honest_paths = toy.query_paths();
    for instance in 0..toy.airs.len() {
        let mut proof = ToyProof::new(D3FriParams::test_params()).proof;
        proof.opened_values.instances[instance]
            .base_opened_values
            .trace_local[1] += EF::ONE;
        assert!(
            toy.verify_natively(&proof).is_err(),
            "AIR {instance}: the native verifier rejects"
        );
        let error = verifier_circuit(&toy, &proof)
            .run(&honest_paths)
            .expect_err("a changed opened value must fail execution");
        eprintln!("changed opened value (AIR {instance}): {error}");
    }
}

#[test]
fn changed_merkle_sibling_is_rejected() {
    let toy = ToyProof::new(D3FriParams::test_params());
    let verifier = verifier_circuit(&toy, &toy.proof);
    let honest = toy.query_paths();
    // In-circuit: a sibling of an input (trace) opening and of a commit-phase opening.
    for (input, place) in [(true, "input batch"), (false, "commit phase")] {
        let mut paths = honest.clone();
        let chain = if input {
            &mut paths[0].input[0]
        } else {
            &mut paths[0].commit_phase[0]
        };
        chain[0][0] += F::ONE;
        let error = verifier
            .run(&paths)
            .expect_err("a changed Merkle sibling must fail execution");
        eprintln!("changed {place} sibling: {error}");
    }
    // Natively: the same kind of change in the proof's pruned input and commit-phase paths.
    for input in [true, false] {
        let mut proof = ToyProof::new(D3FriParams::test_params()).proof;
        let siblings = if input {
            &mut proof.opening_proof.input_openings[0]
                .opening_proof
                .sibling_hashes
        } else {
            &mut proof.opening_proof.commit_phase_openings[0]
                .opening_proof
                .sibling_hashes
        };
        siblings[0][0] += F::ONE;
        assert!(
            toy.verify_natively(&proof).is_err(),
            "the native verifier rejects a changed sibling"
        );
    }
}

#[test]
fn bad_query_pow_witness_is_rejected() {
    let toy = ToyProof::new(D3FriParams::test_params());
    let query_paths = toy.query_paths();
    let mut proof = ToyProof::new(D3FriParams::test_params()).proof;
    proof.opening_proof.query_pow_witness += F::ONE;
    assert!(
        toy.verify_natively(&proof).is_err(),
        "the native verifier rejects the changed witness"
    );
    let error = verifier_circuit(&toy, &proof)
        .run(&query_paths)
        .expect_err("a bad query PoW witness must fail execution");
    eprintln!("bad query PoW witness: {error}");
}

/// A proof of a trace that breaks `z = x^3` on one `Cubes` row, with the buses balanced. The
/// quotient is still a low-degree polynomial, so FRI, its proof of work and its Merkle paths are
/// all honest; only the out-of-domain check `C(zeta) = Z_H(zeta) q(zeta)` fails. The native
/// verifier rejects there, and the in-circuit verifier fails the same check at execution (a
/// witness conflict on the connected quotient value; every other check passes).
#[test]
#[cfg_attr(
    debug_assertions,
    ignore = "debug provers check the constraints and panic before a proof exists"
)]
fn invalid_trace_is_rejected_at_the_ood_check() {
    let params = D3FriParams::test_params();
    let toy = ToyProof::prove(params, Some(CUBES_ROWS / 2));
    let native = toy.verify_natively(&toy.proof);
    assert!(
        matches!(
            native,
            Err(BatchVerificationError::Verification(
                VerificationError::OodEvaluationMismatch { index: Some(CUBES) }
            ))
        ),
        "the native verifier rejects at the OOD check of `Cubes`: {native:?}"
    );
    // FRI is honest: the query PoW, the commit-phase folding and the paths all check natively.
    let query_paths = toy
        .config
        .try_query_paths(&toy.proof.opening_proof, toy.transcript(&toy.proof))
        .expect("the invalid trace's FRI proof is honest");
    let error = verifier_circuit(&toy, &toy.proof)
        .run(&query_paths)
        .expect_err("an invalid trace must fail execution");
    assert!(
        matches!(error, CircuitError::WitnessConflict { .. }),
        "the failing check is a connection, not a hash or PoW operation: {error}"
    );
    eprintln!("invalid trace: {error}");

    // The same circuit shape accepts the honest proof.
    let honest = ToyProof::new(params);
    verifier_circuit(&honest, &honest.proof)
        .run(&honest.query_paths())
        .expect("the honest proof's verifier circuit runs");
}

/// A layer-1 proof with one changed opened value. The native verifier rejects it, its FRI paths do
/// not restore (the backend refuses to set the layer-2 private data), and with the honest proof's
/// paths the layer-2 verifier circuit fails at execution.
#[test]
fn tampered_layer1_proof_is_rejected_by_layer2() {
    let params = D3FriParams::test_params();
    let toy = ToyProof::new(params);
    let layer1_config = D3RecursionConfig::new(params);
    let layer1 = {
        let verifier = verifier_circuit(&toy, &toy.proof);
        let traces = verifier.run(&toy.query_paths()).unwrap();
        prove_layer_with_stats(&layer1_config, &verifier.circuit, &traces)
    };
    // The honest layer-1 proof runs through layer 2.
    run_next_layer(&layer1_config, &layer1.proof, &layer1.proof, &layer1.proof)
        .traces
        .expect("the honest layer-1 proof's verifier circuit runs");
    layer1
        .verifier
        .verify(&clone_layer(&layer1.proof), &[])
        .expect("an unchanged copy verifies");

    // Change an opened value of every table in turn (primitive and non-primitive).
    for table in 0..layer1.proof.proof.opened_values.instances.len() {
        let mut tampered = clone_layer(&layer1.proof);
        tampered.proof.opened_values.instances[table]
            .base_opened_values
            .trace_local[0] += EF::ONE;
        assert!(
            layer1.verifier.verify(&tampered, &[]).is_err(),
            "table {table}: the native verifier rejects"
        );
        let own_paths = run_next_layer(&layer1_config, &layer1.proof, &tampered, &tampered)
            .traces
            .expect_err("the tampered proof must be rejected");
        assert!(own_paths.starts_with("private data"), "{own_paths}");
        let honest_paths = run_next_layer(&layer1_config, &layer1.proof, &tampered, &layer1.proof)
            .traces
            .expect_err("the tampered proof must fail layer-2 execution");
        assert!(honest_paths.starts_with("execution"), "{honest_paths}");
        eprintln!("tampered layer-1 table {table}: {own_paths} / {honest_paths}");
    }
}

fn clone_layer(proof: &BatchStarkProof<D3RecursionConfig>) -> BatchStarkProof<D3RecursionConfig> {
    // `BatchStarkProof` is serde-only; round-trip it.
    postcard::from_bytes(&postcard::to_allocvec(proof).unwrap()).unwrap()
}
