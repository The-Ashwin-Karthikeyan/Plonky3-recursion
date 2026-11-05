//! The D3 end-to-end pipeline shared by the D3 recursion tests: three toy AIRs and their native
//! inner proof, layer 1 (the inner proof's verifier circuit) and layer 2 (the layer-1 proof's
//! verifier circuit, built by the D3 backend), plus memory measurements. Moved out of
//! `goldilocks_d3_e2e.rs` unchanged so `goldilocks_d3_zk.rs` can reuse it.
//!
//! The including test crate must also declare `mod goldilocks_d3_config` (see that file).

#![allow(dead_code)]

use std::time::{Duration, Instant};

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_batch_stark::{
    BatchProof, BatchVerificationError, CommonData, ProverData, StarkInstance, prove_batch,
    verify_batch,
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

use crate::goldilocks_d3_config::{
    Commitment, D, D3FriParams, D3RecursionConfig, DIGEST, EF, F, InputProof, OpeningProof, PERM,
    RATE, WIDTH, backend, layer_input,
};

// ---------------------------------------------------------------------------------------------
// Toy AIRs
// ---------------------------------------------------------------------------------------------

pub const SQUARES_ROWS: usize = 1 << 3;
pub const CUBES_ROWS: usize = 1 << 5;
pub const LOOKUP_ROWS: usize = 1 << 7;
pub const SQUARES_BUS: &str = "d3-e2e-squares";
pub const CUBES_BUS: &str = "d3-e2e-cubes";
/// `Squares`' first `x`, its public value.
pub const X0: u64 = 5;
/// `Cubes`' first `x`, fixed by its AIR.
pub const C0: u64 = 11;
/// The index of `Cubes` among the AIRs.
pub const CUBES: usize = 1;

#[derive(Clone, Copy)]
pub enum ToyAir {
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

pub fn squares_row(i: usize) -> (F, F) {
    let x = F::from_u64(X0 + i as u64);
    (x, x * x + F::from_usize(3 * i + 1))
}

pub fn cubes_row(i: usize) -> (F, F) {
    let x = F::from_u64(C0 + i as u64);
    (x, x * x * x)
}

/// The toy traces. With `broken_cube = Some(i)`, `Cubes` row `i` has `z = x^3 + 1`, and `Lookup`
/// receives that changed message: the buses still balance, but `z = x^3` fails on that row.
pub fn toy_traces(broken_cube: Option<usize>) -> [RowMajorMatrix<F>; 3] {
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

pub struct ToyProof {
    pub config: D3RecursionConfig,
    pub airs: [ToyAir; 3],
    pub public_values: Vec<Vec<F>>,
    pub prover_data: ProverData<D3RecursionConfig>,
    pub proof: BatchProof<D3RecursionConfig>,
}

impl ToyProof {
    /// The honest toy proof; the native verifier accepts it.
    pub fn new(params: D3FriParams) -> Self {
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

    pub fn prove(params: D3FriParams, broken_cube: Option<usize>) -> Self {
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

    pub const fn common(&self) -> &CommonData<D3RecursionConfig> {
        &self.prover_data.common
    }

    pub fn verify_natively(
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
    pub fn transcript(
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

    pub fn query_paths(&self) -> Vec<FriQueryPaths<F, DIGEST>> {
        self.config
            .query_paths(&self.proof.opening_proof, self.transcript(&self.proof))
    }
}

// ---------------------------------------------------------------------------------------------
// Layer 1: the inner proof's verifier circuit
// ---------------------------------------------------------------------------------------------

pub struct VerifierCircuit {
    pub circuit: Circuit<EF>,
    pub mmcs_op_ids: Vec<NonPrimitiveOpId>,
    pub public_inputs: Vec<EF>,
    pub private_inputs: Vec<EF>,
}

/// Build the verifier circuit for `toy` and pack the circuit inputs from `proof` (the toy's own
/// proof, or a changed copy of it).
pub fn verifier_circuit(toy: &ToyProof, proof: &BatchProof<D3RecursionConfig>) -> VerifierCircuit {
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
    pub fn run(
        &self,
        query_paths: &[FriQueryPaths<F, DIGEST>],
    ) -> Result<Traces<EF>, CircuitError> {
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
pub struct NextLayerRun {
    pub circuit: Circuit<EF>,
    pub build: Duration,
    pub run: Duration,
    pub traces: Result<Traces<EF>, String>,
}

/// Build the next-layer verifier circuit of `layer` (proved under `config`) and run it. The
/// circuit inputs come from `inputs_from` and the FRI Merkle paths from `paths_from`; both are
/// `layer` for an honest run.
pub fn run_next_layer(
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
pub fn reset_peak_rss() {
    let _ = std::fs::write("/proc/self/clear_refs", "5");
}

/// This process's peak resident set size since the last reset, in MiB (Linux `VmHWM`).
pub fn peak_rss_mib() -> Option<u64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    let line = status.lines().find(|line| line.starts_with("VmHWM:"))?;
    let kib: u64 = line.split_whitespace().nth(1)?.parse().ok()?;
    Some(kib / 1024)
}

pub fn permutations(traces: &Traces<EF>) -> [usize; 2] {
    [PERM.for_challenger(), PERM].map(|config| {
        traces
            .non_primitive_trace::<Poseidon2Trace<F>>(&NpoTypeId::poseidon2_perm(config))
            .map_or(0, |trace| trace.operations.len())
    })
}
