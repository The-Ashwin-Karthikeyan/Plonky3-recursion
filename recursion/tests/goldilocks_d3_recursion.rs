//! In-circuit verification of Goldilocks D3 / Poseidon2 width-12 batch-STARK proofs.
//!
//! The native proofs use `CubicTrinomialExtensionField<Goldilocks>` challenges and
//! p3-goldilocks' reference width-12 permutation (rate 6, 6-element digests, cap height 0, a
//! `DuplexChallenger<_, _, 12, 6>`), with FRI in lrup's shape: folding arity up to 8
//! (`max_log_arity` 3), `log_final_poly_len` 0 and a query proof of work, which the circuit
//! checks. The parameters are otherwise small, so the tests stay fast.
//!
//! - A native batch proof of two toy AIRs (different heights, a preprocessed column, a global
//!   lookup between them, a public value) is verified with `verify_batch_circuit` over the cubic
//!   extension. The verification circuit is then proved by circuit-prover at `D = 3` with the
//!   tables the D3 recursion backend registers, and the proof is verified natively.
//! - Negatives: a changed opened value, a changed Merkle sibling, a bad query PoW witness and an
//!   unbalanced global lookup each make the verification circuit fail to execute.
//! - The D3 backend (`FriRecursionBackendForExt<3, ..>`) captures and validates the prepared input
//!   contract of that circuit proof and builds its verifier circuit, which runs. The second layer
//!   is proved in `goldilocks_d3_e2e.rs`.
//!
//! The recursion config is shared with `goldilocks_d3_e2e.rs` (`common/goldilocks_d3_config.rs`).

#[path = "common/goldilocks_d3_config.rs"]
mod goldilocks_d3_config;

use goldilocks_d3_config::{
    Commitment, D, D3FriParams, D3RecursionConfig, DIGEST, EF, F, InputProof, OpeningProof, PERM,
    RATE, WIDTH, backend, layer_input, prove_layer,
};
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_batch_stark::{
    BatchProof, CommonData, ProverData, StarkInstance, prove_batch, verify_batch,
};
use p3_circuit::ops::{NpoTypeId, Poseidon2Trace};
use p3_circuit::{Circuit, CircuitBuilder, CircuitError, NonPrimitiveOpId};
use p3_circuit_prover::BatchStarkProof;
use p3_field::PrimeCharacteristicRing;
use p3_lookup::logup::LogUpGadget;
use p3_lookup::{Count, InteractionBuilder};
use p3_matrix::dense::RowMajorMatrix;
use p3_recursion::pcs::{FriQueryPaths, set_fri_mmcs_private_data};
use p3_recursion::{
    BatchOnly, BatchStarkVerifierInputsBuilder, FriRecursionBackend, FriRecursionConfig,
    OpeningTranscript, PcsRecursionBackend, Poseidon2Config, PreparedInput,
    PreparedPcsRecursionBackend, RecursionInput, VerificationError, VerifierCircuitResult,
    build_next_layer_circuit, replay_batch_stark_transcript, verify_batch_circuit,
};

// ---------------------------------------------------------------------------------------------
// Toy AIRs: `Squares` (8 rows, preprocessed) sends `(x, y)` on a global bus, `Lookup` (16 rows)
// receives each of them once.
// ---------------------------------------------------------------------------------------------

const SQUARES_ROWS: usize = 8;
const LOOKUP_ROWS: usize = 16;
const BUS: &str = "d3-squares";
const X0: u64 = 5;

#[derive(Clone, Copy)]
enum ToyAir {
    /// Main `(x, y)`, preprocessed `k_i = 3i + 1`, public value `x_0`. Constraints:
    /// `x_0 = pv[0]`, `x' = x + 1`, `y = x^2 + k`. Sends `(x, y)` on every row.
    Squares,
    /// Main `(x, y, s)` with `s` boolean. Receives `(x, y)` with multiplicity `s`.
    Lookup,
}

impl<Fl: p3_field::Field> BaseAir<Fl> for ToyAir {
    fn width(&self) -> usize {
        match self {
            Self::Squares => 2,
            Self::Lookup => 3,
        }
    }

    fn num_public_values(&self) -> usize {
        match self {
            Self::Squares => 1,
            Self::Lookup => 0,
        }
    }

    fn preprocessed_width(&self) -> usize {
        match self {
            Self::Squares => 1,
            Self::Lookup => 0,
        }
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<Fl>> {
        match self {
            Self::Squares => Some(RowMajorMatrix::new_col(
                (0..SQUARES_ROWS)
                    .map(|i| Fl::from_usize(3 * i + 1))
                    .collect(),
            )),
            Self::Lookup => None,
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
                builder.push_interaction(BUS, [x.into(), y.into()], -1);
            }
            Self::Lookup => {
                let x = main.current(0).unwrap();
                let y = main.current(1).unwrap();
                let s = main.current(2).unwrap();
                builder.assert_bool(s);
                builder.push_interaction(BUS, [x.into(), y.into()], Count::bounded(s.into(), 1));
            }
        }
    }
}

fn squares_row(i: usize) -> (F, F) {
    let x = F::from_u64(X0 + i as u64);
    (x, x * x + F::from_usize(3 * i + 1))
}

/// The toy traces. With `unbalanced`, the first `Lookup` row has `s = 0`: every constraint
/// still holds, but one `Squares` message is never received, so the bus does not balance.
fn toy_traces(unbalanced: bool) -> [RowMajorMatrix<F>; 2] {
    let squares = (0..SQUARES_ROWS)
        .flat_map(|i| {
            let (x, y) = squares_row(i);
            [x, y]
        })
        .collect();
    // Every `Squares` row once (in reverse order), then unused rows with `s = 0`.
    let lookup = (0..LOOKUP_ROWS)
        .flat_map(|i| {
            if i < SQUARES_ROWS {
                let (x, y) = squares_row(SQUARES_ROWS - 1 - i);
                [x, y, F::from_bool(!(unbalanced && i == 0))]
            } else {
                [F::from_usize(i), F::from_usize(7 * i + 2), F::ZERO]
            }
        })
        .collect();
    [
        RowMajorMatrix::new(squares, 2),
        RowMajorMatrix::new(lookup, 3),
    ]
}

struct ToyProof {
    config: D3RecursionConfig,
    airs: [ToyAir; 2],
    public_values: Vec<Vec<F>>,
    prover_data: ProverData<D3RecursionConfig>,
    proof: BatchProof<D3RecursionConfig>,
}

impl ToyProof {
    /// The honest toy proof; the native verifier accepts it.
    fn new() -> Self {
        let toy = Self::prove(false);
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

    fn prove(unbalanced: bool) -> Self {
        let config = D3RecursionConfig::new(D3FriParams::test_params());
        let airs = [ToyAir::Squares, ToyAir::Lookup];
        let traces = toy_traces(unbalanced);
        let public_values = vec![vec![F::from_u64(X0)], vec![]];
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
        assert_eq!(proof.degree_bits, vec![3, 4]);
        assert!(proof.lookup_terminals.iter().all(Option::is_some));
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
}

/// The verification circuit of a toy proof, built with `verify_batch_circuit`.
struct VerifierCircuit {
    circuit: Circuit<EF>,
    mmcs_op_ids: Vec<NonPrimitiveOpId>,
    public_inputs: Vec<EF>,
    private_inputs: Vec<EF>,
}

/// Build the verifier circuit for `toy` and pack the circuit inputs from `proof` (the toy's own
/// proof, or a tampered copy of it).
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
            &[1, 0],
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
    fn run(
        &self,
        query_paths: &[FriQueryPaths<F, DIGEST>],
    ) -> Result<p3_circuit::tables::Traces<EF>, CircuitError> {
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

fn describe_layer(proof: &BatchStarkProof<D3RecursionConfig>) {
    eprintln!(
        "D3 layer proof: primitive rows {:?}, degree bits {:?}",
        proof.rows, proof.proof.degree_bits
    );
    for entry in &proof.non_primitives {
        eprintln!(
            "  non-primitive table {:?}: {} rows",
            entry.op_type, entry.rows
        );
    }
}

#[test]
fn native_d3_batch_proof_verifies_in_circuit_and_proves_at_d3() {
    let toy = ToyProof::new();
    let verifier = verifier_circuit(&toy, &toy.proof);
    let query_paths = toy
        .config
        .query_paths(&toy.proof.opening_proof, toy.transcript(&toy.proof));
    let traces = verifier
        .run(&query_paths)
        .expect("the honest proof's verifier circuit runs");
    for config in [PERM.for_challenger(), PERM] {
        let operations = traces
            .non_primitive_trace::<Poseidon2Trace<F>>(&NpoTypeId::poseidon2_perm(config))
            .map_or(0, |trace| trace.operations.len());
        eprintln!("{} permutations: {operations}", config.variant_name());
    }
    let layer = prove_layer(&toy.config, &verifier.circuit, &traces);
    describe_layer(&layer);
}

/// A changed opened value changes the Fiat-Shamir transcript the circuit replays, so its query
/// indices and proof-of-work check move with it. The circuit fails at execution: on the query
/// PoW check for most changes, and on the Merkle checks of the moved query indices when the
/// changed transcript happens to pass the PoW. Both cases are exercised for each AIR.
#[test]
fn changed_opened_value_fails_execution() {
    let toy = ToyProof::new();
    let honest_paths = toy
        .config
        .query_paths(&toy.proof.opening_proof, toy.transcript(&toy.proof));
    for instance in 0..2 {
        let mut pow_rejected = false;
        let mut pow_passed = false;
        for delta in 1..=64u64 {
            let mut proof = ToyProof::new().proof;
            proof.opened_values.instances[instance]
                .base_opened_values
                .trace_local[1] += EF::from_u64(delta);
            // Natively, the changed transcript either fails the query PoW or samples other
            // indices, which the proof's Merkle openings do not authenticate.
            let native = toy
                .config
                .try_query_paths(&proof.opening_proof, toy.transcript(&proof));
            let native_pow_failed = matches!(&native, Err(e) if e.contains("InvalidPowWitness"));
            assert!(
                native.is_err(),
                "AIR {instance}, +{delta}: native restoration fails"
            );
            if (native_pow_failed && pow_rejected) || (!native_pow_failed && pow_passed) {
                continue;
            }
            let result = verifier_circuit(&toy, &proof).run(&honest_paths);
            let error = result.expect_err("a changed opened value must fail execution");
            eprintln!(
                "changed opened value (AIR {instance}, +{delta}, native PoW {}): {error}",
                if native_pow_failed { "fails" } else { "passes" }
            );
            pow_rejected |= native_pow_failed;
            pow_passed |= !native_pow_failed;
            if pow_rejected && pow_passed {
                break;
            }
        }
        assert!(
            pow_rejected && pow_passed,
            "AIR {instance}: both rejection paths are exercised"
        );
    }
}

/// The bus does not balance (one message is sent but never received), while every AIR
/// constraint holds. The native verifier rejects the nonzero sum of lookup terminals; so must
/// the circuit.
#[test]
#[cfg_attr(
    debug_assertions,
    ignore = "debug provers check the lookups and panic before a proof exists"
)]
fn unbalanced_global_lookup_fails_execution() {
    let toy = ToyProof::prove(true);
    assert!(
        verify_batch(
            &toy.config,
            &toy.airs,
            &toy.proof,
            &toy.public_values,
            toy.common()
        )
        .is_err(),
        "the native verifier rejects the unbalanced bus"
    );
    let query_paths = toy
        .config
        .query_paths(&toy.proof.opening_proof, toy.transcript(&toy.proof));
    let result = verifier_circuit(&toy, &toy.proof).run(&query_paths);
    let error = result.expect_err("an unbalanced bus must fail execution");
    eprintln!("unbalanced global lookup: {error}");
}

#[test]
fn changed_merkle_sibling_fails_execution() {
    let toy = ToyProof::new();
    let verifier = verifier_circuit(&toy, &toy.proof);
    let honest = toy
        .config
        .query_paths(&toy.proof.opening_proof, toy.transcript(&toy.proof));
    // A sibling of an input (trace) opening and of a commit-phase opening.
    for (input, place) in [(true, "input batch"), (false, "commit phase")] {
        let mut paths = honest.clone();
        let chain = if input {
            &mut paths[0].input[0]
        } else {
            &mut paths[0].commit_phase[0]
        };
        chain[0][0] += F::ONE;
        let result = verifier.run(&paths);
        assert!(
            result.is_err(),
            "a changed {place} Merkle sibling must fail execution"
        );
        eprintln!("changed {place} sibling: {}", result.err().unwrap());
    }
}

#[test]
fn bad_query_pow_witness_fails_execution() {
    let toy = ToyProof::new();
    let query_paths = toy
        .config
        .query_paths(&toy.proof.opening_proof, toy.transcript(&toy.proof));
    // The next field element as the witness; the native verifier confirms it fails the grind.
    let mut proof = ToyProof::new().proof;
    let honest = proof.opening_proof.query_pow_witness;
    proof.opening_proof.query_pow_witness = honest + F::ONE;
    let verifier = verifier_circuit(&toy, &proof);
    assert!(
        verify_batch(
            &toy.config,
            &toy.airs,
            &proof,
            &toy.public_values,
            toy.common()
        )
        .is_err(),
        "the native verifier rejects the changed witness"
    );
    let result = verifier.run(&query_paths);
    assert!(
        result.is_err(),
        "a bad query PoW witness must fail execution"
    );
    eprintln!("bad query PoW witness: {}", result.err().unwrap());
}

#[test]
fn d3_backend_builds_and_runs_the_layer_verifier() {
    let toy = ToyProof::new();
    let verifier = verifier_circuit(&toy, &toy.proof);
    let query_paths = toy
        .config
        .query_paths(&toy.proof.opening_proof, toy.transcript(&toy.proof));
    let traces = verifier.run(&query_paths).unwrap();
    let layer = prove_layer(&toy.config, &verifier.circuit, &traces);

    let backend = backend();
    // As `RecursionOutput::into_recursion_input`.
    let prev = layer_input(&layer);
    let contract =
        PreparedPcsRecursionBackend::<D3RecursionConfig, BatchOnly, D>::capture_input_contract(
            &backend,
            &toy.config,
            &prev,
        )
        .expect("the D3 backend captures the layer proof's input contract");
    let RecursionInput::BatchStark {
        table_public_inputs,
        ..
    } = &prev
    else {
        unreachable!()
    };
    PreparedPcsRecursionBackend::<D3RecursionConfig, BatchOnly, D>::validate_prepared_input(
        &backend,
        &toy.config,
        &contract,
        &PreparedInput::BatchStark {
            proof: &layer,
            common_data: &layer.stark_common,
            table_public_inputs,
        },
    )
    .expect("the layer proof matches its own contract");

    let (circuit, result) = build_next_layer_circuit::<_, _, _, D>(&prev, &toy.config, &backend)
        .expect("the D3 backend builds the layer verifier circuit");
    let mut runner = circuit.runner();
    runner
        .set_public_inputs(&result.pack_public_inputs(&prev).unwrap())
        .unwrap();
    runner
        .set_private_inputs(&result.pack_private_inputs(&prev).unwrap())
        .unwrap();
    PcsRecursionBackend::<D3RecursionConfig, BatchOnly, D>::set_private_data_for_result(
        &backend,
        &toy.config,
        &mut runner,
        &result,
        &prev,
    )
    .expect("the D3 backend sets the layer proof's private data");
    let traces = runner
        .run()
        .expect("the layer verifier circuit runs on the honest layer proof");
    for config in [PERM.for_challenger(), PERM] {
        let operations = traces
            .non_primitive_trace::<Poseidon2Trace<F>>(&NpoTypeId::poseidon2_perm(config))
            .map_or(0, |trace| trace.operations.len());
        eprintln!(
            "layer verifier {} permutations: {operations}",
            config.variant_name()
        );
    }
}

/// The degree-3 backend proves its permutations with degree-3 Poseidon2 tables only, so it
/// refuses any other challenger config before building a circuit.
#[test]
fn d3_backend_rejects_a_challenger_of_another_degree() {
    let config = D3RecursionConfig::new(D3FriParams::test_params());
    let backend = FriRecursionBackend::<WIDTH, RATE, _>::new(Poseidon2Config::GOLDILOCKS_D2_W8)
        .for_extension_degree::<D>();
    let mut builder = CircuitBuilder::<EF>::new();
    let result = PcsRecursionBackend::<D3RecursionConfig, BatchOnly, D>::prepare_circuit(
        &backend,
        &config,
        &mut builder,
    );
    assert!(matches!(
        result,
        Err(VerificationError::InvalidProofShape(message)) if message.contains("degree-3 Poseidon2")
    ));
}
