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
//!   is not proved here.

use std::sync::Arc;

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_batch_stark::{
    BatchProof, CommonData, ProverData, StarkInstance, prove_batch, verify_batch,
};
use p3_circuit::ops::{
    GoldilocksD3Width12, NpoTypeId, Poseidon2Trace, generate_poseidon2_trace,
    generate_recompose_trace,
};
use p3_circuit::{Circuit, CircuitBuilder, CircuitError, CircuitRunner, NonPrimitiveOpId};
use p3_circuit_prover::config::{GoldilocksD3W12Config, GoldilocksD3W12ValMmcs};
use p3_circuit_prover::{BatchStarkProof, BatchStarkProver, ConstraintProfile, TablePacking};
use p3_commit::{ExtensionMmcs, Pcs};
use p3_dft::Radix2DitParallel;
use p3_field::PrimeCharacteristicRing;
use p3_field::extension::CubicTrinomialExtensionField;
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_goldilocks::{Goldilocks, Poseidon2Goldilocks, default_goldilocks_poseidon2_12};
use p3_lookup::logup::LogUpGadget;
use p3_lookup::{Count, InteractionBuilder};
use p3_matrix::dense::RowMajorMatrix;
use p3_recursion::pcs::{
    FriProofTargets, FriQueryPaths, InputProofTargets, MerkleCapTargets, RecExtensionValMmcs,
    RecValMmcs, Witness, restore_fri_query_paths, set_fri_mmcs_private_data,
};
use p3_recursion::traits::RecursivePcs;
use p3_recursion::{
    BatchOnly, BatchStarkVerifierInputsBuilder, FriRecursionBackend, FriRecursionBackendForExt,
    FriRecursionConfig, FriVerifierParams, NativeFriParams, OpeningTranscript, PcsRecursionBackend,
    Poseidon2Config, PreparedInput, PreparedPcsRecursionBackend, RecursionInput, RecursiveAir,
    VerificationError, VerifierCircuitResult, build_next_layer_circuit, observe_opened_values,
    replay_batch_stark_transcript, verify_batch_circuit,
};
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{StarkGenericConfig, Val};

type F = Goldilocks;
type EF = CubicTrinomialExtensionField<F>;
type Perm = Poseidon2Goldilocks<WIDTH>;
type Hash = PaddingFreeSponge<Perm, WIDTH, RATE, DIGEST>;
type Compress = TruncatedPermutation<Perm, 2, DIGEST, WIDTH>;
type ValMmcs = GoldilocksD3W12ValMmcs;
type ChallengeMmcs = ExtensionMmcs<F, EF, ValMmcs>;
type NativePcs = TwoAdicFriPcs<F, Radix2DitParallel<F>, ValMmcs, ChallengeMmcs>;
type Challenger = <GoldilocksD3W12Config as StarkGenericConfig>::Challenger;

type Commitment = MerkleCapTargets<F, DIGEST>;
type InputProof = InputProofTargets<F, EF, RecValMmcs<F, DIGEST, Hash, Compress>>;
type OpeningProof = FriProofTargets<
    F,
    EF,
    RecExtensionValMmcs<F, EF, DIGEST, RecValMmcs<F, DIGEST, Hash, Compress>>,
    InputProof,
    Witness<F>,
>;

/// The D3 recursion backend under test.
type Backend = FriRecursionBackendForExt<3, WIDTH, RATE, Poseidon2Config>;

const D: usize = 3;
const WIDTH: usize = 12;
const RATE: usize = 6;
const DIGEST: usize = 6;
const PERM: Poseidon2Config = Poseidon2Config::GOLDILOCKS_D3_W12;

/// Small FRI parameters in lrup's shape.
const LOG_BLOWUP: usize = 1;
const MAX_LOG_ARITY: usize = 3;
const NUM_QUERIES: usize = 8;
const QUERY_POW_BITS: usize = 4;

// ---------------------------------------------------------------------------------------------
// The recursion FRI config: `GoldilocksD3W12Config` with lrup-shaped test FRI parameters, plus
// what the in-circuit verifier needs (modelled on `common::KoalaBearD4RecursionConfig`).
// ---------------------------------------------------------------------------------------------

#[derive(Clone)]
struct D3RecursionConfig {
    config: Arc<GoldilocksD3W12Config>,
    fri_verifier_params: FriVerifierParams,
    native_fri_params: NativeFriParams,
    val_mmcs: ValMmcs,
    fri_params: FriParameters<ChallengeMmcs>,
}

impl D3RecursionConfig {
    fn new() -> Self {
        let perm = default_goldilocks_poseidon2_12();
        let val_mmcs = ValMmcs::new(Hash::new(perm.clone()), Compress::new(perm.clone()), 0);
        let fri_params = FriParameters {
            log_blowup: LOG_BLOWUP,
            log_final_poly_len: 0,
            max_log_arity: MAX_LOG_ARITY,
            num_queries: NUM_QUERIES,
            batch_proof_of_work_bits: 0,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: QUERY_POW_BITS,
            mmcs: ChallengeMmcs::new(val_mmcs.clone()),
        };
        let native_fri_params = NativeFriParams::try_from_native::<F, _>(&fri_params).unwrap();
        let fri_verifier_params = FriVerifierParams::with_mmcs(
            native_fri_params.log_blowup(),
            native_fri_params.log_final_poly_len(),
            native_fri_params.max_log_arity(),
            native_fri_params.commit_pow_bits(),
            native_fri_params.query_pow_bits(),
            native_fri_params.num_queries(),
            PERM,
        );
        let pcs = NativePcs::new(
            Radix2DitParallel::default(),
            val_mmcs.clone(),
            fri_params.clone(),
        );
        Self {
            config: Arc::new(GoldilocksD3W12Config::new(pcs, Challenger::new(perm))),
            fri_verifier_params,
            native_fri_params,
            val_mmcs,
            fri_params,
        }
    }

    /// The per-query Merkle paths of a FRI proof, restored from its replayed transcript.
    fn query_paths(
        &self,
        opening_proof: &<NativePcs as Pcs<EF, Challenger>>::Proof,
        transcript: OpeningTranscript<Self>,
    ) -> Vec<FriQueryPaths<F, DIGEST>> {
        self.try_query_paths(opening_proof, transcript)
            .expect("the honest FRI proof's query paths restore")
    }

    /// [`Self::query_paths`], or the native error: the restoration checks the query proof of
    /// work and the commit-phase folding on the way.
    fn try_query_paths(
        &self,
        opening_proof: &<NativePcs as Pcs<EF, Challenger>>::Proof,
        transcript: OpeningTranscript<Self>,
    ) -> Result<Vec<FriQueryPaths<F, DIGEST>>, String> {
        let OpeningTranscript {
            mut challenger,
            commitments_with_opening_points,
        } = transcript;
        observe_opened_values::<Self>(
            &mut challenger,
            &commitments_with_opening_points,
            self.fri_params.batch_proof_of_work_bits,
        );
        let claims: Vec<_> = commitments_with_opening_points
            .into_iter()
            .map(Into::into)
            .collect();
        restore_fri_query_paths(
            &self.fri_params,
            &self.val_mmcs,
            &self.val_mmcs,
            opening_proof,
            &mut challenger,
            &claims,
        )
        .map_err(|error| format!("{error:?}"))
    }
}

impl StarkGenericConfig for D3RecursionConfig {
    type Challenge = EF;
    type Challenger = Challenger;
    type Pcs = NativePcs;
    fn pcs(&self) -> &NativePcs {
        self.config.pcs()
    }
    fn initialise_challenger(&self) -> Challenger {
        self.config.initialise_challenger()
    }
}

impl FriRecursionConfig for D3RecursionConfig
where
    NativePcs: RecursivePcs<
            Self,
            InputProof,
            OpeningProof,
            Commitment,
            <NativePcs as Pcs<EF, Challenger>>::Domain,
        >,
{
    type Commitment = Commitment;
    type InputProof = InputProof;
    type OpeningProof = OpeningProof;
    type RawOpeningProof = <NativePcs as Pcs<EF, Challenger>>::Proof;
    const DIGEST_ELEMS: usize = DIGEST;

    fn native_fri_validation_params(&self) -> Option<NativeFriParams> {
        Some(self.native_fri_params)
    }

    fn with_fri_opening_proof<'a, A, R>(
        prev: &RecursionInput<'a, Self, A>,
        f: impl FnOnce(&Self::RawOpeningProof) -> R,
    ) -> R
    where
        A: RecursiveAir<Val<Self>, Self::Challenge, LogUpGadget>,
    {
        match prev {
            RecursionInput::UniStark { proof, .. } => f(&proof.opening_proof),
            RecursionInput::BatchStark { proof, .. } => f(&proof.proof.opening_proof),
        }
    }

    fn prepare_circuit_for_verification(
        &self,
        circuit: &mut CircuitBuilder<EF>,
    ) -> Result<(), VerificationError> {
        circuit.enable_poseidon2_perm_width_12::<GoldilocksD3Width12, _>(
            generate_poseidon2_trace::<EF, GoldilocksD3Width12>,
            default_goldilocks_poseidon2_12(),
        );
        circuit.enable_recompose::<F>(generate_recompose_trace::<F, EF>);
        Ok(())
    }

    fn pcs_verifier_params(&self) -> &FriVerifierParams {
        &self.fri_verifier_params
    }

    fn set_fri_private_data(
        config: &Self,
        runner: &mut CircuitRunner<'_, EF>,
        op_ids: &[NonPrimitiveOpId],
        opening_proof: &Self::RawOpeningProof,
        transcript: OpeningTranscript<Self>,
    ) -> Result<(), &'static str> {
        let query_paths = config.query_paths(opening_proof, transcript);
        set_fri_mmcs_private_data::<F, EF, DIGEST>(runner, op_ids, &query_paths, PERM)
    }
}

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
        let config = D3RecursionConfig::new();
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

/// The D3 backend for `GOLDILOCKS_D3_W12`.
fn backend() -> Backend {
    FriRecursionBackend::<WIDTH, RATE, _>::new(PERM).for_extension_degree::<D>()
}

/// Prove a D3 verifier circuit with the tables the D3 backend registers, and verify the proof.
fn prove_layer(
    config: &D3RecursionConfig,
    circuit: &Circuit<EF>,
    traces: &p3_circuit::tables::Traces<EF>,
) -> BatchStarkProof<D3RecursionConfig> {
    let backend = backend();
    let preprocessors =
        PcsRecursionBackend::<D3RecursionConfig, BatchOnly, D>::non_primitive_preprocessors(
            &backend,
        );
    let air_builders =
        PcsRecursionBackend::<D3RecursionConfig, BatchOnly, D>::non_primitive_air_builders(
            &backend,
        );
    let mut prover =
        BatchStarkProver::new(config.clone()).with_table_packing(TablePacking::new(2, 4));
    for table in
        PcsRecursionBackend::<D3RecursionConfig, BatchOnly, D>::non_primitive_provers(&backend, D)
    {
        prover.register_table_prover(table);
    }
    let prepared = prover
        .prepare_circuit::<EF, D>(
            circuit,
            &preprocessors,
            &air_builders,
            ConstraintProfile::Standard,
        )
        .expect("the D3 verifier circuit prepares");
    let proof = prepared
        .prove(traces)
        .expect("the D3 verifier circuit proves");
    assert_eq!(proof.ext_degree, D);
    assert!(
        proof.alu_quintic_trinomial,
        "D3 uses the cubic trinomial ALU"
    );
    prepared
        .verifier()
        .verify(&proof, &[])
        .expect("the D3 layer proof verifies natively");
    proof
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
    // As `RecursionOutput::into_recursion_input`: no public values on the primitive tables, then
    // each non-primitive table's attached vector.
    let num_primitive = layer.proof.opened_values.instances.len() - layer.non_primitives.len();
    let mut table_public_inputs = vec![vec![]; num_primitive];
    table_public_inputs.extend(
        layer
            .non_primitives
            .iter()
            .map(|entry| entry.public_values.clone()),
    );
    let prev: RecursionInput<'_, D3RecursionConfig, BatchOnly> = RecursionInput::BatchStark {
        proof: &layer,
        common_data: &layer.stark_common,
        table_public_inputs,
    };
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
    let config = D3RecursionConfig::new();
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
