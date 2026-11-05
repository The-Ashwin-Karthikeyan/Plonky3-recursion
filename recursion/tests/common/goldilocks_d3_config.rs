//! Goldilocks D3 / Poseidon2 width-12 FRI recursion config shared by the D3 recursion tests.
//!
//! The STARK config is lrup's native shape: Goldilocks with `CubicTrinomialExtensionField`
//! challenges, p3-goldilocks' reference width-12 permutation, `PaddingFreeSponge<_, 12, 6, 6>`
//! leaves, `TruncatedPermutation<_, 2, 6, 12>` nodes, cap height 0, a
//! `DuplexChallenger<_, _, 12, 6>`, `log_final_poly_len` 0, no commit or batch proof of work and
//! no lookup or out-of-domain grinding. The FRI blowup, query count, query proof of work and
//! maximum folding arity are the parameters ([`D3FriParams`]).
//!
//! [`D3RecursionConfig`] adds what the in-circuit verifier needs (modelled on
//! `common::KoalaBearD4RecursionConfig`). The same type serves for the native inner proofs and
//! for the recursion-layer proofs, each with its own parameters.

#![allow(dead_code)]

use std::sync::Arc;
use std::time::{Duration, Instant};

use p3_circuit::ops::{GoldilocksD3Width12, generate_poseidon2_trace, generate_recompose_trace};
use p3_circuit::{Circuit, CircuitBuilder, CircuitRunner, NonPrimitiveOpId};
use p3_circuit_prover::config::{GoldilocksD3W12Config, GoldilocksD3W12ValMmcs};
use p3_circuit_prover::{
    BatchStarkProof, BatchStarkProver, CircuitVerifier, ConstraintProfile, TablePacking,
};
use p3_commit::{ExtensionMmcs, Pcs};
use p3_dft::Radix2DitParallel;
use p3_field::extension::CubicTrinomialExtensionField;
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_goldilocks::{Goldilocks, Poseidon2Goldilocks, default_goldilocks_poseidon2_12};
use p3_lookup::logup::LogUpGadget;
use p3_recursion::pcs::{
    FriProofTargets, FriQueryPaths, InputProofTargets, MerkleCapTargets, RecExtensionValMmcs,
    RecValMmcs, Witness, restore_fri_query_paths, set_fri_mmcs_private_data,
};
use p3_recursion::traits::RecursivePcs;
use p3_recursion::{
    BatchOnly, FriRecursionBackend, FriRecursionBackendForExt, FriRecursionConfig,
    FriVerifierParams, NativeFriParams, OpeningTranscript, PcsRecursionBackend, Poseidon2Config,
    RecursionInput, RecursiveAir, VerificationError, observe_opened_values,
};
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{StarkGenericConfig, Val};

pub type F = Goldilocks;
pub type EF = CubicTrinomialExtensionField<F>;
pub type Perm = Poseidon2Goldilocks<WIDTH>;
pub type Hash = PaddingFreeSponge<Perm, WIDTH, RATE, DIGEST>;
pub type Compress = TruncatedPermutation<Perm, 2, DIGEST, WIDTH>;
pub type ValMmcs = GoldilocksD3W12ValMmcs;
pub type ChallengeMmcs = ExtensionMmcs<F, EF, ValMmcs>;
pub type NativePcs = TwoAdicFriPcs<F, Radix2DitParallel<F>, ValMmcs, ChallengeMmcs>;
pub type Challenger = <GoldilocksD3W12Config as StarkGenericConfig>::Challenger;

pub type Commitment = MerkleCapTargets<F, DIGEST>;
pub type InputProof = InputProofTargets<F, EF, RecValMmcs<F, DIGEST, Hash, Compress>>;
pub type OpeningProof = FriProofTargets<
    F,
    EF,
    RecExtensionValMmcs<F, EF, DIGEST, RecValMmcs<F, DIGEST, Hash, Compress>>,
    InputProof,
    Witness<F>,
>;

/// The D3 recursion backend.
pub type Backend = FriRecursionBackendForExt<3, WIDTH, RATE, Poseidon2Config>;

pub const D: usize = 3;
pub const WIDTH: usize = 12;
pub const RATE: usize = 6;
pub const DIGEST: usize = 6;
pub const PERM: Poseidon2Config = Poseidon2Config::GOLDILOCKS_D3_W12;

/// The FRI parameters that vary between configs. Everything else is fixed to lrup's shape.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct D3FriParams {
    pub log_blowup: usize,
    pub num_queries: usize,
    pub query_pow_bits: usize,
    pub max_log_arity: usize,
}

impl D3FriParams {
    /// lrup's inner config exactly (`lrup-backend-p3/src/config.rs`, `make_config`): rate 1/2,
    /// 256 queries and 22 bits of query grinding (~128 proven bits under unique decoding), folding
    /// arity up to 8.
    pub const fn lrup_inner_params() -> Self {
        Self {
            log_blowup: 1,
            num_queries: 256,
            query_pow_bits: 22,
            max_log_arity: 3,
        }
    }

    /// A recursion-layer config at the same 128-bit target (plan "Soundness budget"): rate 1/4,
    /// 157 queries and 22 bits of query grinding.
    pub const fn recursion_layer_params() -> Self {
        Self {
            log_blowup: 2,
            num_queries: 157,
            query_pow_bits: 22,
            max_log_arity: 3,
        }
    }

    /// Cheap parameters in lrup's shape (folding arity up to 8, a nonzero query proof of work)
    /// for fast tests. Not sound.
    pub const fn test_params() -> Self {
        Self {
            log_blowup: 1,
            num_queries: 8,
            query_pow_bits: 4,
            max_log_arity: 3,
        }
    }
}

#[derive(Clone)]
pub struct D3RecursionConfig {
    config: Arc<GoldilocksD3W12Config>,
    params: D3FriParams,
    fri_verifier_params: FriVerifierParams,
    native_fri_params: NativeFriParams,
    /// The base-field MMCS and FRI parameters `config` commits with, needed to restore a FRI
    /// proof's per-query Merkle paths.
    val_mmcs: ValMmcs,
    fri_params: FriParameters<ChallengeMmcs>,
}

impl D3RecursionConfig {
    pub fn new(params: D3FriParams) -> Self {
        let perm = default_goldilocks_poseidon2_12();
        let val_mmcs = ValMmcs::new(Hash::new(perm.clone()), Compress::new(perm.clone()), 0);
        let fri_params = FriParameters {
            log_blowup: params.log_blowup,
            log_final_poly_len: 0,
            max_log_arity: params.max_log_arity,
            num_queries: params.num_queries,
            batch_proof_of_work_bits: 0,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: params.query_pow_bits,
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
        let config = GoldilocksD3W12Config::new(pcs, Challenger::new(perm))
            .with_lookup_proof_of_work_bits(0)
            .with_ood_proof_of_work_bits(0);
        Self {
            config: Arc::new(config),
            params,
            fri_verifier_params,
            native_fri_params,
            val_mmcs,
            fri_params,
        }
    }

    pub const fn params(&self) -> D3FriParams {
        self.params
    }

    pub const fn fri_params(&self) -> &FriParameters<ChallengeMmcs> {
        &self.fri_params
    }

    /// The per-query Merkle paths of a FRI proof, restored from its replayed transcript.
    pub fn query_paths(
        &self,
        opening_proof: &<NativePcs as Pcs<EF, Challenger>>::Proof,
        transcript: OpeningTranscript<Self>,
    ) -> Vec<FriQueryPaths<F, DIGEST>> {
        self.try_query_paths(opening_proof, transcript)
            .expect("the honest FRI proof's query paths restore")
    }

    /// [`Self::query_paths`], or the native error: the restoration checks the query proof of
    /// work and the commit-phase folding on the way.
    pub fn try_query_paths(
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
    fn lookup_proof_of_work_bits(&self) -> usize {
        self.config.lookup_proof_of_work_bits()
    }
    fn ood_proof_of_work_bits(&self) -> usize {
        self.config.ood_proof_of_work_bits()
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
        let query_paths = config
            .try_query_paths(opening_proof, transcript)
            .map_err(|_| "the FRI proof's per-query Merkle paths do not restore")?;
        set_fri_mmcs_private_data::<F, EF, DIGEST>(runner, op_ids, &query_paths, PERM)
    }
}

/// The D3 backend for `GOLDILOCKS_D3_W12`.
pub fn backend() -> Backend {
    FriRecursionBackend::<WIDTH, RATE, _>::new(PERM).for_extension_degree::<D>()
}

/// A recursion-layer proof, with the verifier of its relation and the time each stage took.
pub struct ProvedLayer {
    pub proof: BatchStarkProof<D3RecursionConfig>,
    pub verifier: CircuitVerifier<D3RecursionConfig>,
    /// Preprocessing and committing the circuit relation.
    pub prepare: Duration,
    /// Proving the execution traces.
    pub prove: Duration,
    /// Native verification of the proof.
    pub verify: Duration,
}

/// Prove a D3 verifier circuit under `config` with the tables the D3 backend registers, and
/// verify the proof natively.
pub fn prove_layer_with_stats(
    config: &D3RecursionConfig,
    circuit: &Circuit<EF>,
    traces: &p3_circuit::tables::Traces<EF>,
) -> ProvedLayer {
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
    let start = Instant::now();
    let prepared = prover
        .prepare_circuit::<EF, D>(
            circuit,
            &preprocessors,
            &air_builders,
            ConstraintProfile::Standard,
        )
        .expect("the D3 verifier circuit prepares");
    let prepare = start.elapsed();
    let start = Instant::now();
    let proof = prepared
        .prove(traces)
        .expect("the D3 verifier circuit proves");
    let prove = start.elapsed();
    assert_eq!(proof.ext_degree, D);
    assert!(
        proof.alu_quintic_trinomial,
        "D3 uses the cubic trinomial ALU"
    );
    let verifier = prepared.verifier();
    let start = Instant::now();
    verifier
        .verify(&proof, &[])
        .expect("the D3 layer proof verifies natively");
    let verify = start.elapsed();
    ProvedLayer {
        proof,
        verifier,
        prepare,
        prove,
        verify,
    }
}

/// [`prove_layer_with_stats`], keeping only the proof.
pub fn prove_layer(
    config: &D3RecursionConfig,
    circuit: &Circuit<EF>,
    traces: &p3_circuit::tables::Traces<EF>,
) -> BatchStarkProof<D3RecursionConfig> {
    prove_layer_with_stats(config, circuit, traces).proof
}

/// The next-layer input for a layer proof, as `RecursionOutput::into_recursion_input` builds it:
/// no public values on the primitive tables, then each non-primitive table's attached vector.
pub fn layer_input(
    layer: &BatchStarkProof<D3RecursionConfig>,
) -> RecursionInput<'_, D3RecursionConfig, BatchOnly> {
    let num_primitive = layer.proof.opened_values.instances.len() - layer.non_primitives.len();
    let mut table_public_inputs = vec![vec![]; num_primitive];
    table_public_inputs.extend(
        layer
            .non_primitives
            .iter()
            .map(|entry| entry.public_values.clone()),
    );
    RecursionInput::BatchStark {
        proof: layer,
        common_data: &layer.stark_common,
        table_public_inputs,
    }
}
