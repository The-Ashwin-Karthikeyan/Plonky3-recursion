//! STARK proving configurations.
//!
//! This module provides STARK configurations for different prime fields.
//!
//! # Quick Start
//!
//! ```rust
//! use p3_circuit_prover::config;
//!
//! // Use a preconfigured setup
//! let config = config::baby_bear();
//! ```

use p3_baby_bear::{BabyBear, Poseidon2BabyBear, default_babybear_poseidon2_16};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::{BinomialExtensionField, CubicTrinomialExtensionField};
use p3_field::{Field, PrimeCharacteristicRing, PrimeField64, TwoAdicField};
use p3_fri::{FriParameters, HidingFriPcs, TwoAdicFriPcs};
use p3_goldilocks::{Goldilocks, Poseidon2Goldilocks, default_goldilocks_poseidon2_12};
use p3_koala_bear::{KoalaBear, Poseidon2KoalaBear, default_koalabear_poseidon2_16};
use p3_merkle_tree::{MerkleTreeHidingMmcs, MerkleTreeMmcs};
use p3_symmetric::{CryptographicPermutation, PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::StarkConfig;

/// Compression function arity (number of inputs per compression).
const COMPRESS_ARITY: usize = 2;

/// A STARK configuration with all cryptographic primitives specified.
///
/// ### Type Parameters
/// - `F`: Base field.
/// - `PermHash`: Permutation function used for sponge hashing (leaves, transcript absorption).
/// - `PermCompress`: Permutation function used for Merkle tree compression.
/// - `HASH_PERM_WIDTH`: Width of the hash permutation state.
/// - `COMPRESS_PERM_WIDTH`: Width of the compression permutation state.
/// - `RATE`: Number of field elements absorbed per permutation in sponge mode.
/// - `OUT`: Number of output elements squeezed per permutation.
/// - `COMPRESS_CHUNK`: Number of elements per compression chunk in Merkle commitments.
/// - `CHALLENGE_DEGREE`: Extension field degree.
pub type Config<
    F,
    PermHash,
    PermCompress,
    const HASH_PERM_WIDTH: usize,
    const COMPRESS_PERM_WIDTH: usize,
    const RATE: usize,
    const OUT: usize,
    const COMPRESS_CHUNK: usize,
    const CHALLENGE_DEGREE: usize,
> = StarkConfig<
    TwoAdicFriPcs<
        F,
        Radix2DitParallel<F>,
        MerkleTreeMmcs<
            F,
            F,
            PaddingFreeSponge<PermHash, HASH_PERM_WIDTH, RATE, OUT>,
            TruncatedPermutation<PermCompress, COMPRESS_ARITY, COMPRESS_CHUNK, COMPRESS_PERM_WIDTH>,
            2,
            COMPRESS_CHUNK,
        >,
        ExtensionMmcs<
            F,
            BinomialExtensionField<F, CHALLENGE_DEGREE>,
            MerkleTreeMmcs<
                F,
                F,
                PaddingFreeSponge<PermHash, HASH_PERM_WIDTH, RATE, OUT>,
                TruncatedPermutation<
                    PermCompress,
                    COMPRESS_ARITY,
                    COMPRESS_CHUNK,
                    COMPRESS_PERM_WIDTH,
                >,
                2,
                COMPRESS_CHUNK,
            >,
        >,
    >,
    BinomialExtensionField<F, CHALLENGE_DEGREE>,
    DuplexChallenger<F, PermHash, HASH_PERM_WIDTH, RATE>,
>;

/// Builds a STARK configuration directly from the hash and compression permutations.
///
/// This replaces the former `ConfigBuilder` (which was only ever used internally,
/// immediately followed by `.build()`): the field factories below call this and
/// return the concrete config, so callers no longer chain `.build()`.
#[allow(clippy::type_complexity)]
fn build_poseidon2_stark_config<
    F,
    PermHash,
    PermCompress,
    const HASH_PERM_WIDTH: usize,
    const COMPRESS_PERM_WIDTH: usize,
    const RATE: usize,
    const OUT: usize,
    const COMPRESS_CHUNK: usize,
    const CHALLENGE_DEGREE: usize,
>(
    perm_hash: PermHash,
    perm_compress: PermCompress,
) -> Config<
    F,
    PermHash,
    PermCompress,
    HASH_PERM_WIDTH,
    COMPRESS_PERM_WIDTH,
    RATE,
    OUT,
    COMPRESS_CHUNK,
    CHALLENGE_DEGREE,
>
where
    F: Field,
    PermHash: Clone + CryptographicPermutation<[F; HASH_PERM_WIDTH]>,
    PermCompress: Clone + CryptographicPermutation<[F; COMPRESS_PERM_WIDTH]>,
{
    type Hash<Perm, const PERM_WIDTH: usize, const RATE: usize, const OUT: usize> =
        PaddingFreeSponge<Perm, PERM_WIDTH, RATE, OUT>;
    type Compress<Perm, const PERM_WIDTH: usize, const COMPRESS_CHUNK: usize> =
        TruncatedPermutation<Perm, COMPRESS_ARITY, COMPRESS_CHUNK, PERM_WIDTH>;

    let hash = Hash::<PermHash, HASH_PERM_WIDTH, RATE, OUT>::new(perm_hash.clone());
    let compress =
        Compress::<PermCompress, COMPRESS_PERM_WIDTH, COMPRESS_CHUNK>::new(perm_compress);
    let val_mmcs = MerkleTreeMmcs::new(hash, compress, 3);
    let challenge_mmcs = ExtensionMmcs::new(val_mmcs.clone());
    let dft = Radix2DitParallel::default();
    let fri_params = FriParameters::new_benchmark_high_arity(challenge_mmcs);
    let pcs = TwoAdicFriPcs::new(dft, val_mmcs, fri_params);
    let challenger = DuplexChallenger::new(perm_hash);

    StarkConfig::new(pcs, challenger)
}

/// Creates a standard BabyBear configuration.
///
/// BabyBear is a 31-bit prime field (2^31 - 2^27 + 1).
///
/// # Parameters
/// - **Hash permutation width**: 16 (appropriate for 32-bit fields)
/// - **Compression permutation width**: 16
/// - **Rate**: 8 (256 bits / 32 bits per element)
/// - **Output size**: 8 (256 bits / 32 bits per element)
/// - **Challenge degree**: 4
///
/// # Examples
///
/// ```rust
/// use p3_circuit_prover::{BatchStarkProver, config};
/// let config = config::baby_bear();
/// let prover = BatchStarkProver::new(config);
/// ```
#[inline]
pub fn baby_bear() -> BabyBearConfig {
    let perm = default_babybear_poseidon2_16();
    build_poseidon2_stark_config(perm.clone(), perm)
}

/// Creates a standard KoalaBear configuration.
///
/// KoalaBear is a 31-bit prime field (2^31 - 2^24 + 1).
///
/// # Parameters
/// - **Hash permutation width**: 16 (appropriate for 32-bit fields)
/// - **Compression permutation width**: 16
/// - **Rate**: 8 (256 bits / 32 bits per element)
/// - **Output size**: 8 (256 bits / 32 bits per element)
/// - **Challenge degree**: 4
///
/// # Examples
///
/// ```rust
/// use p3_circuit_prover::{BatchStarkProver, config};
/// let config = config::koala_bear();
/// let prover = BatchStarkProver::new(config);
/// ```
#[inline]
pub fn koala_bear() -> KoalaBearConfig {
    let perm = default_koalabear_poseidon2_16();
    build_poseidon2_stark_config(perm.clone(), perm)
}

/// Creates a standard Goldilocks configuration.
///
/// Goldilocks is a 64-bit prime field (2^64 - 2^32 + 1).
///
/// # Parameters
/// - **Hash permutation width**: 8 (appropriate for 64-bit fields)
/// - **Compression permutation width**: 8
/// - **Rate**: 4 (256 bits / 64 bits per element)
/// - **Output size**: 4 (256 bits / 64 bits per element)
/// - **Challenge degree**: 2
///
/// # Examples
///
/// ```rust
/// use p3_circuit_prover::{BatchStarkProver, config};
/// let config = config::goldilocks();
/// let prover = BatchStarkProver::new(config);
/// ```
#[inline]
pub fn goldilocks() -> GoldilocksConfig {
    use rand::SeedableRng;
    let mut rng = rand::rngs::Xoshiro256PlusPlus::seed_from_u64(1);
    let perm = p3_goldilocks::Poseidon2Goldilocks::<8>::new_from_rng_128(&mut rng);
    build_poseidon2_stark_config(perm.clone(), perm)
}

/// Creates a Goldilocks configuration with the cubic trinomial challenge field and
/// Poseidon2 width 12.
///
/// The hashing matches the `GOLDILOCKS_D3_W12` circuit permutation: p3-goldilocks' reference
/// permutation `default_goldilocks_poseidon2_12()`, a binary MMCS with cap height 0, and a
/// duplex challenger.
///
/// # Parameters
/// - **Hash permutation width**: 12
/// - **Compression permutation width**: 12
/// - **Rate**: 6
/// - **Output size**: 6 (a 6-element digest)
/// - **Challenge field**: `CubicTrinomialExtensionField<Goldilocks>` (`X^3 = X + 1`)
/// - **FRI**: the benchmark high-arity parameters of the other factories
///
/// # Examples
///
/// ```rust
/// use p3_circuit_prover::{BatchStarkProver, config};
/// let config = config::goldilocks_d3_w12();
/// let prover = BatchStarkProver::new(config);
/// ```
#[inline]
pub fn goldilocks_d3_w12() -> GoldilocksD3W12Config {
    let perm = default_goldilocks_poseidon2_12();
    let val_mmcs = GoldilocksD3W12ValMmcs::new(
        PaddingFreeSponge::new(perm.clone()),
        TruncatedPermutation::new(perm.clone()),
        0,
    );
    let challenge_mmcs = ExtensionMmcs::new(val_mmcs.clone());
    let fri_params = FriParameters::new_benchmark_high_arity(challenge_mmcs);
    let pcs = TwoAdicFriPcs::new(Radix2DitParallel::default(), val_mmcs, fri_params);
    StarkConfig::new(pcs, DuplexChallenger::new(perm))
}

/// Type alias for BabyBear STARK configuration.
pub type BabyBearConfig =
    Config<BabyBear, Poseidon2BabyBear<16>, Poseidon2BabyBear<16>, 16, 16, 8, 8, 8, 4>;

/// Type alias for KoalaBear STARK configuration.
pub type KoalaBearConfig =
    Config<KoalaBear, Poseidon2KoalaBear<16>, Poseidon2KoalaBear<16>, 16, 16, 8, 8, 8, 4>;

/// Type alias for Goldilocks STARK configuration.
pub type GoldilocksConfig =
    Config<Goldilocks, Poseidon2Goldilocks<8>, Poseidon2Goldilocks<8>, 8, 8, 4, 4, 4, 2>;

/// Binary Merkle MMCS of [`GoldilocksD3W12Config`]: `PaddingFreeSponge<_, 12, 6, 6>` leaves and
/// `TruncatedPermutation<_, 2, 6, 12>` nodes.
pub type GoldilocksD3W12ValMmcs = MerkleTreeMmcs<
    <Goldilocks as Field>::Packing,
    <Goldilocks as Field>::Packing,
    PaddingFreeSponge<Poseidon2Goldilocks<12>, 12, 6, 6>,
    TruncatedPermutation<Poseidon2Goldilocks<12>, COMPRESS_ARITY, 6, 12>,
    2,
    6,
>;

/// Type alias for the Goldilocks cubic-extension, Poseidon2 width-12 STARK configuration.
pub type GoldilocksD3W12Config = StarkConfig<
    TwoAdicFriPcs<
        Goldilocks,
        Radix2DitParallel<Goldilocks>,
        GoldilocksD3W12ValMmcs,
        ExtensionMmcs<Goldilocks, CubicTrinomialExtensionField<Goldilocks>, GoldilocksD3W12ValMmcs>,
    >,
    CubicTrinomialExtensionField<Goldilocks>,
    DuplexChallenger<Goldilocks, Poseidon2Goldilocks<12>, 12, 6>,
>;

// ---------------------------------------------------------------------------------------------
// Goldilocks D3 / W12: salted hiding configuration
// ---------------------------------------------------------------------------------------------

/// Salt elements appended to every Merkle leaf of [`GoldilocksD3W12ZkConfig`]: four Goldilocks
/// elements, 256 bits of salt per leaf.
pub const GOLDILOCKS_D3_W12_ZK_SALT_ELEMS: usize = 4;

/// Extension degree of [`GoldilocksD3W12ZkConfig`]'s challenge field.
const GOLDILOCKS_D3_W12_ZK_EXT_DEGREE: usize = 3;

/// The most points a batch-STARK proof opens one committed matrix at: `zeta` and its next-row
/// shift (main, permutation and preprocessed traces). Quotient chunks and the randomization
/// polynomial are opened at `zeta` only.
pub const BATCH_STARK_MAX_OPENING_POINTS: usize = 2;

/// Generator behind every salt and mask of [`GoldilocksD3W12ZkConfig`] (ChaCha12, a
/// [`rand::CryptoRng`]). Each of the three streams is seeded separately from the caller's OS
/// entropy source by [`goldilocks_d3_w12_zk`].
pub type GoldilocksD3W12ZkRng = rand::rngs::StdRng;

/// Salted binary Merkle MMCS of [`GoldilocksD3W12ZkConfig`]: the leaves and nodes of
/// [`GoldilocksD3W12ValMmcs`], with [`GOLDILOCKS_D3_W12_ZK_SALT_ELEMS`] random elements appended
/// to every leaf row before hashing.
pub type GoldilocksD3W12HidingMmcs = MerkleTreeHidingMmcs<
    <Goldilocks as Field>::Packing,
    <Goldilocks as Field>::Packing,
    PaddingFreeSponge<Poseidon2Goldilocks<12>, 12, 6, 6>,
    TruncatedPermutation<Poseidon2Goldilocks<12>, COMPRESS_ARITY, 6, 12>,
    GoldilocksD3W12ZkRng,
    2,
    6,
    GOLDILOCKS_D3_W12_ZK_SALT_ELEMS,
>;

/// Hiding FRI PCS of [`GoldilocksD3W12ZkConfig`]: random codewords and trace/quotient masks over
/// salted input and commit-phase MMCSs.
pub type GoldilocksD3W12ZkPcs = HidingFriPcs<
    Goldilocks,
    Radix2DitParallel<Goldilocks>,
    GoldilocksD3W12HidingMmcs,
    ExtensionMmcs<Goldilocks, CubicTrinomialExtensionField<Goldilocks>, GoldilocksD3W12HidingMmcs>,
    GoldilocksD3W12ZkRng,
>;

/// The salted hiding counterpart of [`GoldilocksD3W12Config`]: same field, challenge field,
/// permutation, sponge, compression, cap height and challenger.
pub type GoldilocksD3W12ZkConfig = StarkConfig<
    GoldilocksD3W12ZkPcs,
    CubicTrinomialExtensionField<Goldilocks>,
    DuplexChallenger<Goldilocks, Poseidon2Goldilocks<12>, 12, 6>,
>;

/// A [`GoldilocksD3W12ZkParams`] or an entropy source that [`goldilocks_d3_w12_zk`] refuses.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum GoldilocksD3W12ZkError {
    /// Fewer random codewords than the challenge field's degree: the extension-field FRI batch
    /// combination would not be uniformly masked.
    #[error("hiding FRI needs at least {required} random codewords, got {got}")]
    InsufficientRandomCodewords { required: usize, got: usize },
    /// A FRI parameter is out of range.
    #[error("invalid hiding FRI parameter: {0}")]
    InvalidFri(&'static str),
    /// The hiding budget does not fit in `usize`.
    #[error("hiding budget overflows")]
    BudgetOverflow,
    /// A table packing whose minimum trace height is below the hiding budget.
    #[error("minimum trace height {got} is below the hiding budget's {required} rows")]
    TableBelowHidingBudget { required: usize, got: usize },
    /// The entropy source failed to produce a seed.
    #[error("the OS entropy source failed: {0}")]
    Entropy(alloc::string::String),
}

/// FRI and hiding parameters of [`GoldilocksD3W12ZkConfig`]. Everything else is fixed to the shape
/// of [`goldilocks_d3_w12`]: `log_final_poly_len` 0, cap height 0, no commit or batch proof of
/// work, no lookup or out-of-domain grinding.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GoldilocksD3W12ZkParams {
    pub log_blowup: usize,
    pub num_queries: usize,
    pub query_pow_bits: usize,
    pub max_log_arity: usize,
    /// Random codewords appended to every private committed matrix (at least 3).
    pub num_random_codewords: usize,
}

impl GoldilocksD3W12ZkParams {
    /// The outer-wrap parameters: rate 1/8, 143 queries and 22 bits of query grinding, folding
    /// arity up to 8, three random codewords.
    ///
    /// Hiding does not change the FRI rate: the hiding PCS doubles every committed polynomial's
    /// degree bound (`2N` for a trace of height `N`) and then applies the blowup to that, so the
    /// committed codewords have rate exactly `2^-log_blowup`. Under unique decoding each query
    /// gives `-log2((1 + 1/8) / 2) = 0.830` bits: `143 * 0.830 + 22 = 140.7` proven bits. The
    /// hiding budget is `2 * (143 + 3 * 2) = 298` values, so every table needs at least 512 rows.
    pub const fn outer_wrap() -> Self {
        Self {
            log_blowup: 3,
            num_queries: 143,
            query_pow_bits: 22,
            max_log_arity: 3,
            num_random_codewords: GOLDILOCKS_D3_W12_ZK_EXT_DEGREE,
        }
    }

    /// Cheap parameters in the same shape for fast tests (rate 1/2, 8 queries, 4 bits of
    /// grinding). Hiding holds (the budget is enforced as usual), soundness does not.
    pub const fn test() -> Self {
        Self {
            log_blowup: 1,
            num_queries: 8,
            query_pow_bits: 4,
            max_log_arity: 3,
            num_random_codewords: GOLDILOCKS_D3_W12_ZK_EXT_DEGREE,
        }
    }

    /// Refuse parameters the hiding PCS cannot use safely.
    pub const fn validate(&self) -> Result<(), GoldilocksD3W12ZkError> {
        if self.num_random_codewords < GOLDILOCKS_D3_W12_ZK_EXT_DEGREE {
            return Err(GoldilocksD3W12ZkError::InsufficientRandomCodewords {
                required: GOLDILOCKS_D3_W12_ZK_EXT_DEGREE,
                got: self.num_random_codewords,
            });
        }
        if self.log_blowup == 0 {
            return Err(GoldilocksD3W12ZkError::InvalidFri(
                "log_blowup must be at least 1",
            ));
        }
        if self.num_queries == 0 {
            return Err(GoldilocksD3W12ZkError::InvalidFri(
                "num_queries must be positive",
            ));
        }
        if self.max_log_arity == 0 {
            return Err(GoldilocksD3W12ZkError::InvalidFri(
                "max_log_arity must be at least 1",
            ));
        }
        match self.min_trace_height() {
            Some(_) => Ok(()),
            None => Err(GoldilocksD3W12ZkError::BudgetOverflow),
        }
    }

    /// The hiding PCS's per-matrix budget at [`BATCH_STARK_MAX_OPENING_POINTS`] points:
    /// `2 * (num_queries + 3 * 2)` (p3-fri `HidingFriPcs::hiding_budget`). A committed matrix of
    /// height `N` carries `N` independent mask values per column, and must have `N` at least this.
    pub const fn hiding_budget(&self) -> Option<usize> {
        let Some(points) =
            GOLDILOCKS_D3_W12_ZK_EXT_DEGREE.checked_mul(BATCH_STARK_MAX_OPENING_POINTS)
        else {
            return None;
        };
        let Some(disclosed) = self.num_queries.checked_add(points) else {
            return None;
        };
        disclosed.checked_mul(2)
    }

    /// The smallest power-of-two table height that covers [`Self::hiding_budget`].
    pub const fn min_trace_height(&self) -> Option<usize> {
        match self.hiding_budget() {
            Some(budget) => budget.checked_next_power_of_two(),
            None => None,
        }
    }

    /// `packing` with its minimum trace height raised to [`Self::min_trace_height`], so every
    /// table is padded up to the hiding budget. Per-table minimum heights below the new floor make
    /// the packing invalid, and the prover then refuses it.
    pub fn pad_table_packing(
        &self,
        packing: crate::TablePacking,
    ) -> Result<crate::TablePacking, GoldilocksD3W12ZkError> {
        let required = self
            .min_trace_height()
            .ok_or(GoldilocksD3W12ZkError::BudgetOverflow)?;
        let floor = packing.min_trace_height().max(required);
        Ok(packing.with_min_trace_height(floor))
    }

    /// Refuse a packing that would let a table fall below the hiding budget. (The hiding PCS
    /// refuses such a table anyway, at commitment, opening and verification; this fails earlier.)
    pub fn check_table_packing(
        &self,
        packing: &crate::TablePacking,
    ) -> Result<(), GoldilocksD3W12ZkError> {
        let required = self
            .min_trace_height()
            .ok_or(GoldilocksD3W12ZkError::BudgetOverflow)?;
        let floors = [
            Some(packing.min_trace_height()),
            packing.alu_min_height(),
            packing.public_min_height(),
            packing.const_min_height(),
        ];
        let lowest = floors
            .into_iter()
            .flatten()
            .chain(packing.npo_min_heights().map(|(_, height)| height))
            .min()
            .unwrap_or(0);
        if lowest < required {
            return Err(GoldilocksD3W12ZkError::TableBelowHidingBudget {
                required,
                got: lowest,
            });
        }
        Ok(())
    }
}

/// Creates the salted hiding Goldilocks D3 / W12 configuration.
///
/// Every commitment is a salted Merkle tree ([`GoldilocksD3W12HidingMmcs`]), the FRI
/// commit-phase commitments included, and the PCS is p3-fri's [`HidingFriPcs`]: random codewords,
/// trace randomization (each committed trace of height `N` becomes a degree-`2N` polynomial with
/// `N` fresh random values per column), quotient-chunk masking and a randomization polynomial.
///
/// # Randomness
///
/// The input MMCS's salts, the FRI MMCS's salts and the PCS's masks come from three generators
/// ([`GoldilocksD3W12ZkRng`]), each seeded with a fresh draw from `os_entropy`, so their streams
/// are independent. Within a stream nothing is reused: every commitment advances it, and p3-fri
/// lets the masks of private prover data be opened only once.
///
/// `os_entropy` must be the operating system's generator, for example `rand::rngs::SysRng`
/// (rand's `sys_rng` feature). This crate is `no_std` and does not enable an OS-entropy feature,
/// so it cannot read OS entropy itself. There is deliberately no constructor that takes a seed:
/// a predictable source makes every salt and mask reproducible and voids hiding.
///
/// Under [`crate::BatchStarkProver::prepare_circuit`], the circuit's preprocessed commitment is
/// salted from the input MMCS's stream as well, so every preparation gives a different verifying
/// key. Its contents are public (p3-fri pads it with zero rows, not random ones), so to get a
/// verifying key that anyone can recompute from the circuit, prepare with
/// [`crate::BatchStarkProver::prepare_circuit_with_public_preprocessing`] and
/// [`goldilocks_d3_w12_zk_public_preprocessing`]: the preprocessed commitment then uses a fixed,
/// public salt stream, and every witness-dependent salt and mask still comes from `os_entropy`.
///
/// # Table heights
///
/// The PCS refuses any committed table shorter than [`GoldilocksD3W12ZkParams::hiding_budget`].
/// Pad the circuit's tables with [`GoldilocksD3W12ZkParams::pad_table_packing`].
pub fn goldilocks_d3_w12_zk<E>(
    params: GoldilocksD3W12ZkParams,
    os_entropy: &mut E,
) -> Result<GoldilocksD3W12ZkConfig, GoldilocksD3W12ZkError>
where
    E: rand::TryCryptoRng + ?Sized,
{
    use alloc::string::ToString;
    use rand::SeedableRng;

    params.validate()?;
    let mut fresh = || {
        GoldilocksD3W12ZkRng::try_from_rng(&mut *os_entropy)
            .map_err(|error| GoldilocksD3W12ZkError::Entropy(error.to_string()))
    };
    // Three separately seeded streams: input-MMCS salts, FRI-MMCS salts, PCS masks.
    let input_salts = fresh()?;
    let fri_salts = fresh()?;
    let masks = fresh()?;

    Ok(goldilocks_d3_w12_zk_from_streams(
        params,
        input_salts,
        fri_salts,
        masks,
    ))
}

/// [`GoldilocksD3W12ZkConfig`] at `params` (already validated) over the given salt and mask
/// streams.
fn goldilocks_d3_w12_zk_from_streams(
    params: GoldilocksD3W12ZkParams,
    input_salts: GoldilocksD3W12ZkRng,
    fri_salts: GoldilocksD3W12ZkRng,
    masks: GoldilocksD3W12ZkRng,
) -> GoldilocksD3W12ZkConfig {
    let perm = default_goldilocks_poseidon2_12();
    let input_mmcs = GoldilocksD3W12HidingMmcs::new(
        PaddingFreeSponge::new(perm.clone()),
        TruncatedPermutation::new(perm.clone()),
        0,
        input_salts,
    );
    let fri_mmcs = GoldilocksD3W12HidingMmcs::new(
        PaddingFreeSponge::new(perm.clone()),
        TruncatedPermutation::new(perm.clone()),
        0,
        fri_salts,
    );
    let fri_params = FriParameters {
        log_blowup: params.log_blowup,
        log_final_poly_len: 0,
        max_log_arity: params.max_log_arity,
        num_queries: params.num_queries,
        batch_proof_of_work_bits: 0,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: params.query_pow_bits,
        mmcs: ExtensionMmcs::new(fri_mmcs),
    };
    let pcs = HidingFriPcs::new(
        Radix2DitParallel::default(),
        input_mmcs,
        fri_params,
        params.num_random_codewords,
        masks,
    );
    StarkConfig::new(pcs, DuplexChallenger::new(perm))
        .with_lookup_proof_of_work_bits(0)
        .with_ood_proof_of_work_bits(0)
}

/// The public seeds of [`goldilocks_d3_w12_zk_public_preprocessing`]'s three streams (input-MMCS
/// salts, FRI-MMCS salts, PCS masks). Only the first is ever drawn from: committing preprocessing
/// salts its leaves and uses no FRI commitment or mask.
const GOLDILOCKS_D3_W12_ZK_PUBLIC_PREPROCESSING_SEEDS: [[u8; 32]; 3] = [
    *b"p3-circuit-prover/D3W12ZK/prep/0",
    *b"p3-circuit-prover/D3W12ZK/prep/1",
    *b"p3-circuit-prover/D3W12ZK/prep/2",
];

/// The configuration that commits a circuit's public preprocessing for proofs under
/// [`goldilocks_d3_w12_zk`] with the same `params`, with salts from a fixed, public seed.
///
/// Pass it to [`crate::BatchStarkProver::prepare_circuit_with_public_preprocessing`] (with a
/// prover built from [`goldilocks_d3_w12_zk`]) to make the preprocessed commitment, and so the
/// verifying key, a deterministic function of the circuit and `params`: two preparations of one
/// circuit, by the prover or by a verifier, get the same key.
///
/// This hides nothing it should not. The preprocessed matrices are the public circuit description;
/// the hiding PCS commits them interleaved with zero rows and opens them without random codewords,
/// and a verifier could recompute every opened row anyway. Merkle binding does not depend on the
/// salts being secret. Every witness-dependent commitment, salt and mask is still drawn by the
/// proving configuration from its OS-entropy streams; this configuration cannot be taken out of
/// [`crate::PublicPreprocessingConfig`], so it never proves.
///
/// The salts come from [`GoldilocksD3W12ZkRng`] (`rand`'s `StdRng`), so the key also depends on
/// that generator's algorithm in the pinned `rand` release.
pub fn goldilocks_d3_w12_zk_public_preprocessing(
    params: GoldilocksD3W12ZkParams,
) -> Result<crate::PublicPreprocessingConfig<GoldilocksD3W12ZkConfig>, GoldilocksD3W12ZkError> {
    use rand::SeedableRng;

    params.validate()?;
    let [input_salts, fri_salts, masks] =
        GOLDILOCKS_D3_W12_ZK_PUBLIC_PREPROCESSING_SEEDS.map(GoldilocksD3W12ZkRng::from_seed);
    Ok(crate::PublicPreprocessingConfig::new(
        goldilocks_d3_w12_zk_from_streams(params, input_salts, fri_salts, masks),
    ))
}

/// Trait bounds for STARK-compatible fields.
pub trait StarkField: Field + PrimeCharacteristicRing + TwoAdicField + PrimeField64 {}

impl<F> StarkField for F where F: Field + PrimeCharacteristicRing + TwoAdicField + PrimeField64 {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_fields_configs_compile() {
        let _bb: BabyBearConfig = baby_bear();
        let _kb: KoalaBearConfig = koala_bear();
        let _gl: GoldilocksConfig = goldilocks();
        let _gl3: GoldilocksD3W12Config = goldilocks_d3_w12();
    }

    /// An entropy source that always fails, and one that counts the bytes drawn from it.
    struct Entropy {
        fail: bool,
        drawn: usize,
        state: u64,
    }

    impl rand::TryRng for Entropy {
        type Error = core::fmt::Error;

        fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
            self.try_next_u64().map(|x| x as u32)
        }

        fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
            let mut bytes = [0u8; 8];
            self.try_fill_bytes(&mut bytes)?;
            Ok(u64::from_le_bytes(bytes))
        }

        fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Self::Error> {
            if self.fail {
                return Err(core::fmt::Error);
            }
            for byte in dst.iter_mut() {
                self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1);
                *byte = (self.state >> 56) as u8;
            }
            self.drawn += dst.len();
            Ok(())
        }
    }

    impl rand::TryCryptoRng for Entropy {}

    #[test]
    fn goldilocks_d3_w12_zk_params_and_budget() {
        let outer = GoldilocksD3W12ZkParams::outer_wrap();
        outer.validate().unwrap();
        assert_eq!(outer.hiding_budget(), Some(298));
        assert_eq!(outer.min_trace_height(), Some(512));
        let test = GoldilocksD3W12ZkParams::test();
        assert_eq!(test.hiding_budget(), Some(28));
        assert_eq!(test.min_trace_height(), Some(32));

        for (params, expected) in [
            (
                GoldilocksD3W12ZkParams {
                    num_random_codewords: 2,
                    ..outer
                },
                GoldilocksD3W12ZkError::InsufficientRandomCodewords {
                    required: 3,
                    got: 2,
                },
            ),
            (
                GoldilocksD3W12ZkParams {
                    log_blowup: 0,
                    ..outer
                },
                GoldilocksD3W12ZkError::InvalidFri("log_blowup must be at least 1"),
            ),
            (
                GoldilocksD3W12ZkParams {
                    num_queries: 0,
                    ..outer
                },
                GoldilocksD3W12ZkError::InvalidFri("num_queries must be positive"),
            ),
            (
                GoldilocksD3W12ZkParams {
                    num_queries: usize::MAX,
                    ..outer
                },
                GoldilocksD3W12ZkError::BudgetOverflow,
            ),
        ] {
            assert_eq!(params.validate(), Err(expected));
        }

        // Padding raises the floor; overrides below it are refused.
        let packing = outer
            .pad_table_packing(crate::TablePacking::new(1, 1))
            .unwrap();
        assert_eq!(packing.min_trace_height(), 512);
        outer.check_table_packing(&packing).unwrap();
        assert_eq!(
            outer.check_table_packing(&crate::TablePacking::new(1, 1).with_min_trace_height(256)),
            Err(GoldilocksD3W12ZkError::TableBelowHidingBudget {
                required: 512,
                got: 256,
            })
        );
        let short_npo = packing.with_npo_min_height(p3_circuit::ops::NpoTypeId::recompose(), 64);
        assert!(outer.check_table_packing(&short_npo).is_err());
        let taller = outer
            .pad_table_packing(crate::TablePacking::new(1, 1).with_min_trace_height(2048))
            .unwrap();
        assert_eq!(taller.min_trace_height(), 2048);
    }

    #[test]
    fn goldilocks_d3_w12_zk_draws_three_seeds_and_reports_entropy_failure() {
        let mut source = Entropy {
            fail: false,
            drawn: 0,
            state: 1,
        };
        let _config: GoldilocksD3W12ZkConfig =
            goldilocks_d3_w12_zk(GoldilocksD3W12ZkParams::test(), &mut source).unwrap();
        // Three 32-byte ChaCha seeds: input salts, FRI salts, masks.
        assert_eq!(source.drawn, 3 * 32);

        let mut failing = Entropy {
            fail: true,
            drawn: 0,
            state: 1,
        };
        assert!(matches!(
            goldilocks_d3_w12_zk(GoldilocksD3W12ZkParams::test(), &mut failing),
            Err(GoldilocksD3W12ZkError::Entropy(_))
        ));
        // Invalid parameters are refused before any entropy is drawn.
        let mut untouched = Entropy {
            fail: false,
            drawn: 0,
            state: 1,
        };
        assert!(
            goldilocks_d3_w12_zk(
                GoldilocksD3W12ZkParams {
                    num_random_codewords: 0,
                    ..GoldilocksD3W12ZkParams::test()
                },
                &mut untouched
            )
            .is_err()
        );
        assert_eq!(untouched.drawn, 0);
    }

    #[test]
    fn goldilocks_d3_w12_zk_public_preprocessing_seeds_and_params() {
        // Three distinct public seeds.
        let seeds = GOLDILOCKS_D3_W12_ZK_PUBLIC_PREPROCESSING_SEEDS;
        assert!(seeds[0] != seeds[1] && seeds[1] != seeds[2] && seeds[0] != seeds[2]);
        goldilocks_d3_w12_zk_public_preprocessing(GoldilocksD3W12ZkParams::outer_wrap()).unwrap();
        assert_eq!(
            goldilocks_d3_w12_zk_public_preprocessing(GoldilocksD3W12ZkParams {
                num_random_codewords: 2,
                ..GoldilocksD3W12ZkParams::outer_wrap()
            })
            .unwrap_err(),
            GoldilocksD3W12ZkError::InsufficientRandomCodewords {
                required: 3,
                got: 2,
            }
        );
    }
}
