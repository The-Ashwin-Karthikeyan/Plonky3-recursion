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
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_goldilocks::{Goldilocks, Poseidon2Goldilocks, default_goldilocks_poseidon2_12};
use p3_koala_bear::{KoalaBear, Poseidon2KoalaBear, default_koalabear_poseidon2_16};
use p3_merkle_tree::MerkleTreeMmcs;
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
}
