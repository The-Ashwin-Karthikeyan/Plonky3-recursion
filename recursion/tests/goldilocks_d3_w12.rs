//! Goldilocks D3 / Poseidon2 width-12 circuits against native Plonky3, by execution only.
//!
//! The circuits run over `CubicTrinomialExtensionField<Goldilocks>` with the
//! `GOLDILOCKS_D3_W12` permutation (four cubic limbs: rate 6, digest 6 base elements) and
//! p3-goldilocks' reference permutation `default_goldilocks_poseidon2_12()`. Each test
//! replays a native computation and checks the circuit reaches the same values:
//!
//! - the leaf sponge against `PaddingFreeSponge<_, 12, 6, 6>`, for leaf widths 1-13;
//! - the 2-to-1 compression against `TruncatedPermutation<_, 2, 6, 12>`, in both directions,
//!   and full Merkle openings with mixed matrix heights;
//! - the challenger against `DuplexChallenger<_, _, 12, 6>`.
//!
//! Proving these circuits needs the degree-3 prover integration and is not exercised here.

use p3_challenger::{
    CanObserve, CanSample, CanSampleBits, DuplexChallenger, FieldChallenger, GrindingChallenger,
};
use p3_circuit::CircuitBuilder;
use p3_circuit::ops::{
    GoldilocksD3Width12, Poseidon2Config, generate_poseidon2_trace, generate_recompose_trace,
    perm_private_data,
};
use p3_commit::Mmcs;
use p3_field::extension::CubicTrinomialExtensionField;
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
use p3_goldilocks::{Goldilocks, Poseidon2Goldilocks, default_goldilocks_poseidon2_12};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_recursion::challenger::CircuitChallenger;
use p3_recursion::pcs::verify_batch_circuit;
use p3_recursion::traits::RecursiveChallenger;
use p3_symmetric::{
    CryptographicHasher, PaddingFreeSponge, Permutation, PseudoCompressionFunction,
    TruncatedPermutation,
};
use rand::rngs::SmallRng;
use rand::{RngExt, SeedableRng};

type F = Goldilocks;
type EF = CubicTrinomialExtensionField<F>;
type Perm = Poseidon2Goldilocks<WIDTH>;
type Hash = PaddingFreeSponge<Perm, WIDTH, RATE, DIGEST>;
type Compress = TruncatedPermutation<Perm, 2, DIGEST, WIDTH>;
type NativeMmcs = MerkleTreeMmcs<F, F, Hash, Compress, 2, DIGEST>;

const D: usize = 3;
const WIDTH: usize = 12;
const RATE: usize = 6;
const DIGEST: usize = 6;
const CONFIG: Poseidon2Config = Poseidon2Config::GOLDILOCKS_D3_W12;

fn setup_circuit() -> CircuitBuilder<EF> {
    let mut circuit = CircuitBuilder::<EF>::new();
    circuit.enable_poseidon2_perm_width_12::<GoldilocksD3Width12, _>(
        generate_poseidon2_trace::<EF, GoldilocksD3Width12>,
        default_goldilocks_poseidon2_12(),
    );
    circuit.enable_recompose::<F>(generate_recompose_trace::<F, EF>);
    circuit
}

fn native_mmcs() -> NativeMmcs {
    let perm = default_goldilocks_poseidon2_12();
    NativeMmcs::new(Hash::new(perm.clone()), Compress::new(perm), 0)
}

/// Pack a 6-element digest into its two cubic limbs.
fn digest_limbs(digest: &[F]) -> Vec<EF> {
    assert_eq!(digest.len(), DIGEST);
    digest
        .chunks(D)
        .map(|chunk| EF::from_basis_coefficients_slice(chunk).unwrap())
        .collect()
}

/// Commit `mats` natively, then check every opening with a `verify_batch_circuit` circuit.
///
/// The root, the opened rows and the direction bits are public inputs; the Merkle siblings
/// are private data. Every opening must run, and each one must fail with its root changed.
fn check_all_openings(mats: Vec<RowMajorMatrix<F>>) {
    let mmcs = native_mmcs();
    let dimensions: Vec<_> = mats.iter().map(Matrix::dimensions).collect();
    let max_height = dimensions.iter().map(|d| d.height).max().unwrap();
    let log_max_height = max_height.next_power_of_two().trailing_zeros() as usize;
    let (commitment, prover_data) = mmcs.commit(mats);
    assert_eq!(commitment.num_roots(), 1);
    let root = digest_limbs(&commitment.roots()[0]);

    for index in 0..max_height {
        let opening = mmcs.open_batch(index, &prover_data);

        let mut circuit = setup_circuit();
        let opened: Vec<Vec<_>> = opening
            .opened_values
            .iter()
            .map(|row| circuit.alloc_public_inputs(row.len(), "opened row"))
            .collect();
        let directions = circuit.alloc_public_inputs(log_max_height, "directions");
        let cap = vec![circuit.alloc_public_inputs(CONFIG.rate_ext(), "root")];
        let mmcs_ops = verify_batch_circuit::<F, EF>(
            &mut circuit,
            CONFIG,
            &cap,
            &dimensions,
            &directions,
            &opened,
            None,
        )
        .expect("D3/W12 MMCS circuit builds");
        let circuit = circuit.build().expect("D3/W12 MMCS circuit compiles");

        let mut public_inputs: Vec<EF> = opening
            .opened_values
            .iter()
            .flat_map(|row| row.iter().map(|&v| EF::from(v)))
            .collect();
        public_inputs.extend((0..log_max_height).map(|k| EF::from_bool(index >> k & 1 == 1)));
        let root_at = public_inputs.len();
        public_inputs.extend(root.iter().copied());

        let siblings: Vec<Vec<EF>> = opening
            .opening_proof
            .iter()
            .map(|digest| digest_limbs(digest))
            .collect();
        assert_eq!(mmcs_ops.len(), siblings.len());

        for tamper in [false, true] {
            let mut inputs = public_inputs.clone();
            if tamper {
                inputs[root_at] += EF::ONE;
            }
            let mut runner = circuit.runner();
            runner.set_public_inputs(&inputs).unwrap();
            for (&op_id, sibling) in mmcs_ops.iter().zip(&siblings) {
                runner
                    .set_private_data(op_id, perm_private_data(CONFIG, sibling.clone()))
                    .unwrap();
            }
            let result = runner.run();
            if tamper {
                assert!(
                    result.is_err(),
                    "index {index}: a wrong root must be rejected"
                );
            } else {
                result.unwrap_or_else(|e| panic!("index {index}: circuit disagrees: {e:?}"));
            }
        }
    }
}

/// The circuit leaf sponge equals `PaddingFreeSponge<_, 12, 6, 6>` for widths 1-13: a
/// partial first chunk, partial limbs, an exact chunk, and two and three chunks.
#[test]
fn sponge_matches_padding_free_sponge_for_widths_1_to_13() {
    let mut rng = SmallRng::seed_from_u64(0xD3_01);
    let hash = Hash::new(default_goldilocks_poseidon2_12());
    for width in 1..=13 {
        let leaf: Vec<F> = (0..width).map(|_| rng.random()).collect();
        let expected: [F; DIGEST] = hash.hash_iter(leaf.iter().copied());
        // A one-row matrix commits to its leaf digest.
        let (commitment, _) = native_mmcs().commit(vec![RowMajorMatrix::new(leaf.clone(), width)]);
        assert_eq!(commitment.roots()[0], expected);
        check_all_openings(vec![RowMajorMatrix::new(leaf, width)]);
    }
}

/// The circuit compression equals `TruncatedPermutation<_, 2, 6, 12>` with the opened leaf as
/// the left child (index 0) and as the right child (index 1).
#[test]
fn compression_matches_truncated_permutation_in_both_directions() {
    let mut rng = SmallRng::seed_from_u64(0xD3_02);
    let hash = Hash::new(default_goldilocks_poseidon2_12());
    let compress = Compress::new(default_goldilocks_poseidon2_12());
    for width in [1, 6, 7] {
        let values: Vec<F> = (0..2 * width).map(|_| rng.random()).collect();
        let left: [F; DIGEST] = hash.hash_iter(values[..width].iter().copied());
        let right: [F; DIGEST] = hash.hash_iter(values[width..].iter().copied());
        let matrix = RowMajorMatrix::new(values, width);
        let (commitment, _) = native_mmcs().commit(vec![matrix.clone()]);
        assert_eq!(commitment.roots()[0], compress.compress([left, right]));
        check_all_openings(vec![matrix]);
    }
}

/// Full D3/W12 Merkle openings: a deeper tree, and matrices of mixed heights whose rows are
/// injected at their own level.
#[test]
fn mmcs_openings_with_mixed_heights() {
    let mut rng = SmallRng::seed_from_u64(0xD3_03);
    let mut matrix = |height: usize, width: usize| {
        RowMajorMatrix::new((0..height * width).map(|_| rng.random()).collect(), width)
    };
    check_all_openings(vec![matrix(8, 5)]);
    check_all_openings(vec![
        matrix(8, 3),
        matrix(4, 7),
        matrix(2, 13),
        matrix(8, 1),
    ]);
    check_all_openings(vec![matrix(5, 2), matrix(3, 6)]);
}

/// One transcript through every challenger operation, checked value by value against the
/// native `DuplexChallenger<Goldilocks, Poseidon2Goldilocks<12>, 12, 6>`.
#[test]
fn challenger_transcript_matches_native_duplex_challenger() {
    let mut rng = SmallRng::seed_from_u64(0xD3_04);
    let mut native =
        DuplexChallenger::<F, Perm, WIDTH, RATE>::new(default_goldilocks_poseidon2_12());
    let mut circuit = setup_circuit();
    let mut cc = CircuitChallenger::<WIDTH, RATE, Poseidon2Config>::new_goldilocks_d3();

    fn expect(circuit: &mut CircuitBuilder<EF>, got: p3_recursion::Target, value: EF) {
        let expected = circuit.define_const(value);
        circuit.connect(got, expected);
    }

    // Base observations: a partial absorb, an exact one, and one spilling into the next row.
    for count in [4, RATE, RATE + 5] {
        for _ in 0..count {
            let v: F = rng.random();
            native.observe(v);
            let t = circuit.define_const(EF::from(v));
            RecursiveChallenger::<F, EF>::observe(&mut cc, &mut circuit, t);
        }
        // Samples past one rate's worth force a squeeze.
        for _ in 0..(RATE + 2) {
            let s: F = native.sample();
            let cs = RecursiveChallenger::<F, EF>::sample(&mut cc, &mut circuit);
            expect(&mut circuit, cs, EF::from(s));
        }
    }

    // Extension observations (each absorbs its three coefficients) and extension samples.
    for count in [1, 2, 3] {
        for _ in 0..count {
            let v: EF = rng.random();
            native.observe_algebra_element(v);
            let t = circuit.define_const(v);
            RecursiveChallenger::<F, EF>::observe_ext(&mut cc, &mut circuit, t);
        }
        for _ in 0..3 {
            let s: EF = native.sample_algebra_element();
            let cs = RecursiveChallenger::<F, EF>::sample_ext(&mut cc, &mut circuit);
            expect(&mut circuit, cs, s);
        }
    }

    // Query-index bits.
    for num_bits in [1, 7, 20, 32] {
        let native_bits: usize = native.sample_bits(num_bits);
        let bits = RecursiveChallenger::<F, EF>::sample_bits(&mut cc, &mut circuit, num_bits)
            .expect("sample_bits builds");
        assert_eq!(bits.len(), num_bits);
        for (k, &bit) in bits.iter().enumerate() {
            expect(&mut circuit, bit, EF::from_bool(native_bits >> k & 1 == 1));
        }
    }

    // Proof of work: a ground witness passes natively and in the circuit.
    let pow_bits = 8;
    let before_pow = native.clone();
    let witness = native.clone().grind(pow_bits);
    assert!(native.check_witness(pow_bits, witness));
    let witness_target = circuit.alloc_public_input("pow witness");
    RecursiveChallenger::<F, EF>::check_pow_witness(
        &mut cc,
        &mut circuit,
        pow_bits,
        witness_target,
    )
    .expect("check_pow_witness builds");

    // The transcript stays in step after the PoW check.
    let s: EF = native.sample_algebra_element();
    let cs = RecursiveChallenger::<F, EF>::sample_ext(&mut cc, &mut circuit);
    expect(&mut circuit, cs, s);

    let circuit = circuit.build().expect("challenger circuit compiles");
    let mut runner = circuit.runner();
    runner.set_public_inputs(&[EF::from(witness)]).unwrap();
    runner
        .run()
        .expect("D3/W12 challenger transcript matches native");

    // A witness that fails the native check fails in the circuit too.
    let bad = (1u64..)
        .map(|k| witness + F::from_u64(k))
        .find(|&w| !before_pow.clone().check_witness(pow_bits, w))
        .unwrap();
    let mut runner = circuit.runner();
    runner.set_public_inputs(&[EF::from(bad)]).unwrap();
    assert!(
        runner.run().is_err(),
        "a witness failing the PoW check must be rejected"
    );
}

/// The native permutation is p3-goldilocks' reference instance: its known answer on
/// `[0, 1, ..., 11]` (`test_default_goldilocks_poseidon2_width_12`; lrup's
/// `poseidon_perm_known_answer`), and the circuit permutation reproduces it.
#[test]
fn permutation_known_answer_native_and_in_circuit() {
    let input: [F; WIDTH] = core::array::from_fn(|i| F::from_u64(i as u64));
    let expected = [
        0xf292ab67c0f14b03,
        0x0a32f1b37656544c,
        0x053c61ab895498de,
        0x02ff92e55b196ffb,
        0x58176e8f6f58cab2,
        0xb0aa1206e7aec0f8,
        0xe90c13f3dce83ca4,
        0xf4da15333edf39c2,
        0x23b701c053c2ca6c,
        0xd233d593dcdfbf58,
        0x4effa5f9516fb52e,
        0x0aaf4489f1f40166,
    ]
    .map(F::from_u64);
    assert_eq!(default_goldilocks_poseidon2_12().permute(input), expected);

    // In the circuit: a fresh sponge row over the four input limbs, all outputs exposed.
    let mut circuit = setup_circuit();
    let limbs: Vec<_> = input
        .chunks(D)
        .map(|c| circuit.define_const(EF::from_basis_coefficients_slice(c).unwrap()))
        .collect();
    let (_, outputs) = circuit
        .add_poseidon2_perm(&p3_circuit::ops::Poseidon2PermCall {
            config: CONFIG,
            new_start: true,
            merkle_path: false,
            mmcs_bit: None,
            mmcs_bit2: None,
            inputs: limbs.into_iter().map(Some).collect(),
            out_ctl: vec![true; CONFIG.rate_ext()],
            return_all_outputs: true,
            absorb_len: 0,
        })
        .expect("permutation call builds");
    for (limb, chunk) in outputs.iter().zip(expected.chunks(D)) {
        let want = circuit.define_const(EF::from_basis_coefficients_slice(chunk).unwrap());
        circuit.connect(limb.expect("all outputs returned"), want);
    }
    circuit
        .build()
        .unwrap()
        .runner()
        .run()
        .expect("circuit permutation matches the reference");
}
