//! Goldilocks D3 / Poseidon2 width-12 circuits against native Plonky3.
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
//! The `proving` tests then prove such circuits with `BatchStarkProver` at `D = 3` over
//! `config::goldilocks_d3_w12()` and verify them: the plain permutation and leaf sponge, Merkle
//! compression rows in both directions, the challenger table, and the shared challenger table.
//! Each Poseidon2 table is materialized both from the committed preprocessing and through
//! `TableProver::batch_instance_d3`. A forged permutation output or Merkle sibling must reach
//! the verifier and be rejected.

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

/// Commit `mats` natively, then check every opening natively and with a
/// `verify_batch_circuit` circuit.
///
/// The root, the opened rows and the direction bits are public inputs; the Merkle siblings
/// are private data. Every honest opening must run, and each one must fail with its root, an
/// opened value (first and last) or a Merkle sibling (first and last level) changed.
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
        mmcs.verify_batch(&commitment, &dimensions, index, (&opening).into())
            .unwrap_or_else(|e| panic!("index {index}: native opening rejected: {e:?}"));

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

        #[derive(Debug)]
        enum Tamper {
            None,
            Root,
            Opened(usize),
            Sibling(usize, usize),
        }
        let last_level = siblings.len().saturating_sub(1);
        let mut tampers = vec![
            Tamper::None,
            Tamper::Root,
            Tamper::Opened(0),
            Tamper::Opened(root_at - log_max_height - 1),
        ];
        if !siblings.is_empty() {
            tampers.extend([
                Tamper::Sibling(0, 0),
                Tamper::Sibling(last_level, DIGEST - 1),
            ]);
        }
        for tamper in tampers {
            let mut inputs = public_inputs.clone();
            let mut siblings = siblings.clone();
            match tamper {
                Tamper::None => {}
                Tamper::Root => inputs[root_at] += EF::ONE,
                Tamper::Opened(k) => inputs[k] += EF::ONE,
                Tamper::Sibling(level, coefficient) => {
                    let limb = &mut siblings[level][coefficient / D];
                    let mut coeffs =
                        BasedVectorSpace::<F>::as_basis_coefficients_slice(limb).to_vec();
                    coeffs[coefficient % D] += F::ONE;
                    *limb = EF::from_basis_coefficients_slice(&coeffs).unwrap();
                }
            }
            let mut runner = circuit.runner();
            runner.set_public_inputs(&inputs).unwrap();
            for (&op_id, sibling) in mmcs_ops.iter().zip(&siblings) {
                runner
                    .set_private_data(op_id, perm_private_data(CONFIG, sibling.clone()))
                    .unwrap();
            }
            let result = runner.run();
            if matches!(tamper, Tamper::None) {
                result.unwrap_or_else(|e| panic!("index {index}: circuit disagrees: {e:?}"));
            } else {
                assert!(
                    result.is_err(),
                    "index {index}: {tamper:?} must be rejected"
                );
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

/// `p - 1`, the largest canonical Goldilocks element.
const P_MINUS_1: u64 = 0xFFFF_FFFF_0000_0000;

/// Known answers of `default_goldilocks_poseidon2_12()` on the four inputs of lrup's
/// `poseidon_perm_known_answer` (lrup-backend-p3 `config.rs`; lrup's `poseidon_perm()` is that
/// reference permutation), as `(input, output)`. lrup pins the outputs of the first two; the
/// other two were computed with the same reference permutation. `[0, 1, ..., 11]` is also
/// p3-goldilocks' own `test_default_goldilocks_poseidon2_width_12` vector. The W12 AIR trace
/// is pinned to the same literals in `poseidon2-circuit-air` (`goldilocks_d3_width12`).
const KAT: [([u64; WIDTH], [u64; WIDTH]); 4] = [
    (
        [0; WIDTH],
        [
            0x5b31a8b9799ff836,
            0xe385174fe60f4b08,
            0xe82c6be88d50767c,
            0x2778f3b6a18981e2,
            0xdeebf402c2a98074,
            0x7c963653f27a1734,
            0x0f46bb6190c980e7,
            0x49828ccc24482bf3,
            0xd73a07cf7eda8691,
            0xab9ca371bae24a24,
            0x75f7223257cb0b1d,
            0x9703d4dc4a9dcbf6,
        ],
    ),
    (
        [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
        [
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
        ],
    ),
    (
        [P_MINUS_1; WIDTH],
        [
            0x86f498c3f6f8c30a,
            0xb9c1930740ce3e3f,
            0xf38d22f1852fbb43,
            0xf56e2de37c6f1261,
            0xe8e6c9350180fba7,
            0xdc389fa621dbad0c,
            0x5ed1d3754c149bb3,
            0xb151306f2c45d95d,
            0xd0491b449c1d2812,
            0x5fe3fcb315c0cee8,
            0x13199f45c406f769,
            0x9c7d84e25ded814c,
        ],
    ),
    (
        [
            0x4C52_5550,
            0x0123_4567_89AB_CDEF,
            0xFEDC_BA98_7654_3210,
            1,
            P_MINUS_1,
            2,
            0xDEAD_BEEF,
            0x8000_0000_0000_0000,
            0x0000_0001_0000_0000,
            0xFFFF_FFFE_FFFF_FFFF,
            7,
            0x5555_5555_5555_5555,
        ],
        [
            0xa5477ce5e959c326,
            0xd703c3b8bfc7ef6f,
            0xf6c05ec06abc129b,
            0xdc0d05d40a0b4cfd,
            0x114f366e8f9d209c,
            0x37c4e727b115107b,
            0xfc69b775bb1e8b15,
            0xf1dceac2e25ceca6,
            0xac4263d8502eba31,
            0xe2b8b4f328f940e0,
            0x49f540ce61e84e29,
            0x8a68d27615c3d428,
        ],
    ),
];

/// The native permutation is p3-goldilocks' reference instance, the one lrup's
/// `poseidon_perm()` returns: it reproduces every [`KAT`] literal, and so does the circuit
/// permutation (one fresh sponge row per input, all twelve outputs connected to the literal).
/// A circuit expecting one changed output coefficient must fail.
#[test]
fn permutation_known_answer_native_and_in_circuit() {
    let native = default_goldilocks_poseidon2_12();
    for (input, output) in KAT {
        assert_eq!(
            native.permute(input.map(F::from_u64)),
            output.map(F::from_u64),
            "native permutation of {input:#x?}"
        );
    }

    let build = |tamper: Option<(usize, usize)>| {
        let mut circuit = setup_circuit();
        for (case, (input, output)) in KAT.iter().enumerate() {
            let limbs: Vec<_> = input
                .map(F::from_u64)
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
            let mut expected = output.map(F::from_u64);
            if let Some((tampered_case, k)) = tamper
                && tampered_case == case
            {
                expected[k] += F::ONE;
            }
            for (limb, chunk) in outputs.iter().zip(expected.chunks(D)) {
                let want = circuit.define_const(EF::from_basis_coefficients_slice(chunk).unwrap());
                circuit.connect(limb.expect("all outputs returned"), want);
            }
        }
        circuit.build().unwrap()
    };

    build(None)
        .runner()
        .run()
        .expect("circuit permutation matches the known answers");
    for (case, k) in [(0, 0), (1, 5), (2, 6), (3, 11)] {
        assert!(
            build(Some((case, k))).runner().run().is_err(),
            "a wrong known answer (input {case}, output {k}) must be rejected"
        );
    }
}

mod proving {
    use p3_circuit::ops::{NpoTypeId, Poseidon2PermCall, Poseidon2Trace};
    use p3_circuit::tables::Traces;
    use p3_circuit::{Circuit, CircuitError, NonPrimitiveOpId};
    use p3_circuit_prover::batch_stark_prover::{
        BatchTableInstance, DynamicAirEntry, NonPrimitiveTableEntry, Poseidon2ProverD3,
        TableProver, poseidon2_air_builders_for_configs, recompose_air_builders,
    };
    use p3_circuit_prover::common::NpoPreprocessor;
    use p3_circuit_prover::config::{self, GoldilocksD3W12Config};
    use p3_circuit_prover::{
        BatchStarkProver, BatchStarkProverError, ConstraintProfile, Poseidon2Preprocessor,
        Poseidon2SharedPreprocessor, RecomposePreprocessor, TablePacking,
    };
    use p3_field::extension::BinomialExtensionField;

    use super::*;

    type SC = GoldilocksD3W12Config;

    /// Column of the permutation's first output element in the W12 table: the last `WIDTH`
    /// columns of the permutation block hold the final full round's post-state.
    const FIRST_OUTPUT_COLUMN: usize = p3_poseidon2_air::num_cols::<WIDTH, 7, 1, 4, 22>() - WIDTH;

    /// How the Poseidon2 rows are laid out in tables.
    #[derive(Clone, Copy)]
    enum Tables {
        /// One table per logical config.
        Separate(&'static [Poseidon2Config]),
        /// The challenger and ordinary rows share one physical table.
        Shared,
    }

    // The errors are reported through `Debug` only.
    #[allow(dead_code)]
    #[derive(Debug)]
    enum Rejection {
        Prove(BatchStarkProverError),
        Verify(BatchStarkProverError),
        #[cfg(debug_assertions)]
        DebugPanic,
    }

    /// How the prover materializes the Poseidon2 tables.
    #[derive(Clone, Copy, Debug)]
    enum Materialize {
        /// From the committed preprocessing (`batch_instance_with_committed_preprocessed`), as a
        /// prepared circuit normally does.
        Committed,
        /// From the runtime traces only: the committed path is declined, so the prover falls back
        /// to `TableProver::batch_instance_d3`. A D3 prover that does not implement it yields no
        /// Poseidon2 table, and the proof then cannot contain one.
        Runtime,
    }

    /// Forwards to a D3 Poseidon2 prover. With [`Materialize::Runtime`] it declines the
    /// committed-preprocessing path; with `forge_output` it adds one to the first permutation
    /// output of the first row of the materialized trace, leaving its AIR honest.
    struct TestPoseidon2Prover {
        inner: Poseidon2ProverD3,
        materialize: Materialize,
        forge_output: bool,
    }

    impl TestPoseidon2Prover {
        fn forge(&self, mut instance: BatchTableInstance<SC>) -> BatchTableInstance<SC> {
            if self.forge_output {
                assert!(instance.trace.width > FIRST_OUTPUT_COLUMN);
                instance.trace.values[FIRST_OUTPUT_COLUMN] += F::ONE;
            }
            instance
        }
    }

    impl TableProver<SC> for TestPoseidon2Prover {
        fn op_type(&self) -> NpoTypeId {
            TableProver::<SC>::op_type(&self.inner)
        }

        fn source_op_types(&self) -> Vec<NpoTypeId> {
            TableProver::<SC>::source_op_types(&self.inner)
        }

        fn batch_instance_with_committed_preprocessed(
            &self,
            config: &SC,
            packing: &TablePacking,
            traces: &[(&NpoTypeId, &dyn std::any::Any)],
            committed: &[F],
            circuit_extension_degree: u32,
        ) -> Option<BatchTableInstance<SC>> {
            if matches!(self.materialize, Materialize::Runtime) {
                return None;
            }
            self.inner
                .batch_instance_with_committed_preprocessed(
                    config,
                    packing,
                    traces,
                    committed,
                    circuit_extension_degree,
                )
                .map(|instance| self.forge(instance))
        }

        fn batch_instance_d1(
            &self,
            config: &SC,
            packing: &TablePacking,
            traces: &Traces<F>,
        ) -> Option<BatchTableInstance<SC>> {
            self.inner.batch_instance_d1(config, packing, traces)
        }

        fn batch_instance_d2(
            &self,
            config: &SC,
            packing: &TablePacking,
            traces: &Traces<BinomialExtensionField<F, 2>>,
        ) -> Option<BatchTableInstance<SC>> {
            self.inner.batch_instance_d2(config, packing, traces)
        }

        fn batch_instance_d3(
            &self,
            config: &SC,
            packing: &TablePacking,
            traces: &Traces<EF>,
        ) -> Option<BatchTableInstance<SC>> {
            self.inner
                .batch_instance_d3(config, packing, traces)
                .map(|instance| self.forge(instance))
        }

        fn batch_instance_d4(
            &self,
            config: &SC,
            packing: &TablePacking,
            traces: &Traces<BinomialExtensionField<F, 4>>,
        ) -> Option<BatchTableInstance<SC>> {
            self.inner.batch_instance_d4(config, packing, traces)
        }

        fn batch_instance_d6(
            &self,
            config: &SC,
            packing: &TablePacking,
            traces: &Traces<BinomialExtensionField<F, 6>>,
        ) -> Option<BatchTableInstance<SC>> {
            self.inner.batch_instance_d6(config, packing, traces)
        }

        fn batch_instance_d8(
            &self,
            config: &SC,
            packing: &TablePacking,
            traces: &Traces<BinomialExtensionField<F, 8>>,
        ) -> Option<BatchTableInstance<SC>> {
            self.inner.batch_instance_d8(config, packing, traces)
        }

        fn batch_air_from_table_entry(
            &self,
            config: &SC,
            degree: usize,
            circuit_extension_degree: u32,
            table_entry: &NonPrimitiveTableEntry<SC>,
        ) -> Result<DynamicAirEntry<SC>, String> {
            self.inner.batch_air_from_table_entry(
                config,
                degree,
                circuit_extension_degree,
                table_entry,
            )
        }

        fn air_with_committed_preprocessed(
            &self,
            committed_prep: Vec<F>,
            min_height: usize,
            lanes: usize,
            circuit_extension_degree: u32,
        ) -> Option<DynamicAirEntry<SC>> {
            self.inner.air_with_committed_preprocessed(
                committed_prep,
                min_height,
                lanes,
                circuit_extension_degree,
            )
        }
    }

    /// Prepare `circuit` at `D = 3`, prove `traces` and verify the proof. The Poseidon2 tables
    /// are materialized as `materialize` says; with `forge_output`, the table of that config gets
    /// a forged permutation output (see [`TestPoseidon2Prover`]).
    fn prove_and_verify(
        circuit: &Circuit<EF>,
        traces: &Traces<EF>,
        tables: Tables,
        materialize: Materialize,
        forge_output: Option<Poseidon2Config>,
    ) -> Result<(), Rejection> {
        let shared = [CONFIG.for_shared_challenger_table()];
        let (poseidon_configs, poseidon_preprocessor): (&[_], Box<dyn NpoPreprocessor<F>>) =
            match tables {
                Tables::Separate(configs) => (configs, Box::new(Poseidon2Preprocessor)),
                Tables::Shared => (
                    &shared,
                    Box::new(Poseidon2SharedPreprocessor::new(shared.to_vec())),
                ),
            };
        let preprocessors = vec![
            poseidon_preprocessor,
            Box::new(RecomposePreprocessor::new(true)) as Box<dyn NpoPreprocessor<F>>,
        ];
        let mut air_builders =
            poseidon2_air_builders_for_configs::<SC, D>(poseidon_configs.to_vec());
        air_builders.extend(recompose_air_builders::<SC, D>(1, true));

        let mut prover = BatchStarkProver::new(config::goldilocks_d3_w12())
            .with_table_packing(TablePacking::new(1, 1));
        for &config in poseidon_configs {
            prover.register_table_prover(Box::new(TestPoseidon2Prover {
                inner: Poseidon2ProverD3::new(config, ConstraintProfile::Standard),
                materialize,
                forge_output: forge_output == Some(config),
            }));
        }
        prover.register_recompose_table::<D>(true);
        let prepared = prover
            .prepare_circuit::<EF, D>(
                circuit,
                &preprocessors,
                &air_builders,
                ConstraintProfile::Standard,
            )
            .expect("the D3/W12 circuit prepares");
        let verifier = prepared.verifier();

        let prove = || prepared.prove(traces);
        // Debug builds check every constraint while proving, so a forged trace may stop there.
        #[cfg(debug_assertions)]
        let proof = std::panic::catch_unwind(std::panic::AssertUnwindSafe(prove))
            .map_err(|_| Rejection::DebugPanic)?;
        #[cfg(not(debug_assertions))]
        let proof = prove();
        let proof = proof.map_err(Rejection::Prove)?;
        assert_eq!(proof.ext_degree, D);
        for &config in poseidon_configs {
            let table = NpoTypeId::poseidon2_perm(config);
            if traces
                .non_primitive_trace::<Poseidon2Trace<F>>(&table)
                .is_some()
                || config.is_shared()
            {
                assert!(
                    proof
                        .non_primitives
                        .iter()
                        .any(|entry| entry.op_type == table),
                    "the {} table must be proved ({materialize:?})",
                    config.variant_name()
                );
            }
        }
        verifier.verify(&proof, &[]).map_err(Rejection::Verify)
    }

    /// A forged trace must be rejected. In release the prover does not check constraints, so
    /// the forgery must reach the verifier, which must reject it.
    fn assert_rejected(result: &Result<(), Rejection>, context: &str) {
        #[cfg(not(debug_assertions))]
        assert!(
            matches!(
                result,
                Err(Rejection::Verify(BatchStarkProverError::Verify(_)))
            ),
            "{context}: the forged proof must reach the verifier and be rejected, got {result:?}"
        );
        #[cfg(debug_assertions)]
        assert!(result.is_err(), "{context}: the forgery must be rejected");
    }

    fn run(
        circuit: &Circuit<EF>,
        public_inputs: &[EF],
        private: &[(NonPrimitiveOpId, Vec<EF>)],
    ) -> Result<Traces<EF>, CircuitError> {
        let mut runner = circuit.runner();
        runner.set_public_inputs(public_inputs)?;
        for (op_id, sibling) in private {
            runner.set_private_data(*op_id, perm_private_data(CONFIG, sibling.clone()))?;
        }
        runner.run()
    }

    /// The circuit inputs of one opening: public inputs in allocation order, and each Merkle
    /// row's sibling digest limbs.
    struct Opening {
        public_inputs: Vec<EF>,
        siblings: Vec<(NonPrimitiveOpId, Vec<EF>)>,
    }

    /// Add a `verify_batch_circuit` check of opening `index` of `mats` to `circuit`.
    fn add_mmcs_opening(
        circuit: &mut CircuitBuilder<EF>,
        mats: Vec<RowMajorMatrix<F>>,
        index: usize,
    ) -> Opening {
        let mmcs = native_mmcs();
        let dimensions: Vec<_> = mats.iter().map(Matrix::dimensions).collect();
        let max_height = dimensions.iter().map(|d| d.height).max().unwrap();
        let log_max_height = max_height.next_power_of_two().trailing_zeros() as usize;
        let (commitment, prover_data) = mmcs.commit(mats);
        let opening = mmcs.open_batch(index, &prover_data);

        let opened: Vec<Vec<_>> = opening
            .opened_values
            .iter()
            .map(|row| circuit.alloc_public_inputs(row.len(), "opened row"))
            .collect();
        let directions = circuit.alloc_public_inputs(log_max_height, "directions");
        let cap = vec![circuit.alloc_public_inputs(CONFIG.rate_ext(), "root")];
        let mmcs_ops = verify_batch_circuit::<F, EF>(
            circuit,
            CONFIG,
            &cap,
            &dimensions,
            &directions,
            &opened,
            None,
        )
        .expect("D3/W12 MMCS circuit builds");

        let mut public_inputs: Vec<EF> = opening
            .opened_values
            .iter()
            .flat_map(|row| row.iter().map(|&v| EF::from(v)))
            .collect();
        public_inputs.extend((0..log_max_height).map(|k| EF::from_bool(index >> k & 1 == 1)));
        public_inputs.extend(digest_limbs(&commitment.roots()[0]));
        let siblings: Vec<_> = opening
            .opening_proof
            .iter()
            .map(|digest| digest_limbs(digest))
            .collect();
        assert_eq!(mmcs_ops.len(), siblings.len());
        Opening {
            public_inputs,
            siblings: mmcs_ops.into_iter().zip(siblings).collect(),
        }
    }

    /// Add the known-answer permutation row (a fresh sponge row, every output connected to the
    /// reference output) to `circuit`.
    fn add_known_answer_permutation(circuit: &mut CircuitBuilder<EF>) {
        let input: [F; WIDTH] = core::array::from_fn(|i| F::from_u64(i as u64));
        let expected = default_goldilocks_poseidon2_12().permute(input);
        let limbs: Vec<_> = input
            .chunks(D)
            .map(|c| circuit.define_const(EF::from_basis_coefficients_slice(c).unwrap()))
            .collect();
        let (_, outputs) = circuit
            .add_poseidon2_perm(&Poseidon2PermCall {
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
    }

    /// Add a challenger transcript checked against the native `DuplexChallenger` (observe,
    /// extension observe, `sample`, `sample_ext`, `sample_bits` and a PoW check) to `circuit`.
    /// Returns the PoW witness, the transcript's only public input.
    fn add_challenger_transcript(circuit: &mut CircuitBuilder<EF>, seed: u64) -> EF {
        let mut rng = SmallRng::seed_from_u64(seed);
        let mut native =
            DuplexChallenger::<F, Perm, WIDTH, RATE>::new(default_goldilocks_poseidon2_12());
        let mut cc = CircuitChallenger::<WIDTH, RATE, Poseidon2Config>::new_goldilocks_d3();
        let expect = |circuit: &mut CircuitBuilder<EF>, got, value: EF| {
            let expected = circuit.define_const(value);
            circuit.connect(got, expected);
        };

        for _ in 0..RATE + 2 {
            let v: F = rng.random();
            native.observe(v);
            let t = circuit.define_const(EF::from(v));
            RecursiveChallenger::<F, EF>::observe(&mut cc, circuit, t);
        }
        for _ in 0..3 {
            let s: F = native.sample();
            let cs = RecursiveChallenger::<F, EF>::sample(&mut cc, circuit);
            expect(circuit, cs, EF::from(s));
        }
        for _ in 0..2 {
            let v: EF = rng.random();
            native.observe_algebra_element(v);
            let t = circuit.define_const(v);
            RecursiveChallenger::<F, EF>::observe_ext(&mut cc, circuit, t);
        }
        let s: EF = native.sample_algebra_element();
        let cs = RecursiveChallenger::<F, EF>::sample_ext(&mut cc, circuit);
        expect(circuit, cs, s);
        let native_bits: usize = native.sample_bits(20);
        let bits = RecursiveChallenger::<F, EF>::sample_bits(&mut cc, circuit, 20)
            .expect("sample_bits builds");
        for (k, &bit) in bits.iter().enumerate() {
            expect(circuit, bit, EF::from_bool(native_bits >> k & 1 == 1));
        }

        let pow_bits = 4;
        let witness = native.clone().grind(pow_bits);
        assert!(native.check_witness(pow_bits, witness));
        let witness_target = circuit.alloc_public_input("pow witness");
        RecursiveChallenger::<F, EF>::check_pow_witness(&mut cc, circuit, pow_bits, witness_target)
            .expect("check_pow_witness builds");
        let s: EF = native.sample_algebra_element();
        let cs = RecursiveChallenger::<F, EF>::sample_ext(&mut cc, circuit);
        expect(circuit, cs, s);
        EF::from(witness)
    }

    /// Opening index 2 of an 8x7 matrix plus a 4x3 one injected one level up: two-row leaf
    /// sponges (7 = 6 + 1 elements) and Merkle rows with the running digest on the left
    /// (levels 0 and 2) and on the right (level 1).
    fn mmcs_matrices() -> Vec<RowMajorMatrix<F>> {
        let mut rng = SmallRng::seed_from_u64(0xD3_10);
        let mut matrix = |height: usize, width: usize| {
            RowMajorMatrix::new((0..height * width).map(|_| rng.random()).collect(), width)
        };
        vec![matrix(8, 7), matrix(4, 3)]
    }
    const MMCS_INDEX: usize = 2;

    /// The plain permutation, the leaf sponge and Merkle compression rows in both directions,
    /// proved at D3 and verified, with the table materialized both from the committed
    /// preprocessing and from `batch_instance_d3`. A forged permutation output (on either path)
    /// and a forged Merkle sibling are rejected by the verifier.
    #[test]
    fn permutation_sponge_and_merkle_rows_prove_and_verify() {
        let mut circuit = setup_circuit();
        add_known_answer_permutation(&mut circuit);
        let opening = add_mmcs_opening(&mut circuit, mmcs_matrices(), MMCS_INDEX);
        let circuit = circuit.build().expect("D3/W12 circuit compiles");
        let tables = Tables::Separate(&[CONFIG]);

        let traces =
            run(&circuit, &opening.public_inputs, &opening.siblings).expect("honest opening runs");
        let rows = &traces
            .non_primitive_trace::<Poseidon2Trace<F>>(&NpoTypeId::poseidon2_perm(CONFIG))
            .unwrap()
            .operations;
        let merkle_rows: Vec<_> = rows.iter().filter(|row| row.merkle_path).collect();
        // Three sibling compressions, plus one injecting the shorter matrix's leaf digest.
        assert_eq!(merkle_rows.len(), 4);
        assert!(merkle_rows.iter().any(|row| row.mmcs_bit));
        assert!(merkle_rows.iter().any(|row| !row.mmcs_bit));
        assert!(rows.iter().any(|row| !row.merkle_path && !row.new_start));
        // Without committed preprocessing, the table comes from `batch_instance_d3`.
        let instance = Poseidon2ProverD3::new(CONFIG, ConstraintProfile::Standard)
            .batch_instance_d3(
                &config::goldilocks_d3_w12(),
                &TablePacking::new(1, 1),
                &traces,
            )
            .expect("D3 traces materialize the W12 table");
        assert_eq!(instance.op_type, NpoTypeId::poseidon2_perm(CONFIG));
        assert_eq!(instance.rows, rows.len().next_power_of_two());
        for materialize in [Materialize::Committed, Materialize::Runtime] {
            prove_and_verify(&circuit, &traces, tables, materialize, None).unwrap_or_else(|e| {
                panic!("honest D3/W12 proof verifies ({materialize:?}): {e:?}")
            });

            // The first row is the known-answer permutation: change its first output in the trace.
            assert_rejected(
                &prove_and_verify(&circuit, &traces, tables, materialize, Some(CONFIG)),
                &format!("forged permutation output ({materialize:?})"),
            );
        }

        // A wrong sibling makes the root check fail when the circuit runs.
        let mut wrong = opening.siblings.clone();
        wrong[1].1[0] += EF::ONE;
        assert!(run(&circuit, &opening.public_inputs, &wrong).is_err());

        // A prover that skips execution and writes the wrong sibling into its Merkle row.
        let table = NpoTypeId::poseidon2_perm(CONFIG);
        let mut forged = traces
            .non_primitive_trace::<Poseidon2Trace<F>>(&table)
            .unwrap()
            .clone();
        let sibling: Vec<F> = opening.siblings[1]
            .1
            .iter()
            .flat_map(|limb| limb.as_basis_coefficients_slice().to_vec())
            .collect();
        let (row, start) = forged
            .operations
            .iter_mut()
            .filter(|row| row.merkle_path)
            .find_map(|row| {
                let start = (0..=WIDTH - DIGEST)
                    .step_by(D)
                    .find(|&start| row.input_values[start..start + DIGEST] == sibling[..])?;
                Some((row, start))
            })
            .expect("a Merkle row holds the sibling digest");
        row.input_values[start] += F::ONE;
        let mut forged_traces = run(&circuit, &opening.public_inputs, &opening.siblings).unwrap();
        forged_traces
            .non_primitive_traces
            .insert(table, Box::new(forged));
        assert_rejected(
            &prove_and_verify(
                &circuit,
                &forged_traces,
                tables,
                Materialize::Committed,
                None,
            ),
            "forged Merkle sibling",
        );
    }

    /// Challenger rows live in the `goldilocks_d3_w12_challenger` table; proved next to the
    /// ordinary table and verified. A forged challenger output is rejected.
    #[test]
    fn challenger_table_proves_and_verifies() {
        let mut circuit = setup_circuit();
        let witness = add_challenger_transcript(&mut circuit, 0xD3_11);
        add_known_answer_permutation(&mut circuit);
        let circuit = circuit.build().expect("challenger circuit compiles");
        let traces = run(&circuit, &[witness], &[]).expect("honest transcript runs");
        assert!(
            traces
                .non_primitive_trace::<Poseidon2Trace<F>>(&NpoTypeId::poseidon2_perm(
                    CONFIG.for_challenger()
                ))
                .is_some_and(|trace| trace.operations.len() > 2)
        );
        const CONFIGS: &[Poseidon2Config] = &[CONFIG.for_challenger(), CONFIG];
        let tables = Tables::Separate(CONFIGS);
        for materialize in [Materialize::Committed, Materialize::Runtime] {
            prove_and_verify(&circuit, &traces, tables, materialize, None).unwrap_or_else(|e| {
                panic!("honest D3/W12 challenger proof verifies ({materialize:?}): {e:?}")
            });
        }
        assert_rejected(
            &prove_and_verify(
                &circuit,
                &traces,
                tables,
                Materialize::Committed,
                Some(CONFIG.for_challenger()),
            ),
            "forged challenger output",
        );
    }

    /// Challenger, plain permutation, sponge and Merkle rows in the one shared table, on both
    /// materialization paths, plus a forged output on each.
    #[test]
    fn shared_challenger_table_proves_and_verifies() {
        let mut circuit = setup_circuit();
        let witness = add_challenger_transcript(&mut circuit, 0xD3_12);
        add_known_answer_permutation(&mut circuit);
        let opening = add_mmcs_opening(&mut circuit, mmcs_matrices(), MMCS_INDEX);
        let circuit = circuit.build().expect("shared circuit compiles");
        let mut public_inputs = vec![witness];
        public_inputs.extend(&opening.public_inputs);
        let traces = run(&circuit, &public_inputs, &opening.siblings).expect("honest run");
        for materialize in [Materialize::Committed, Materialize::Runtime] {
            prove_and_verify(&circuit, &traces, Tables::Shared, materialize, None).unwrap_or_else(
                |e| panic!("honest D3/W12 shared-table proof verifies ({materialize:?}): {e:?}"),
            );
            assert_rejected(
                &prove_and_verify(
                    &circuit,
                    &traces,
                    Tables::Shared,
                    materialize,
                    Some(CONFIG.for_shared_challenger_table()),
                ),
                &format!("forged shared-table output ({materialize:?})"),
            );
        }
    }
}
