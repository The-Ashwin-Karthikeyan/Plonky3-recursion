//! Regression test: MMCS leaf packing binds each base coefficient.
//!
//! `verify_batch_circuit` and `verify_batch_circuit_arity4` pack a Merkle leaf's opened base
//! coefficients, and a hiding MMCS's salt, into extension limbs before absorbing them. Whenever the
//! permutation absorbs extension limbs (`d() == EF::DIMENSION > 1`), the packing goes through the
//! coefficient-bound `recompose/coeff` table, which publishes every coefficient on the
//! `WitnessChecks` bus as a base-field element.
//!
//! Each case commits one honest row natively, verifies it in-circuit, and checks:
//!
//! - every opened value (and salt) is an input of a `recompose/coeff` row and is read by no ALU
//!   row other than the downstream consumer the fixture adds;
//! - the honest witness executes, proves and verifies;
//! - a witness that changes two opened coefficients of one limb while keeping that limb's value
//!   (`c_j += t·X`, `c_{j+1} -= t`) is rejected by the circuit runner, and a trace in which only
//!   the downstream consumer reads those changed values is rejected by the verifier. The consumer
//!   (an ALU product per opened value) stands in for the FRI reduction, which reads the same
//!   opened-value targets.
//!
//! Covered: Goldilocks D2 with Poseidon2 width 8 (binary, salted) and width 16 (arity 4), and
//! Goldilocks D3 with Poseidon2 width 12 (binary, salted).

#[path = "common/goldilocks_d3_config.rs"]
mod goldilocks_d3_config;
#[path = "common/rejection_oracle.rs"]
#[allow(clippy::duplicate_mod)]
mod rejection_oracle;

use goldilocks_d3_config::{
    Compress as Compress12, Hash as Hash12, PERM as D3_W12, Perm as Perm12,
};
use p3_circuit::ops::{
    AluOpKind, GoldilocksD2Width8, GoldilocksD3Width12, NpoTypeId, Op, Poseidon2Config,
    generate_poseidon2_trace, generate_recompose_trace,
};
use p3_circuit::{Circuit, CircuitBuilder, CircuitError, Traces, WitnessId};
use p3_circuit_prover::batch_stark_prover::{
    poseidon2_air_builders_for_configs, recompose_air_builders,
};
use p3_circuit_prover::common::NpoPreprocessor;
use p3_circuit_prover::config::{GoldilocksConfig, GoldilocksD3W12Config};
use p3_circuit_prover::{
    BatchStarkProver, ConstraintProfile, Poseidon2Preprocessor, RecomposePreprocessor,
    TablePacking, config,
};
use p3_commit::{BatchOpeningRef, Mmcs};
use p3_field::extension::{BinomialExtensionField, CubicTrinomialExtensionField};
use p3_field::{BasedVectorSpace, ExtensionField, Field, PrimeCharacteristicRing};
use p3_goldilocks::{Goldilocks, Poseidon2Goldilocks, default_goldilocks_poseidon2_12};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::{MerkleTreeHidingMmcs, MerkleTreeMmcs};
use p3_poseidon2_circuit_air::GoldilocksD2Width16;
use p3_recursion::Target;
use p3_recursion::builtin_config::{fixed_goldilocks_poseidon2_8, fixed_goldilocks_poseidon2_16};
use p3_recursion::pcs::{verify_batch_circuit, verify_batch_circuit_arity4};
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use rand::SeedableRng;
use rand::rngs::StdRng;
#[cfg(debug_assertions)]
use rejection_oracle::run_with_debug_oracle;
use rejection_oracle::{ProofCheckError, assert_rejected};

type F = Goldilocks;
type EF2 = BinomialExtensionField<F, 2>;
type EF3 = CubicTrinomialExtensionField<F>;

type Perm8 = Poseidon2Goldilocks<8>;
type Hash8 = PaddingFreeSponge<Perm8, 8, 4, 4>;
type Compress8 = TruncatedPermutation<Perm8, 2, 4, 8>;
type BinaryMmcs8 = MerkleTreeMmcs<F, F, Hash8, Compress8, 2, 4>;
type HidingMmcs8 = MerkleTreeHidingMmcs<F, F, Hash8, Compress8, StdRng, 2, 4, SALT_ELEMS>;

type Perm16 = Poseidon2Goldilocks<16>;
type Hash16 = PaddingFreeSponge<Perm16, 16, 12, 4>;
type Compress16 = TruncatedPermutation<Perm16, 4, 4, 16>;
type Arity4Mmcs16 = MerkleTreeMmcs<F, F, Hash16, Compress16, 4, 4>;

type BinaryMmcs12 = MerkleTreeMmcs<F, F, Hash12, Compress12, 2, 6>;
type HidingMmcs12 = MerkleTreeHidingMmcs<F, F, Hash12, Compress12, StdRng, 2, 6, SALT_ELEMS>;

const D2_W8: Poseidon2Config = Poseidon2Config::GOLDILOCKS_D2_W8;
const D2_W16: Poseidon2Config = Poseidon2Config::GOLDILOCKS_D2_W16;
const SALT_ELEMS: usize = 4;

/// An opened row and its circuit, with the witness ids of the opened values and salts.
struct Fixture<EF> {
    circuit: Circuit<EF>,
    public_inputs: Vec<EF>,
    private_inputs: Vec<EF>,
    /// Witness ids of `private_inputs`, in order: the opened row, then the salt.
    private_wids: Vec<WitnessId>,
}

/// The basis element `X`.
fn gen_x<EF: ExtensionField<F>>() -> EF {
    EF::from_basis_coefficients_fn(|i| if i == 1 { F::ONE } else { F::ZERO })
}

/// `sum(c_i · X^i)` over one limb of `D` coefficients.
fn limb_value<EF: ExtensionField<F>>(coeffs: &[EF]) -> EF {
    coeffs
        .iter()
        .rev()
        .fold(EF::ZERO, |acc, &c| acc * gen_x::<EF>() + c)
}

/// Change coefficients `j` and `j + 1` of `values` without changing the value of the limb that
/// holds them: `c_j += t·X`, `c_{j+1} -= t`.
fn move_within_limb<EF: ExtensionField<F>>(values: &[EF], j: usize, t: EF) -> Vec<EF> {
    let d = <EF as BasedVectorSpace<F>>::DIMENSION;
    assert!(j % d + 1 < d, "both coefficients lie in one limb");
    let mut moved = values.to_vec();
    moved[j] += t * gen_x::<EF>();
    moved[j + 1] -= t;
    let limb = j - j % d..j - j % d + d;
    assert_ne!(moved, values);
    assert_eq!(
        limb_value(&moved[limb.clone()]),
        limb_value(&values[limb]),
        "the move keeps the packed limb"
    );
    moved
}

fn shifts<EF: ExtensionField<F>>() -> [EF; 2] {
    [
        EF::from_u64(12345),
        EF::from_u64(77) + EF::from_u64(999) * gen_x::<EF>(),
    ]
}

/// Allocate the cap (public), the opened row and salt (private) and a public `alpha`, run
/// `verify`, then add one ALU product `v · alpha` per opened value as its downstream consumer.
fn build_fixture<EF, V>(
    mut builder: CircuitBuilder<EF>,
    roots: &[Vec<F>],
    digest_elems: usize,
    row: &[F],
    salt: &[F],
    verify: V,
) -> Fixture<EF>
where
    EF: ExtensionField<F>,
    V: FnOnce(&mut CircuitBuilder<EF>, &[Vec<Target>], &[Target], Option<&[Vec<Target>]>),
{
    let d = <EF as BasedVectorSpace<F>>::DIMENSION;
    let cap: Vec<Vec<Target>> = roots
        .iter()
        .map(|root| {
            assert_eq!(root.len(), digest_elems);
            builder.alloc_public_inputs(root.len() / d, "cap")
        })
        .collect();
    let alpha = builder.public_input();
    let opened = builder.alloc_private_inputs(row.len(), "opened row");
    let salts = (!salt.is_empty()).then(|| vec![builder.alloc_private_inputs(salt.len(), "salt")]);
    verify(&mut builder, &cap, &opened, salts.as_deref());
    for &value in &opened {
        builder.mul(value, alpha);
    }
    let circuit = builder.build().expect("leaf circuit builds");

    let mut public_inputs: Vec<EF> = roots
        .iter()
        .flat_map(|root| {
            root.chunks(d)
                .map(|c| EF::from_basis_coefficients_slice(c).unwrap())
        })
        .collect();
    public_inputs.push(EF::from_u64(3) + EF::from_u64(5) * gen_x::<EF>());
    let private_inputs: Vec<EF> = row.iter().chain(salt).copied().map(EF::from).collect();
    let private_wids = circuit.private_input_rows.clone();
    assert_eq!(private_wids.len(), private_inputs.len());
    Fixture {
        circuit,
        public_inputs,
        private_inputs,
        private_wids,
    }
}

impl<EF: Field> Fixture<EF> {
    fn run(&self, private_inputs: &[EF]) -> Result<Traces<EF>, CircuitError> {
        let mut runner = self.circuit.runner();
        runner.set_public_inputs(&self.public_inputs)?;
        runner.set_private_inputs(private_inputs)?;
        runner.run()
    }
}

/// Every witness in `wids` (opened values, salt coefficients) is an input of a `recompose/coeff`
/// row, and is read by exactly `consumers` ALU rows (the fixture's downstream consumer).
fn assert_coefficient_bound_packing<EF: Field>(
    circuit: &Circuit<EF>,
    wids: &[WitnessId],
    consumers: usize,
) {
    for &wid in wids {
        let coeff_rows = circuit
            .ops
            .iter()
            .filter(|op| match op {
                Op::NonPrimitiveOpWithExecutor {
                    executor, inputs, ..
                } => {
                    *executor.op_type() == NpoTypeId::recompose_with_coeff_lookups()
                        && inputs.iter().flatten().any(|&input| input == wid)
                }
                _ => false,
            })
            .count();
        assert!(
            coeff_rows > 0,
            "{wid:?} is packed by a coefficient-bound recompose row"
        );
        let alu_reads = circuit
            .ops
            .iter()
            .filter(|op| {
                matches!(op, Op::Alu { a, b, c, .. }
                if *a == wid || *b == wid || c.is_some_and(|c| c == wid))
            })
            .count();
        assert_eq!(
            alu_reads, consumers,
            "{wid:?} is read by the ALU only through the fixture's consumer"
        );
    }
}

/// The honest trace, with the ALU rows that read the given witnesses changed to read `value`
/// instead (their outputs recomputed). Every hash and packing row keeps its honest values.
fn with_consumer_reads<EF: Field>(honest: &Traces<EF>, changed: &[(WitnessId, EF)]) -> Traces<EF> {
    let mut traces = honest.clone();
    let alu = &mut traces.alu_trace;
    for &(wid, value) in changed {
        let mut rows = 0;
        for row in 0..alu.indices.len() {
            for operand in 0..3 {
                if alu.indices[row][operand] == wid {
                    alu.values[row][operand] = value;
                    let [a, b, c, _] = alu.values[row];
                    alu.values[row][3] = match alu.op_kind[row] {
                        AluOpKind::Add => a + b,
                        AluOpKind::Mul => a * b,
                        AluOpKind::MulAdd => a * b + c,
                        kind => panic!("unexpected consumer kind {kind:?}"),
                    };
                    rows += 1;
                }
            }
        }
        assert_eq!(rows, 1, "exactly the consumer row reads {wid:?}");
    }
    traces
}

/// Prove `traces` against the honest `circuit`'s fixed key and verify, for one Goldilocks
/// configuration: `$sc` with challenge field `$ef` of degree `$d`.
macro_rules! prove_and_verify_fn {
    ($name:ident, $sc:ty, $ef:ty, $d:literal, $config:expr) => {
        fn $name(
            circuit: &Circuit<$ef>,
            traces: &Traces<$ef>,
            perm: Poseidon2Config,
        ) -> Result<(), ProofCheckError> {
            let npo_preprocessors: Vec<Box<dyn NpoPreprocessor<F>>> = vec![
                Box::new(Poseidon2Preprocessor),
                Box::new(RecomposePreprocessor::new(true)),
            ];
            let mut air_builders = poseidon2_air_builders_for_configs::<$sc, $d>(vec![perm]);
            air_builders.extend(recompose_air_builders::<$sc, $d>(1, true));
            let mut prover =
                BatchStarkProver::new($config).with_table_packing(TablePacking::new(1, 1));
            prover.register_poseidon2_table::<$d>(perm);
            prover.register_recompose_table::<$d>(true);
            let prepared = prover
                .prepare_circuit::<$ef, $d>(
                    circuit,
                    &npo_preprocessors,
                    &air_builders,
                    ConstraintProfile::Standard,
                )
                .expect("fixed-key circuit preparation");
            let verifier = prepared.verifier();

            #[cfg(debug_assertions)]
            let result = run_with_debug_oracle(|| {
                let proof = prepared.prove(traces).map_err(ProofCheckError::Prove)?;
                verifier
                    .verify(&proof, &[])
                    .map_err(ProofCheckError::Verify)
            });

            #[cfg(not(debug_assertions))]
            let result = {
                let proof = prepared.prove(traces).map_err(ProofCheckError::Prove)?;
                verifier
                    .verify(&proof, &[])
                    .map_err(ProofCheckError::Verify)
            };

            #[cfg(debug_assertions)]
            return match result {
                Ok(result) => result,
                Err(kind) => Err(ProofCheckError::DebugPanic(kind)),
            };

            #[cfg(not(debug_assertions))]
            result
        }
    };
}

prove_and_verify_fn!(
    prove_and_verify_d2,
    GoldilocksConfig,
    EF2,
    2,
    config::goldilocks()
);
prove_and_verify_fn!(
    prove_and_verify_d3,
    GoldilocksD3W12Config,
    EF3,
    3,
    config::goldilocks_d3_w12()
);

type ProveAndVerify<EF> =
    fn(&Circuit<EF>, &Traces<EF>, Poseidon2Config) -> Result<(), ProofCheckError>;

/// The honest row proves; each limb-preserving move of two coefficients `(j, j + 1)`, `j` in
/// `pairs`, is rejected by the runner and, as a consumer-only change, by the verifier.
fn check_moves<EF: ExtensionField<F>>(
    fx: &Fixture<EF>,
    prove_and_verify: ProveAndVerify<EF>,
    perm: Poseidon2Config,
    pairs: &[usize],
) {
    let honest = fx.run(&fx.private_inputs).expect("honest leaf executes");
    prove_and_verify(&fx.circuit, &honest, perm)
        .unwrap_or_else(|e| panic!("honest leaf must prove and verify: {e}"));

    // Control for the trace edit below: rewriting the consumer rows with their honest values
    // still proves and verifies.
    let unchanged: Vec<(WitnessId, EF)> = (0..fx.private_inputs.len())
        .filter(|&k| has_consumer(fx, k))
        .map(|k| (fx.private_wids[k], fx.private_inputs[k]))
        .collect();
    prove_and_verify(&fx.circuit, &with_consumer_reads(&honest, &unchanged), perm)
        .unwrap_or_else(|e| panic!("the unchanged consumer edit must prove and verify: {e}"));

    for t in shifts::<EF>() {
        for &j in pairs {
            let moved = move_within_limb(&fx.private_inputs, j, t);
            assert!(
                fx.run(&moved).is_err(),
                "moving coefficients {j}, {} must fail execution",
                j + 1
            );
            let changed: Vec<(WitnessId, EF)> = [j, j + 1]
                .into_iter()
                .filter(|&k| has_consumer(fx, k))
                .map(|k| (fx.private_wids[k], moved[k]))
                .collect();
            assert!(!changed.is_empty());
            let edited = with_consumer_reads(&honest, &changed);
            assert_rejected(
                &prove_and_verify(&fx.circuit, &edited, perm),
                "a consumer reading opened values that differ from the packed coefficients",
            );
        }
    }
}

fn has_consumer<EF: Field>(fx: &Fixture<EF>, k: usize) -> bool {
    let wid = fx.private_wids[k];
    fx.circuit
        .ops
        .iter()
        .any(|op| matches!(op, Op::Alu { a, .. } if *a == wid))
}

fn d2_w8_builder() -> CircuitBuilder<EF2> {
    let mut builder = CircuitBuilder::<EF2>::new();
    builder.enable_poseidon2_perm_width_8::<GoldilocksD2Width8, _>(
        generate_poseidon2_trace::<EF2, GoldilocksD2Width8>,
        fixed_goldilocks_poseidon2_8(),
    );
    builder.enable_recompose::<F>(generate_recompose_trace::<F, EF2>);
    builder
}

fn binary_mmcs8() -> BinaryMmcs8 {
    let perm = fixed_goldilocks_poseidon2_8();
    BinaryMmcs8::new(Hash8::new(perm.clone()), Compress8::new(perm), 0)
}

fn one_row(width: usize) -> Vec<F> {
    (0..width as u64).map(|i| F::from_u64(100 + i)).collect()
}

#[test]
fn goldilocks_d2_binary_leaf_binds_each_base_coefficient() {
    let row = one_row(4);
    let mmcs = binary_mmcs8();
    let matrix = RowMajorMatrix::new(row.clone(), row.len());
    let dims = [matrix.dimensions()];
    let (commitment, prover_data) = mmcs.commit(vec![matrix]);
    let opening = mmcs.open_batch(0, &prover_data);
    mmcs.verify_batch(
        &commitment,
        &dims,
        0,
        BatchOpeningRef::new(&opening.opened_values, &opening.opening_proof),
    )
    .expect("native opening verifies");
    let roots: Vec<Vec<F>> = commitment.roots().iter().map(|r| r.to_vec()).collect();

    let fx = build_fixture(
        d2_w8_builder(),
        &roots,
        4,
        &row,
        &[],
        |b, cap, opened, salts| {
            verify_batch_circuit::<F, EF2>(b, D2_W8, cap, &dims, &[], &[opened.to_vec()], salts)
                .expect("verify_batch_circuit builds");
        },
    );
    assert_coefficient_bound_packing(&fx.circuit, &fx.private_wids, 1);
    check_moves(&fx, prove_and_verify_d2, D2_W8, &[0, 2]);
}

#[test]
fn goldilocks_d2_salted_leaf_binds_each_base_coefficient() {
    // Width 3 puts the last opened value and the first salt coefficient in one limb.
    let row = one_row(3);
    let perm = fixed_goldilocks_poseidon2_8();
    let mmcs = HidingMmcs8::new(
        Hash8::new(perm.clone()),
        Compress8::new(perm),
        0,
        StdRng::seed_from_u64(7),
    );
    let matrix = RowMajorMatrix::new(row.clone(), row.len());
    let dims = [matrix.dimensions()];
    let (commitment, prover_data) = mmcs.commit(vec![matrix]);
    let opening = mmcs.open_batch(0, &prover_data);
    mmcs.verify_batch(
        &commitment,
        &dims,
        0,
        BatchOpeningRef::new(&opening.opened_values, &opening.opening_proof),
    )
    .expect("native salted opening verifies");
    let salt: Vec<F> = opening.opening_proof.0[0].to_vec();
    assert_eq!(salt.len(), SALT_ELEMS);
    let roots: Vec<Vec<F>> = commitment.roots().iter().map(|r| r.to_vec()).collect();

    let fx = build_fixture(
        d2_w8_builder(),
        &roots,
        4,
        &row,
        &salt,
        |b, cap, opened, salts| {
            verify_batch_circuit::<F, EF2>(b, D2_W8, cap, &dims, &[], &[opened.to_vec()], salts)
                .expect("salted verify_batch_circuit builds");
        },
    );
    // Opened values have one consumer each; salt coefficients have none.
    let (opened_wids, salt_wids) = fx.private_wids.split_at(row.len());
    assert_coefficient_bound_packing(&fx.circuit, opened_wids, 1);
    assert_coefficient_bound_packing(&fx.circuit, salt_wids, 0);

    // (0, 1): two opened values; (2, 3): the last opened value and the first salt coefficient.
    check_moves(&fx, prove_and_verify_d2, D2_W8, &[0, 2]);
}

#[test]
fn goldilocks_d2_arity4_leaf_binds_each_base_coefficient() {
    let row = one_row(4);
    let perm = fixed_goldilocks_poseidon2_16();
    let mmcs = Arity4Mmcs16::new(Hash16::new(perm.clone()), Compress16::new(perm), 0);
    let matrix = RowMajorMatrix::new(row.clone(), row.len());
    let dims = [matrix.dimensions()];
    let (commitment, prover_data) = mmcs.commit(vec![matrix]);
    let opening = mmcs.open_batch(0, &prover_data);
    mmcs.verify_batch(
        &commitment,
        &dims,
        0,
        BatchOpeningRef::new(&opening.opened_values, &opening.opening_proof),
    )
    .expect("native arity-4 opening verifies");
    let roots: Vec<Vec<F>> = commitment.roots().iter().map(|r| r.to_vec()).collect();

    let mut builder = CircuitBuilder::<EF2>::new();
    builder.enable_poseidon2_perm::<GoldilocksD2Width16, _>(
        generate_poseidon2_trace::<EF2, GoldilocksD2Width16>,
        fixed_goldilocks_poseidon2_16(),
    );
    builder.enable_recompose::<F>(generate_recompose_trace::<F, EF2>);
    let fx = build_fixture(builder, &roots, 4, &row, &[], |b, cap, opened, _| {
        verify_batch_circuit_arity4::<F, EF2>(b, D2_W16, cap, &dims, &[], &[opened.to_vec()])
            .expect("verify_batch_circuit_arity4 builds");
    });
    assert_coefficient_bound_packing(&fx.circuit, &fx.private_wids, 1);
    check_moves(&fx, prove_and_verify_d2, D2_W16, &[0, 2]);
}

fn d3_w12_builder() -> CircuitBuilder<EF3> {
    let mut builder = CircuitBuilder::<EF3>::new();
    builder.enable_poseidon2_perm_width_12::<GoldilocksD3Width12, _>(
        generate_poseidon2_trace::<EF3, GoldilocksD3Width12>,
        default_goldilocks_poseidon2_12(),
    );
    builder.enable_recompose::<F>(generate_recompose_trace::<F, EF3>);
    builder
}

#[test]
fn goldilocks_d3_binary_leaf_binds_each_base_coefficient() {
    let row = one_row(6);
    let perm: Perm12 = default_goldilocks_poseidon2_12();
    let mmcs = BinaryMmcs12::new(Hash12::new(perm.clone()), Compress12::new(perm), 0);
    let matrix = RowMajorMatrix::new(row.clone(), row.len());
    let dims = [matrix.dimensions()];
    let (commitment, prover_data) = mmcs.commit(vec![matrix]);
    let opening = mmcs.open_batch(0, &prover_data);
    mmcs.verify_batch(
        &commitment,
        &dims,
        0,
        BatchOpeningRef::new(&opening.opened_values, &opening.opening_proof),
    )
    .expect("native D3 opening verifies");
    let roots: Vec<Vec<F>> = commitment.roots().iter().map(|r| r.to_vec()).collect();

    let fx = build_fixture(
        d3_w12_builder(),
        &roots,
        6,
        &row,
        &[],
        |b, cap, opened, salts| {
            verify_batch_circuit::<F, EF3>(b, D3_W12, cap, &dims, &[], &[opened.to_vec()], salts)
                .expect("D3 verify_batch_circuit builds");
        },
    );
    assert_coefficient_bound_packing(&fx.circuit, &fx.private_wids, 1);
    // (0, 1) and (1, 2) in the first cubic limb, (3, 4) in the second.
    check_moves(&fx, prove_and_verify_d3, D3_W12, &[0, 1, 3]);
}

#[test]
fn goldilocks_d3_salted_leaf_binds_each_base_coefficient() {
    // Width 5 puts the last two opened values and the first salt coefficient in one limb.
    let row = one_row(5);
    let perm: Perm12 = default_goldilocks_poseidon2_12();
    let mmcs = HidingMmcs12::new(
        Hash12::new(perm.clone()),
        Compress12::new(perm),
        0,
        StdRng::seed_from_u64(7),
    );
    let matrix = RowMajorMatrix::new(row.clone(), row.len());
    let dims = [matrix.dimensions()];
    let (commitment, prover_data) = mmcs.commit(vec![matrix]);
    let opening = mmcs.open_batch(0, &prover_data);
    mmcs.verify_batch(
        &commitment,
        &dims,
        0,
        BatchOpeningRef::new(&opening.opened_values, &opening.opening_proof),
    )
    .expect("native salted D3 opening verifies");
    let salt: Vec<F> = opening.opening_proof.0[0].to_vec();
    assert_eq!(salt.len(), SALT_ELEMS);
    let roots: Vec<Vec<F>> = commitment.roots().iter().map(|r| r.to_vec()).collect();

    let fx = build_fixture(
        d3_w12_builder(),
        &roots,
        6,
        &row,
        &salt,
        |b, cap, opened, salts| {
            verify_batch_circuit::<F, EF3>(b, D3_W12, cap, &dims, &[], &[opened.to_vec()], salts)
                .expect("salted D3 verify_batch_circuit builds");
        },
    );
    let (opened_wids, salt_wids) = fx.private_wids.split_at(row.len());
    assert_coefficient_bound_packing(&fx.circuit, opened_wids, 1);
    assert_coefficient_bound_packing(&fx.circuit, salt_wids, 0);

    // (0, 1): two opened values; (4, 5): the last opened value and the first salt coefficient.
    check_moves(&fx, prove_and_verify_d3, D3_W12, &[0, 4]);
}
