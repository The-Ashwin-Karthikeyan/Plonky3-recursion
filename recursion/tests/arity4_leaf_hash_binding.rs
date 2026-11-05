//! Bus-binding regression for the arity-4 (4-to-1, W32) MMCS leaf-hash absorb.
//!
//! `verify_batch_circuit_arity4` packs each leaf's opened base-field coefficients into extension
//! limbs before absorbing them into the wide sponge, via the same `add_hash_base_coeffs_overwrite`
//! helper `verify_batch_circuit` uses and under the same policy: a permutation that absorbs
//! extension limbs (`d() == EF::DIMENSION > 1`) packs them with the `recompose/coeff` table. That
//! table publishes each coefficient on the `WitnessChecks` bus as a base-field element and records
//! the coefficient witness ids in its preprocessed columns, so the limb is tied to the
//! coefficients and re-pointing a packing row at another coefficient is visible to the verifier.
//! The plain recompose table publishes only its output limb and is never used for leaves.
//!
//! Both tests build the leaf hash with the recompose NPO table *enabled*, so the plain table
//! would be available to the lowering.

use p3_circuit::ops::{Op, Poseidon2Config, generate_poseidon2_trace, generate_recompose_trace};
use p3_circuit::{Circuit, CircuitBuilder, WitnessId};
use p3_field::extension::BinomialExtensionField;
use p3_koala_bear::{KoalaBear, default_koalabear_poseidon2_32};
use p3_matrix::Dimensions;
use p3_poseidon2_circuit_air::KoalaBearD4Width32;
use p3_recursion::Target;
use p3_recursion::pcs::verify_batch_circuit_arity4;

type F = KoalaBear;
type EF = BinomialExtensionField<F, 4>;

const D: usize = 4;
const CFG: Poseidon2Config = Poseidon2Config::KOALA_BEAR_D4_W32;
/// Single-matrix leaf whose rows round up to height 512: matches the schedule already exercised
/// end-to-end by `arity4_mmcs_bus_balance.rs::arity4_bus_balance_bridge_only`.
const LEAF_HEIGHT: usize = 512;
const LOG_MAX_HEIGHT: usize = 9;
/// Leaf width in base-field coefficients: two full extension limbs, no partial-chunk mixing.
const LEAF_WIDTH: usize = 8;

/// A single-matrix `verify_batch_circuit_arity4` circuit over a leaf of `LEAF_WIDTH` opened
/// coefficients.
///
/// A group of `D` unrelated public inputs is recomposed up front so the built circuit is
/// guaranteed to contain a `recompose` row: that pins down that the NPO table really is
/// enabled here, and therefore that the leaf hash's lowering is a choice rather than a
/// consequence of the table being absent.
fn build_arity4_leaf_hash_circuit() -> Circuit<EF> {
    let perm = default_koalabear_poseidon2_32();
    let mut builder = CircuitBuilder::<EF>::new();
    builder.enable_poseidon2_perm_width_32::<KoalaBearD4Width32, _>(
        generate_poseidon2_trace::<EF, KoalaBearD4Width32>,
        perm,
    );
    builder.enable_recompose::<F>(generate_recompose_trace::<F, EF>);

    let unrelated: Vec<Target> = (0..D).map(|_| builder.public_input()).collect();
    builder
        .recompose_base_coeffs_to_ext::<F>(&unrelated)
        .expect("recompose lowers through the NPO table");

    let cap: Vec<Vec<Target>> = vec![
        (0..CFG.capacity_ext())
            .map(|_| builder.public_input())
            .collect(),
    ];
    let dimensions = [Dimensions {
        width: LEAF_WIDTH,
        height: LEAF_HEIGHT,
    }];
    let index_bits: Vec<Target> = (0..LOG_MAX_HEIGHT)
        .map(|_| builder.public_input())
        .collect();
    let opened: Vec<Vec<Target>> = vec![(0..LEAF_WIDTH).map(|_| builder.public_input()).collect()];

    verify_batch_circuit_arity4::<F, EF>(
        &mut builder,
        CFG,
        &cap,
        &dimensions,
        &index_bits,
        &opened,
    )
    .expect("verify_batch_circuit_arity4 builds");

    builder.build().expect("circuit builds")
}

fn is_npo_type(op: &Op<EF>, needle: &str) -> bool {
    match op {
        Op::NonPrimitiveOpWithExecutor { executor, .. } => {
            format!("{:?}", executor.op_type()).contains(needle)
        }
        _ => false,
    }
}

fn writes(op: &Op<EF>, wid: WitnessId) -> bool {
    match op {
        Op::Const { out, .. } | Op::Public { out, .. } | Op::Alu { out, .. } => *out == wid,
        Op::Hint { outputs, .. } => outputs.contains(&wid),
        Op::NonPrimitiveOpWithExecutor { outputs, .. } => outputs.iter().any(|o| o.contains(&wid)),
    }
}

/// Position of the op that writes `wid`.
fn writer_position(circuit: &Circuit<EF>, wid: WitnessId) -> usize {
    circuit
        .ops
        .iter()
        .position(|op| writes(op, wid))
        .unwrap_or_else(|| panic!("no op writes {wid:?}"))
}

/// Every witness read by a Poseidon2 permutation, in op order.
fn permutation_input_witnesses(circuit: &Circuit<EF>) -> Vec<WitnessId> {
    circuit
        .ops
        .iter()
        .filter(|op| is_npo_type(op, "poseidon2_perm"))
        .flat_map(|op| match op {
            Op::NonPrimitiveOpWithExecutor { inputs, .. } => inputs.concat(),
            _ => unreachable!(),
        })
        .collect()
}

fn is_exact_npo_type(op: &Op<EF>, expected: &str) -> bool {
    match op {
        Op::NonPrimitiveOpWithExecutor { executor, .. } => executor.op_type().as_str() == expected,
        _ => false,
    }
}

/// The leaf limbs absorbed by the first permutation, which hashes the leaf: its first
/// `LEAF_WIDTH / D` rate inputs.
fn leaf_hash_input_witnesses(circuit: &Circuit<EF>) -> Vec<WitnessId> {
    circuit
        .ops
        .iter()
        .find(|op| is_npo_type(op, "poseidon2_perm"))
        .map(|op| match op {
            Op::NonPrimitiveOpWithExecutor { inputs, .. } => inputs
                .iter()
                .take(LEAF_WIDTH / D)
                .flatten()
                .copied()
                .collect(),
            _ => unreachable!(),
        })
        .expect("the leaf hash runs a permutation")
}

#[test]
fn arity4_leaf_hash_limbs_use_coefficient_bound_recompose() {
    let circuit = build_arity4_leaf_hash_circuit();

    assert!(
        circuit.ops.iter().any(|op| is_npo_type(op, "recompose")),
        "the recompose NPO table must be enabled for this test to say anything"
    );

    for wid in permutation_input_witnesses(&circuit) {
        let writer = &circuit.ops[writer_position(&circuit, wid)];
        assert!(
            !is_exact_npo_type(writer, "recompose"),
            "a permutation reads {wid:?}, whose only writer is a plain recompose row: its packed \
             value is a free main-trace column"
        );
    }

    let leaf_inputs = leaf_hash_input_witnesses(&circuit);
    assert_eq!(
        leaf_inputs.len(),
        LEAF_WIDTH / D,
        "each leaf limb is one CTL input"
    );
    assert!(
        leaf_inputs.iter().all(|&wid| {
            is_exact_npo_type(
                &circuit.ops[writer_position(&circuit, wid)],
                "recompose/coeff",
            )
        }),
        "every leaf limb must be written by an exact coefficient-bound row"
    );
}

#[test]
fn re_pointing_an_arity4_leaf_hash_packing_is_visible_to_the_verifier() {
    let honest = build_arity4_leaf_hash_circuit();
    let leaf_inputs = leaf_hash_input_witnesses(&honest);

    // The first leaf limb's coefficient-bound packing row, and its first operand.
    let packing_pos = writer_position(&honest, leaf_inputs[0]);
    assert!(is_exact_npo_type(
        &honest.ops[packing_pos],
        "recompose/coeff"
    ));
    let original_operand = match &honest.ops[packing_pos] {
        Op::NonPrimitiveOpWithExecutor { inputs, .. } => inputs[0][0],
        _ => unreachable!(),
    };

    // Re-point the packing at a different coefficient the same leaf already carries.
    let donor = leaf_inputs
        .iter()
        .filter_map(|&wid| match &honest.ops[writer_position(&honest, wid)] {
            Op::NonPrimitiveOpWithExecutor { inputs, .. } if inputs[0][0] != original_operand => {
                Some(inputs[0][0])
            }
            _ => None,
        })
        .next()
        .expect("a second coefficient-bound leaf limb to donate an operand");

    let mut edited = honest.clone();
    match &mut edited.ops[packing_pos] {
        Op::NonPrimitiveOpWithExecutor { inputs, .. } => inputs[0][0] = donor,
        _ => unreachable!(),
    }

    let honest_prep = honest
        .generate_preprocessed_columns::<D>()
        .expect("honest preprocessed columns");
    let edited_prep = edited
        .generate_preprocessed_columns::<D>()
        .expect("edited preprocessed columns");
    assert!(
        honest_prep != edited_prep,
        "re-pointing the packing that feeds the arity-4 leaf hash must change the constraint \
         system the verifier derives, not just prover-side data"
    );
}
