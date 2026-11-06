//! End-to-end gate for Goldilocks D3 / Poseidon2 width-12 recursion: two proved layers.
//!
//! The inner proof is a native batch-STARK proof in lrup's config shape (cubic trinomial
//! challenges, W12 hashing, cap height 0, `max_log_arity` 3, `log_final_poly_len` 0, a query proof
//! of work, no batch proof of work) of three toy AIRs:
//!
//! - `Squares` (2^3 rows): a preprocessed column and a public value; sends `(x, x^2 + k)`.
//! - `Cubes` (2^5 rows): a degree-3 constraint `z = x^3`, so its quotient has two chunks; sends
//!   `(x, z)`.
//! - `Lookup` (2^7 rows): receives both, on two global buses.
//!
//! Layer 1 verifies the inner proof in-circuit (`verify_batch_circuit`) and proves that circuit at
//! `D = 3`. Layer 2 verifies the layer-1 proof in-circuit (the D3 backend's
//! `build_next_layer_circuit`) and proves that circuit at `D = 3`. Both layer proofs are verified
//! natively.
//!
//! Negatives: a changed opened value, a changed Merkle sibling and a bad query PoW witness in the
//! inner proof; an inner proof of an invalid trace (honest FRI, failing constraint), rejected by
//! both verifiers at the out-of-domain check; and a tampered layer-1 proof fed to layer 2.
//!
//! The fast tests use `D3FriParams::test_params()`. The ignored
//! `two_layers_at_lrup_parameters` runs the inner proof at lrup's exact parameters and both
//! layers at a 140-bit recursion config, and prints each layer's table heights, times and peak
//! memory.

#[path = "common/goldilocks_d3_config.rs"]
mod goldilocks_d3_config;
#[path = "common/goldilocks_d3_toy.rs"]
mod goldilocks_d3_toy;

use std::time::{Duration, Instant};

use goldilocks_d3_config::{
    D, D3FriParams, D3RecursionConfig, EF, F, ProvedLayer, prove_layer_with_stats,
};
use goldilocks_d3_toy::{
    CUBES, CUBES_ROWS, NextLayerRun, ToyProof, peak_rss_mib, permutations, reset_peak_rss,
    run_next_layer, verifier_circuit,
};
use p3_batch_stark::{BatchVerificationError, VerificationError};
use p3_circuit::CircuitError;
use p3_circuit::tables::Traces;
use p3_circuit_prover::BatchStarkProof;
use p3_field::PrimeCharacteristicRing;

// ---------------------------------------------------------------------------------------------
// Measurements
// ---------------------------------------------------------------------------------------------

fn report(
    name: &str,
    params: D3FriParams,
    build: Duration,
    run: Duration,
    traces: &Traces<EF>,
    layer: &ProvedLayer,
) {
    let proof = &layer.proof;
    let [challenger, ordinary] = permutations(traces);
    let rows: Vec<usize> = proof.rows.iter().collect();
    eprintln!("== {name} (proved with {params:?})");
    eprintln!(
        "   circuit build {build:.2?}, execution {run:.2?}, prepare {:.2?}, prove {:.2?}, \
         native verify {:.2?}, peak RSS {} MiB",
        layer.prepare,
        layer.prove,
        layer.verify,
        peak_rss_mib().map_or_else(|| "n/a".to_string(), |mib| mib.to_string()),
    );
    eprintln!("   permutations: challenger {challenger}, ordinary {ordinary}");
    eprintln!("   primitive rows (Const, Public, ALU): {rows:?}");
    for entry in &proof.non_primitives {
        eprintln!(
            "   non-primitive {}: {} rows, {} lanes",
            entry.op_type, entry.rows, entry.lanes
        );
    }
    eprintln!(
        "   committed degree bits per table: {:?}",
        proof.proof.degree_bits
    );
}

/// Both proved layers.
struct TwoLayers {
    layer1: ProvedLayer,
    layer2: ProvedLayer,
}

/// The inner proof under `inner`, then layers 1 and 2, each proved under `layer` and verified
/// natively. Prints each layer's measurements.
fn two_layers(inner: D3FriParams, layer: D3FriParams) -> TwoLayers {
    reset_peak_rss();
    let start = Instant::now();
    let toy = ToyProof::new(inner);
    eprintln!(
        "== inner native proof ({inner:?}): prove + verify {:.2?}, peak RSS {} MiB",
        start.elapsed(),
        peak_rss_mib().map_or_else(|| "n/a".to_string(), |mib| mib.to_string()),
    );

    // Layer 1: verify the inner proof in-circuit and prove that circuit.
    reset_peak_rss();
    let layer1_config = D3RecursionConfig::new(layer);
    let (layer1, layer1_circuit_size) = {
        let start = Instant::now();
        let verifier = verifier_circuit(&toy, &toy.proof);
        let build = start.elapsed();
        let query_paths = toy.query_paths();
        let start = Instant::now();
        let traces = verifier
            .run(&query_paths)
            .expect("the inner proof's verifier circuit runs");
        let run = start.elapsed();
        let proved = prove_layer_with_stats(&layer1_config, &verifier.circuit, &traces);
        report("layer 1", layer, build, run, &traces, &proved);
        (proved, permutations(&traces))
    };

    // Layer 2: verify the layer-1 proof in-circuit and prove that circuit.
    reset_peak_rss();
    let layer2_config = D3RecursionConfig::new(layer);
    let layer2 = {
        let NextLayerRun {
            circuit,
            build,
            run,
            traces,
        } = run_next_layer(&layer1_config, &layer1.proof, &layer1.proof, &layer1.proof);
        let traces = traces.expect("the layer-1 proof's verifier circuit runs");
        let proved = prove_layer_with_stats(&layer2_config, &circuit, &traces);
        report("layer 2", layer, build, run, &traces, &proved);
        assert!(
            permutations(&traces)[1] > layer1_circuit_size[1],
            "layer 2 verifies a larger proof than layer 1"
        );
        proved
    };
    TwoLayers { layer1, layer2 }
}

// ---------------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------------

#[test]
fn two_layers_prove_and_verify() {
    let layers = two_layers(D3FriParams::test_params(), D3FriParams::test_params());
    assert_eq!(layers.layer1.proof.ext_degree, D);
    assert_eq!(layers.layer2.proof.ext_degree, D);
}

/// Layers 1 and 2 over an inner proof at lrup's exact parameters, each layer at a 140-bit
/// recursion config (rate 1/4, 175 queries, 22-bit query PoW). Run explicitly, on one thread,
/// to record the per-layer table heights, times and peak memory.
#[test]
#[ignore = "slow: lrup's inner parameters and 140-bit recursion layers; run with --ignored"]
fn two_layers_at_lrup_parameters() {
    let inner = D3FriParams::lrup_inner_params();
    let config = D3RecursionConfig::new(inner);
    let fri = config.fri_params();
    // lrup-backend-p3 `make_config`.
    assert_eq!(
        (
            fri.log_blowup,
            fri.num_queries,
            fri.query_proof_of_work_bits,
            fri.max_log_arity,
            fri.log_final_poly_len,
            fri.commit_proof_of_work_bits,
            fri.batch_proof_of_work_bits,
        ),
        (1, 285, 22, 3, 0, 0, 0)
    );
    two_layers(inner, D3FriParams::recursion_layer_params());
}

/// A changed opened value changes the transcript the circuit replays, so the query PoW check or
/// the Merkle checks of the moved query indices fail at execution. The native verifier rejects
/// the same proof.
#[test]
fn changed_opened_value_is_rejected() {
    let toy = ToyProof::new(D3FriParams::test_params());
    let honest_paths = toy.query_paths();
    for instance in 0..toy.airs.len() {
        let mut proof = ToyProof::new(D3FriParams::test_params()).proof;
        proof.opened_values.instances[instance]
            .base_opened_values
            .trace_local[1] += EF::ONE;
        assert!(
            toy.verify_natively(&proof).is_err(),
            "AIR {instance}: the native verifier rejects"
        );
        let error = verifier_circuit(&toy, &proof)
            .run(&honest_paths)
            .expect_err("a changed opened value must fail execution");
        eprintln!("changed opened value (AIR {instance}): {error}");
    }
}

#[test]
fn changed_merkle_sibling_is_rejected() {
    let toy = ToyProof::new(D3FriParams::test_params());
    let verifier = verifier_circuit(&toy, &toy.proof);
    let honest = toy.query_paths();
    // In-circuit: a sibling of an input (trace) opening and of a commit-phase opening.
    for (input, place) in [(true, "input batch"), (false, "commit phase")] {
        let mut paths = honest.clone();
        let chain = if input {
            &mut paths[0].input[0]
        } else {
            &mut paths[0].commit_phase[0]
        };
        chain[0][0] += F::ONE;
        let error = verifier
            .run(&paths)
            .expect_err("a changed Merkle sibling must fail execution");
        eprintln!("changed {place} sibling: {error}");
    }
    // Natively: the same kind of change in the proof's pruned input and commit-phase paths.
    for input in [true, false] {
        let mut proof = ToyProof::new(D3FriParams::test_params()).proof;
        let siblings = if input {
            &mut proof.opening_proof.input_openings[0]
                .opening_proof
                .sibling_hashes
        } else {
            &mut proof.opening_proof.commit_phase_openings[0]
                .opening_proof
                .sibling_hashes
        };
        siblings[0][0] += F::ONE;
        assert!(
            toy.verify_natively(&proof).is_err(),
            "the native verifier rejects a changed sibling"
        );
    }
}

#[test]
fn bad_query_pow_witness_is_rejected() {
    let toy = ToyProof::new(D3FriParams::test_params());
    let query_paths = toy.query_paths();
    let mut proof = ToyProof::new(D3FriParams::test_params()).proof;
    proof.opening_proof.query_pow_witness += F::ONE;
    assert!(
        toy.verify_natively(&proof).is_err(),
        "the native verifier rejects the changed witness"
    );
    let error = verifier_circuit(&toy, &proof)
        .run(&query_paths)
        .expect_err("a bad query PoW witness must fail execution");
    eprintln!("bad query PoW witness: {error}");
}

/// A proof of a trace that breaks `z = x^3` on one `Cubes` row, with the buses balanced. The
/// quotient is still a low-degree polynomial, so FRI, its proof of work and its Merkle paths are
/// all honest; only the out-of-domain check `C(zeta) = Z_H(zeta) q(zeta)` fails. The native
/// verifier rejects there, and the in-circuit verifier fails the same check at execution (a
/// witness conflict on the connected quotient value; every other check passes).
#[test]
#[cfg_attr(
    debug_assertions,
    ignore = "debug provers check the constraints and panic before a proof exists"
)]
fn invalid_trace_is_rejected_at_the_ood_check() {
    let params = D3FriParams::test_params();
    let toy = ToyProof::prove(params, Some(CUBES_ROWS / 2));
    let native = toy.verify_natively(&toy.proof);
    assert!(
        matches!(
            native,
            Err(BatchVerificationError::Verification(
                VerificationError::OodEvaluationMismatch { index: Some(CUBES) }
            ))
        ),
        "the native verifier rejects at the OOD check of `Cubes`: {native:?}"
    );
    // FRI is honest: the query PoW, the commit-phase folding and the paths all check natively.
    let query_paths = toy
        .config
        .try_query_paths(&toy.proof.opening_proof, toy.transcript(&toy.proof))
        .expect("the invalid trace's FRI proof is honest");
    let error = verifier_circuit(&toy, &toy.proof)
        .run(&query_paths)
        .expect_err("an invalid trace must fail execution");
    assert!(
        matches!(error, CircuitError::WitnessConflict { .. }),
        "the failing check is a connection, not a hash or PoW operation: {error}"
    );
    eprintln!("invalid trace: {error}");

    // The same circuit shape accepts the honest proof.
    let honest = ToyProof::new(params);
    verifier_circuit(&honest, &honest.proof)
        .run(&honest.query_paths())
        .expect("the honest proof's verifier circuit runs");
}

/// A layer-1 proof with one changed opened value. The native verifier rejects it, its FRI paths do
/// not restore (the backend refuses to set the layer-2 private data), and with the honest proof's
/// paths the layer-2 verifier circuit fails at execution.
#[test]
fn tampered_layer1_proof_is_rejected_by_layer2() {
    let params = D3FriParams::test_params();
    let toy = ToyProof::new(params);
    let layer1_config = D3RecursionConfig::new(params);
    let layer1 = {
        let verifier = verifier_circuit(&toy, &toy.proof);
        let traces = verifier.run(&toy.query_paths()).unwrap();
        prove_layer_with_stats(&layer1_config, &verifier.circuit, &traces)
    };
    // The honest layer-1 proof runs through layer 2.
    run_next_layer(&layer1_config, &layer1.proof, &layer1.proof, &layer1.proof)
        .traces
        .expect("the honest layer-1 proof's verifier circuit runs");
    layer1
        .verifier
        .verify(&clone_layer(&layer1.proof), &[])
        .expect("an unchanged copy verifies");

    // Change an opened value of every table in turn (primitive and non-primitive).
    for table in 0..layer1.proof.proof.opened_values.instances.len() {
        let mut tampered = clone_layer(&layer1.proof);
        tampered.proof.opened_values.instances[table]
            .base_opened_values
            .trace_local[0] += EF::ONE;
        assert!(
            layer1.verifier.verify(&tampered, &[]).is_err(),
            "table {table}: the native verifier rejects"
        );
        let own_paths = run_next_layer(&layer1_config, &layer1.proof, &tampered, &tampered)
            .traces
            .expect_err("the tampered proof must be rejected");
        assert!(own_paths.starts_with("private data"), "{own_paths}");
        let honest_paths = run_next_layer(&layer1_config, &layer1.proof, &tampered, &layer1.proof)
            .traces
            .expect_err("the tampered proof must fail layer-2 execution");
        assert!(honest_paths.starts_with("execution"), "{honest_paths}");
        eprintln!("tampered layer-1 table {table}: {own_paths} / {honest_paths}");
    }
}

fn clone_layer(proof: &BatchStarkProof<D3RecursionConfig>) -> BatchStarkProof<D3RecursionConfig> {
    // `BatchStarkProof` is serde-only; round-trip it.
    postcard::from_bytes(&postcard::to_allocvec(proof).unwrap()).unwrap()
}
