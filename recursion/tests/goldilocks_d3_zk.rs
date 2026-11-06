//! Salted hiding proofs at Goldilocks D3 / Poseidon2 width 12.
//!
//! The circuit is the second recursion layer of `goldilocks_d3_e2e`: a native inner proof of the
//! toy AIRs, layer 1 (its verifier circuit, proved without hiding), and layer 2 (the layer-1
//! proof's verifier circuit, built by the D3 backend). Layer 2 is proved under
//! `p3_circuit_prover::config::goldilocks_d3_w12_zk` (salted input and FRI MMCSs, random
//! codewords, trace and quotient masks) and verified natively. No in-circuit verifier of a hiding
//! proof is involved.
//!
//! Every hiding config here is built from OS entropy (`/dev/urandom`, the kernel generator: this
//! crate's `rand` has no `sys_rng` feature). No test uses a seeded generator.
//!
//! Tests:
//! - the hiding layer-2 proof verifies natively, with the hiding structure present;
//! - two proofs of the same statement and witness share no commitment, Merkle digest, salt or
//!   opened value (walked field by field);
//! - hiding proofs of one preparation proven concurrently on one Rayon pool complete and share
//!   none of these either;
//! - a table below the hiding budget is refused (by the config's packing check, and by the PCS
//!   when proving with an unpadded packing), and so are too few random codewords;
//! - a changed salt (input batch or FRI commit phase) is rejected by the native verifier;
//! - a changed opened value, random-codeword opening or query opening is rejected.
//!
//! The ignored `hiding_layer2_at_outer_parameters` measures the hiding layer-2 proof at the
//! outer-wrap parameters against the non-hiding one.

#[path = "common/goldilocks_d3_config.rs"]
mod goldilocks_d3_config;
#[path = "common/goldilocks_d3_toy.rs"]
mod goldilocks_d3_toy;

use std::collections::BTreeSet;
use std::fs::File;
use std::io::Read;
use std::time::{Duration, Instant};

use goldilocks_d3_config::{
    D, D3FriParams, D3RecursionConfig, DIGEST, EF, F, PERM, backend, prove_layer_with_stats,
};
use goldilocks_d3_toy::{ToyProof, peak_rss_mib, reset_peak_rss, run_next_layer, verifier_circuit};
use p3_circuit::Circuit;
use p3_circuit::tables::Traces;
use p3_circuit_prover::batch_stark_prover::poseidon2_air_builders_for_configs;
use p3_circuit_prover::common::NpoAirBuilder;
use p3_circuit_prover::config::{
    GOLDILOCKS_D3_W12_ZK_SALT_ELEMS, GoldilocksD3W12ZkConfig, GoldilocksD3W12ZkError,
    GoldilocksD3W12ZkParams, goldilocks_d3_w12_zk, goldilocks_d3_w12_zk_public_preprocessing,
};
use p3_circuit_prover::{
    BatchStarkProof, BatchStarkProver, CircuitVerifier, ConstraintProfile, Poseidon2ProverD3,
    PreparedCircuitProver, PublicPreprocessingConfig, RecomposeAirBuilder, RecomposeProver,
    TablePacking,
};
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing, PrimeField64};
use p3_recursion::{BatchOnly, PcsRecursionBackend};
use p3_uni_stark::StarkOpeningLayout;
use rand::{TryCryptoRng, TryRng};

type ZkConfig = GoldilocksD3W12ZkConfig;
type ZkProof = BatchStarkProof<ZkConfig>;

// ---------------------------------------------------------------------------------------------
// OS entropy
// ---------------------------------------------------------------------------------------------

/// The kernel's generator, read directly. Every hiding config in these tests draws its three
/// seeds from it.
struct DevUrandom(File);

impl DevUrandom {
    fn open() -> Self {
        Self(File::open("/dev/urandom").expect("OS entropy (/dev/urandom) is available"))
    }
}

impl TryRng for DevUrandom {
    type Error = std::io::Error;

    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
        let mut bytes = [0u8; 4];
        self.0.read_exact(&mut bytes)?;
        Ok(u32::from_le_bytes(bytes))
    }

    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        let mut bytes = [0u8; 8];
        self.0.read_exact(&mut bytes)?;
        Ok(u64::from_le_bytes(bytes))
    }

    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Self::Error> {
        self.0.read_exact(dst)
    }
}

impl TryCryptoRng for DevUrandom {}

fn zk_config(params: GoldilocksD3W12ZkParams) -> ZkConfig {
    goldilocks_d3_w12_zk(params, &mut DevUrandom::open()).expect("the hiding config builds")
}

// ---------------------------------------------------------------------------------------------
// The layer-2 circuit and its hiding prover
// ---------------------------------------------------------------------------------------------

/// The layer-2 verifier circuit and its execution traces.
struct Layer2 {
    circuit: Circuit<EF>,
    traces: Traces<EF>,
    /// The non-hiding layer-1 proof's config, for the non-hiding layer-2 comparison.
    layer1_config: D3RecursionConfig,
}

/// The inner toy proof under `inner`, layer 1 proved (without hiding) under `layer1`, then the
/// layer-2 verifier circuit built and run.
fn layer2(inner: D3FriParams, layer1: D3FriParams) -> Layer2 {
    let toy = ToyProof::new(inner);
    let layer1_config = D3RecursionConfig::new(layer1);
    let verifier = verifier_circuit(&toy, &toy.proof);
    let traces = verifier
        .run(&toy.query_paths())
        .expect("the inner proof's verifier circuit runs");
    let proved = prove_layer_with_stats(&layer1_config, &verifier.circuit, &traces);
    let run = run_next_layer(&layer1_config, &proved.proof, &proved.proof, &proved.proof);
    Layer2 {
        circuit: run.circuit,
        traces: run
            .traces
            .expect("the layer-1 proof's verifier circuit runs"),
        layer1_config,
    }
}

/// Prepare `circuit` for hiding proofs, with the tables the D3 backend registers (the shared
/// W12 Poseidon2 table and `recompose/coeff`) and `packing`.
fn prepare_hiding(
    config: ZkConfig,
    packing: TablePacking,
    circuit: &Circuit<EF>,
) -> Result<PreparedCircuitProver<ZkConfig>, p3_circuit_prover::BatchStarkProverError> {
    prepare_hiding_with(config, None, packing, circuit)
}

/// [`prepare_hiding`], with the preprocessing committed under `preprocessing` when given.
fn prepare_hiding_with(
    config: ZkConfig,
    preprocessing: Option<&PublicPreprocessingConfig<ZkConfig>>,
    packing: TablePacking,
    circuit: &Circuit<EF>,
) -> Result<PreparedCircuitProver<ZkConfig>, p3_circuit_prover::BatchStarkProverError> {
    let shared = PERM.for_shared_challenger_table();
    let mut prover = BatchStarkProver::new(config).with_table_packing(packing);
    prover.register_table_prover(Box::new(Poseidon2ProverD3::new(
        shared,
        ConstraintProfile::Standard,
    )));
    prover.register_table_prover(Box::new(RecomposeProver::<3>::new(1, true)));
    let mut air_builders: Vec<Box<dyn NpoAirBuilder<ZkConfig, D>>> =
        poseidon2_air_builders_for_configs::<ZkConfig, D>(vec![shared]);
    air_builders.push(Box::new(RecomposeAirBuilder::<3>::new(1, true)));
    // The preprocessors depend only on the base field: take the D3 backend's.
    let preprocessors =
        PcsRecursionBackend::<D3RecursionConfig, BatchOnly, D>::non_primitive_preprocessors(
            &backend(),
        );
    match preprocessing {
        None => prover.prepare_circuit::<EF, D>(
            circuit,
            &preprocessors,
            &air_builders,
            ConstraintProfile::Standard,
        ),
        Some(preprocessing) => prover.prepare_circuit_with_public_preprocessing::<EF, D>(
            preprocessing,
            circuit,
            &preprocessors,
            &air_builders,
            ConstraintProfile::Standard,
        ),
    }
}

/// A hiding layer proof with its verifier and timings.
struct HidingLayer {
    prepared: PreparedCircuitProver<ZkConfig>,
    verifier: CircuitVerifier<ZkConfig>,
    proof: ZkProof,
    prepare: Duration,
    prove: Duration,
    verify: Duration,
}

/// Prepare `circuit` under a fresh OS-seeded hiding config with tables padded to the hiding
/// budget, prove `traces` once and verify natively.
fn prove_hiding(
    params: GoldilocksD3W12ZkParams,
    circuit: &Circuit<EF>,
    traces: &Traces<EF>,
) -> HidingLayer {
    let packing = params
        .pad_table_packing(TablePacking::new(2, 4))
        .expect("the hiding budget fits");
    params
        .check_table_packing(&packing)
        .expect("the padded packing meets the hiding budget");
    let start = Instant::now();
    let prepared = prepare_hiding(zk_config(params), packing, circuit)
        .expect("the layer-2 circuit prepares under the hiding config");
    let prepare = start.elapsed();
    let start = Instant::now();
    let proof = prepared
        .prove(traces)
        .expect("the layer-2 circuit proves under the hiding config");
    let prove = start.elapsed();
    let verifier = prepared.verifier();
    let start = Instant::now();
    verifier
        .verify(&proof, &[])
        .expect("the hiding layer-2 proof verifies natively");
    let verify = start.elapsed();
    HidingLayer {
        prepared,
        verifier,
        proof,
        prepare,
        prove,
        verify,
    }
}

fn clone_proof(proof: &ZkProof) -> ZkProof {
    // `BatchStarkProof` is serde-only; round-trip it.
    postcard::from_bytes(&postcard::to_allocvec(proof).unwrap()).unwrap()
}

fn proof_bytes<T: serde::Serialize>(proof: &T) -> usize {
    postcard::to_allocvec(proof).unwrap().len()
}

/// The PCS opening rounds of a batch proof under a hiding PCS: the randomization polynomial
/// first, then the main traces, the quotient chunks, the preprocessed traces (when present) and
/// the permutation traces (when present).
const fn layout() -> StarkOpeningLayout {
    StarkOpeningLayout::new(true)
}

// ---------------------------------------------------------------------------------------------
// Everything a proof discloses, walked field by field
// ---------------------------------------------------------------------------------------------

/// Every value a hiding proof reveals that may depend on the witness or the prover's randomness.
///
/// Excluded, because they are public by definition and identical in any two proofs of one
/// statement: the preprocessed (verifying-key) commitment, and every opening of the preprocessed
/// round (its out-of-domain values, query rows, salts and Merkle siblings; the tree is fixed at
/// preparation and its contents are the public circuit description); the public values and
/// statement; the table shape (`degree_bits`, row counts, packing, non-primitive manifest,
/// extension metadata). Also excluded: the proof-of-work nonces (lookup, out-of-domain, batch,
/// commit-phase and query witnesses), which are public functions of the transcript and grinding
/// bits; with few grinding bits two proofs can find the same small nonce.
#[derive(Default)]
struct Disclosed {
    /// Every commitment root (main, permutation, quotient, randomization, each FRI commit-phase
    /// layer) and every Merkle sibling digest of every opening.
    digests: Vec<[u64; DIGEST]>,
    /// Every leaf salt: input batches and FRI commit phase.
    salts: Vec<Vec<u64>>,
    /// Out-of-domain openings (main, next row, quotient chunks, randomization polynomial,
    /// permutation), the random-codeword openings, FRI commit-phase sibling values, the final
    /// polynomial and the lookup terminals.
    ext_values: Vec<[u64; 3]>,
    /// Query openings of the input batches (one row per matrix per query).
    base_values: Vec<u64>,
    /// Salts of the input batches only, and of the FRI commit phase only.
    input_salts: Vec<Vec<u64>>,
    fri_salts: Vec<Vec<u64>>,
}

fn base(x: F) -> u64 {
    x.as_canonical_u64()
}

fn ext(x: EF) -> [u64; 3] {
    let coeffs: &[F] = x.as_basis_coefficients_slice();
    [base(coeffs[0]), base(coeffs[1]), base(coeffs[2])]
}

fn digest(d: &[F; DIGEST]) -> [u64; DIGEST] {
    d.map(base)
}

fn disclosed(proof: &ZkProof) -> Disclosed {
    let mut out = Disclosed::default();
    let batch = &proof.proof;
    let layout = layout();
    let preprocessed_round = batch_has_preprocessed(proof).then_some(layout.preprocessed);

    // Commitments.
    let commitments = &batch.commitments;
    let mut roots = vec![&commitments.main, &commitments.quotient_chunks];
    roots.extend(commitments.permutation.as_ref());
    roots.extend(commitments.random.as_ref());
    let (random_openings, fri) = &batch.opening_proof;
    roots.extend(fri.commit_phase_commits.iter());
    for cap in roots {
        out.digests.extend(cap.roots().iter().map(digest));
    }

    // Out-of-domain openings (preprocessed columns excluded).
    for instance in &batch.opened_values.instances {
        let values = &instance.base_opened_values;
        let mut ood: Vec<EF> = values.trace_local.clone();
        ood.extend(values.trace_next.iter().flatten());
        ood.extend(values.quotient_chunks.iter().flatten());
        ood.extend(values.random.iter().flatten());
        ood.extend(&instance.permutation_local);
        ood.extend(&instance.permutation_next);
        out.ext_values.extend(ood.into_iter().map(ext));
    }
    // Random-codeword openings: round, matrix, point.
    for (round, matrices) in random_openings.iter().enumerate() {
        for points in matrices {
            for values in points {
                if Some(round) == preprocessed_round {
                    assert!(
                        values.is_empty(),
                        "public preprocessing has no random codewords"
                    );
                }
                out.ext_values.extend(values.iter().copied().map(ext));
            }
        }
    }
    out.ext_values
        .extend(batch.lookup_terminals.iter().flatten().map(|t| ext(t.0)));

    // Input-batch query openings: per round, the opened rows, salts and pruned Merkle siblings.
    for (round, opening) in fri.input_openings.iter().enumerate() {
        if Some(round) == preprocessed_round {
            continue;
        }
        for rows in &opening.opened_values {
            for row in rows {
                out.base_values.extend(row.iter().copied().map(base));
            }
        }
        let (salts, pruned) = &opening.opening_proof;
        for salt in salts.iter().flatten() {
            assert_eq!(salt.len(), GOLDILOCKS_D3_W12_ZK_SALT_ELEMS);
            out.input_salts
                .push(salt.iter().copied().map(base).collect());
        }
        out.digests.extend(pruned.sibling_hashes.iter().map(digest));
    }
    // FRI commit phase: sibling values, salts and Merkle siblings per layer; the final polynomial.
    for step in &fri.commit_phase_openings {
        for values in &step.sibling_values {
            out.ext_values.extend(values.iter().copied().map(ext));
        }
        let (salts, pruned) = &step.opening_proof;
        for salt in salts.iter().flatten() {
            assert_eq!(salt.len(), GOLDILOCKS_D3_W12_ZK_SALT_ELEMS);
            out.fri_salts.push(salt.iter().copied().map(base).collect());
        }
        out.digests.extend(pruned.sibling_hashes.iter().map(digest));
    }
    out.ext_values
        .extend(fri.final_poly.iter().copied().map(ext));
    out.salts.extend(out.input_salts.iter().cloned());
    out.salts.extend(out.fri_salts.iter().cloned());
    out
}

const fn batch_has_preprocessed(proof: &ZkProof) -> bool {
    proof.stark_common.preprocessed.is_some()
}

/// Assert `a` and `b` have no element in common; return their sizes.
fn assert_disjoint<T: Ord + Clone + core::fmt::Debug>(what: &str, a: &[T], b: &[T]) -> usize {
    assert!(!a.is_empty(), "{what}: the walk found nothing to compare");
    let a_set: BTreeSet<_> = a.iter().cloned().collect();
    let shared: Vec<_> = b.iter().filter(|x| a_set.contains(x)).collect();
    assert!(
        shared.is_empty(),
        "{what}: {} of {} values shared between the two proofs, e.g. {:?}",
        shared.len(),
        b.len(),
        shared.first()
    );
    a.len()
}

// ---------------------------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------------------------

/// The hiding layer-2 proof verifies natively and carries the hiding structure: a randomization
/// commitment and openings, three random-codeword values per private opening point, salts on
/// every leaf, and committed degrees doubled over tables padded to the hiding budget.
#[test]
fn hiding_layer2_proof_verifies() {
    let params = GoldilocksD3W12ZkParams::test();
    let layer = layer2(D3FriParams::test_params(), D3FriParams::test_params());
    let hiding = prove_hiding(params, &layer.circuit, &layer.traces);
    let batch = &hiding.proof.proof;
    assert_eq!(hiding.proof.ext_degree, D);
    assert!(batch.commitments.random.is_some());
    assert!(
        batch
            .opened_values
            .instances
            .iter()
            .all(|instance| instance.base_opened_values.random.is_some())
    );
    let min_log_height = params.min_trace_height().unwrap().trailing_zeros() as usize;
    assert!(
        batch.degree_bits.iter().all(|&bits| bits > min_log_height),
        "every table is padded to the hiding budget and doubled: {:?}",
        batch.degree_bits
    );
    let preprocessed = batch_has_preprocessed(&hiding.proof).then_some(layout().preprocessed);
    for (round, matrices) in batch.opening_proof.0.iter().enumerate() {
        let expected = if Some(round) == preprocessed {
            0
        } else {
            params.num_random_codewords
        };
        assert!(
            matrices
                .iter()
                .flatten()
                .all(|values| values.len() == expected),
            "round {round}: {expected} random-codeword values per point"
        );
    }
    let seen = disclosed(&hiding.proof);
    assert!(!seen.input_salts.is_empty() && !seen.fri_salts.is_empty());
    eprintln!(
        "hiding layer 2 ({params:?}): prepare {:.2?}, prove {:.2?}, verify {:.2?}, {} bytes, \
         degree bits {:?}",
        hiding.prepare,
        hiding.prove,
        hiding.verify,
        proof_bytes(&hiding.proof),
        batch.degree_bits
    );
}

/// Two proofs of the same statement and witness, from one preparation (one verifying key), share
/// no commitment root, Merkle digest, salt or opened value. A third proof from a separately built
/// config (fresh OS entropy) shares none with either, and has a different preprocessed
/// commitment. Within one proof the input-batch salts and the FRI salts (separate streams) do not
/// meet either.
#[test]
fn two_proofs_share_no_commitment_salt_or_opened_value() {
    let params = GoldilocksD3W12ZkParams::test();
    let layer = layer2(D3FriParams::test_params(), D3FriParams::test_params());
    let first = prove_hiding(params, &layer.circuit, &layer.traces);
    let second_proof = first
        .prepared
        .prove(&layer.traces)
        .expect("a second proof from the same preparation");
    first
        .verifier
        .verify(&second_proof, &[])
        .expect("the second proof verifies");
    let other = prove_hiding(params, &layer.circuit, &layer.traces);

    // Same statement, same shape, same verifying key for the first two.
    assert_eq!(
        first.proof.proof.degree_bits,
        second_proof.proof.degree_bits
    );
    let vk = |proof: &ZkProof| {
        proof
            .stark_common
            .preprocessed
            .as_ref()
            .map(|p| p.commitment.roots().iter().map(digest).collect::<Vec<_>>())
    };
    assert_eq!(vk(&first.proof), vk(&second_proof));
    assert!(vk(&first.proof).is_some());
    assert_ne!(
        vk(&first.proof),
        vk(&other.proof),
        "a separately built config salts its preprocessed commitment from fresh entropy"
    );

    let proofs = [&first.proof, &second_proof, &other.proof];
    let walks: Vec<Disclosed> = proofs.iter().map(|proof| disclosed(proof)).collect();
    for (i, j) in [(0, 1), (0, 2), (1, 2)] {
        let (a, b) = (&walks[i], &walks[j]);
        let counts = [
            assert_disjoint(
                "commitment roots and Merkle digests",
                &a.digests,
                &b.digests,
            ),
            assert_disjoint("salts", &a.salts, &b.salts),
            assert_disjoint(
                "out-of-domain, random-codeword, FRI and terminal values",
                &a.ext_values,
                &b.ext_values,
            ),
            assert_disjoint("input query openings", &a.base_values, &b.base_values),
        ];
        eprintln!(
            "proofs {i} and {j}: disjoint digests {}, salts {}, extension values {}, base values {}",
            counts[0], counts[1], counts[2], counts[3]
        );
    }
    for (index, walk) in walks.iter().enumerate() {
        assert_disjoint(
            &format!("proof {index}: input vs FRI salts"),
            &walk.input_salts,
            &walk.fri_salts,
        );
    }
}

/// Hiding proofs of one shared preparation, proven concurrently as tasks of one Rayon pool,
/// complete, verify, and share no commitment root, Merkle digest, salt or opened value.
///
/// All of them draw from the same PCS and MMCS generators. With `parallel`, a worker that waits
/// inside one proof's parallel work can pick up another proof that locks the same generator
/// (Plonky3#2368): this hangs if any generator lock is held across parallel work, and the
/// watchdog turns that hang into a failure. Concurrent draws must not repeat randomness.
#[test]
fn concurrent_proofs_from_one_preparation_complete_and_share_nothing() {
    use rayon::prelude::*;

    const PROOFS: usize = 4;
    const DEADLINE: Duration = Duration::from_secs(600);

    let params = GoldilocksD3W12ZkParams::test();
    let layer = layer2(D3FriParams::test_params(), D3FriParams::test_params());
    let first = prove_hiding(params, &layer.circuit, &layer.traces);

    let (done, finished) = std::sync::mpsc::channel::<()>();
    let watchdog = std::thread::spawn(move || {
        if finished.recv_timeout(DEADLINE).is_err() {
            eprintln!("concurrent hiding proofs did not finish within {DEADLINE:?}: aborting");
            std::process::abort();
        }
    });
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(PROOFS)
        .build()
        .expect("the test pool builds");
    let start = Instant::now();
    let proofs: Vec<ZkProof> = pool.install(|| {
        (0..PROOFS)
            .into_par_iter()
            .map(|_| {
                first
                    .prepared
                    .prove(&layer.traces)
                    .expect("a concurrent proof from the shared preparation")
            })
            .collect()
    });
    let elapsed = start.elapsed();
    done.send(()).expect("the watchdog is waiting");
    watchdog.join().expect("the watchdog exits");
    eprintln!(
        "{PROOFS} concurrent hiding proofs in {elapsed:.2?} (one sequential proof: {:.2?})",
        first.prove
    );

    for proof in &proofs {
        first
            .verifier
            .verify(proof, &[])
            .expect("a concurrent proof verifies");
    }
    let walks: Vec<Disclosed> = core::iter::once(&first.proof)
        .chain(&proofs)
        .map(disclosed)
        .collect();
    for i in 0..walks.len() {
        for j in i + 1..walks.len() {
            let (a, b) = (&walks[i], &walks[j]);
            assert_disjoint(
                &format!("proofs {i} and {j}: digests"),
                &a.digests,
                &b.digests,
            );
            assert_disjoint(&format!("proofs {i} and {j}: salts"), &a.salts, &b.salts);
            assert_disjoint(
                &format!("proofs {i} and {j}: extension values"),
                &a.ext_values,
                &b.ext_values,
            );
            assert_disjoint(
                &format!("proofs {i} and {j}: input query openings"),
                &a.base_values,
                &b.base_values,
            );
        }
        assert_disjoint(
            &format!("proof {i}: input vs FRI salts"),
            &walks[i].input_salts,
            &walks[i].fri_salts,
        );
    }
}

/// With the preprocessing committed under the public-seed configuration
/// (`goldilocks_d3_w12_zk_public_preprocessing`), two independent preparations of one circuit,
/// each with its own OS-seeded proving config, get the same preprocessed commitment and relation,
/// so the verifying key is recomputable: a proof from one verifies under the other's verifier. A
/// preparation that salts the preprocessing from OS entropy gets another commitment. The two
/// proofs still share no witness-dependent commitment, salt or opened value.
#[test]
fn public_preprocessing_gives_a_recomputable_verifying_key() {
    let params = GoldilocksD3W12ZkParams::test();
    let layer = layer2(D3FriParams::test_params(), D3FriParams::test_params());
    let packing = params
        .pad_table_packing(TablePacking::new(2, 4))
        .expect("the hiding budget fits");
    let prepare = |public: bool| {
        let preprocessing = public.then(|| {
            goldilocks_d3_w12_zk_public_preprocessing(params)
                .expect("the public preprocessing config builds")
        });
        prepare_hiding_with(
            zk_config(params),
            preprocessing.as_ref(),
            packing.clone(),
            &layer.circuit,
        )
        .expect("the layer-2 circuit prepares")
    };
    let vk = |verifier: &CircuitVerifier<ZkConfig>| {
        verifier
            .common_data()
            .preprocessed
            .as_ref()
            .map(|p| p.commitment.roots().iter().map(digest).collect::<Vec<_>>())
            .expect("the circuit has preprocessed columns")
    };

    let first = prepare(true);
    let second = prepare(true);
    let salted = prepare(false);
    assert_eq!(vk(&first.verifier()), vk(&second.verifier()));
    assert_eq!(
        first.relation().trace_degree_bits(),
        second.relation().trace_degree_bits()
    );
    assert_ne!(
        vk(&first.verifier()),
        vk(&salted.verifier()),
        "OS-entropy preprocessing salts give another commitment"
    );

    // Each proof verifies under the other preparation's verifier.
    let proof_first = first.prove(&layer.traces).expect("proves");
    let proof_second = second.prove(&layer.traces).expect("proves");
    second
        .verifier()
        .verify(&proof_first, &[])
        .expect("verifies under the independently prepared key");
    first
        .verifier()
        .verify(&proof_second, &[])
        .expect("verifies under the independently prepared key");
    // Not under the OS-salted preparation's key.
    assert!(salted.verifier().verify(&proof_first, &[]).is_err());

    let (a, b) = (disclosed(&proof_first), disclosed(&proof_second));
    assert_disjoint(
        "commitment roots and Merkle digests",
        &a.digests,
        &b.digests,
    );
    assert_disjoint("salts", &a.salts, &b.salts);
    assert_disjoint(
        "out-of-domain, random-codeword, FRI and terminal values",
        &a.ext_values,
        &b.ext_values,
    );
    assert_disjoint("input query openings", &a.base_values, &b.base_values);
}

/// A table below the hiding budget is refused: by the config's packing check, and by the hiding
/// PCS when the circuit is prepared or proved with an unpadded packing. The same circuit proves
/// once its tables are padded. Fewer random codewords than the extension degree are refused by
/// the constructor.
#[test]
fn table_below_hiding_budget_is_refused() {
    let params = GoldilocksD3W12ZkParams::test();
    assert_eq!(params.hiding_budget(), Some(2 * (8 + 3 * 2)));
    assert_eq!(params.min_trace_height(), Some(32));

    // 32 queries: a budget of 2 * (32 + 6) = 76 values, so 128 rows. The layer-2 circuit's
    // smallest table (Public, 64 rows at its natural height) falls below it.
    let params = GoldilocksD3W12ZkParams {
        num_queries: 32,
        ..params
    };
    let required = params.min_trace_height().unwrap();
    assert_eq!(params.hiding_budget(), Some(76));
    assert_eq!(required, 128);

    // The config's packing check.
    let unpadded = TablePacking::new(2, 4);
    assert_eq!(
        params.check_table_packing(&unpadded),
        Err(GoldilocksD3W12ZkError::TableBelowHidingBudget {
            required,
            got: unpadded.min_trace_height(),
        })
    );
    let short_alu = TablePacking::new(2, 4)
        .with_min_trace_height(required)
        .with_alu_min_height(required / 2);
    assert!(params.check_table_packing(&short_alu).is_err());
    let padded = params.pad_table_packing(unpadded.clone()).unwrap();
    assert_eq!(padded.min_trace_height(), required);
    params.check_table_packing(&padded).unwrap();

    // The hiding PCS, with the tables left at their natural heights.
    let layer = layer2(D3FriParams::test_params(), D3FriParams::test_params());
    let error = prepare_hiding(zk_config(params), unpadded, &layer.circuit)
        .and_then(|prepared| prepared.prove(&layer.traces))
        .map(|_| ())
        .expect_err("an unpadded table must be refused");
    let message = error.to_string();
    eprintln!("unpadded tables: {message}");
    assert!(
        message.contains("HidingBudgetExceeded"),
        "refused for the hiding budget: {message}"
    );

    // Padded to the budget, the same circuit proves and verifies; no table is below it.
    let hiding = prove_hiding(params, &layer.circuit, &layer.traces);
    let min_log_height = required.trailing_zeros() as usize;
    assert!(
        hiding
            .proof
            .proof
            .degree_bits
            .iter()
            .all(|&bits| bits > min_log_height),
        "{:?}",
        hiding.proof.proof.degree_bits
    );

    // Too few random codewords.
    let too_few = GoldilocksD3W12ZkParams {
        num_random_codewords: 2,
        ..params
    };
    assert!(matches!(
        goldilocks_d3_w12_zk(too_few, &mut DevUrandom::open()),
        Err(GoldilocksD3W12ZkError::InsufficientRandomCodewords {
            required: 3,
            got: 2
        })
    ));
}

/// A changed salt, in an input batch (every private round) or in a FRI commit-phase layer, is
/// rejected by the native verifier.
#[test]
fn tampered_salt_is_rejected() {
    let params = GoldilocksD3W12ZkParams::test();
    let layer = layer2(D3FriParams::test_params(), D3FriParams::test_params());
    let hiding = prove_hiding(params, &layer.circuit, &layer.traces);
    let preprocessed = layout().preprocessed;
    let rounds = hiding.proof.proof.opening_proof.1.input_openings.len();
    for round in 0..rounds {
        let mut proof = clone_proof(&hiding.proof);
        let salts = &mut proof.proof.opening_proof.1.input_openings[round]
            .opening_proof
            .0;
        salts[0][0][0] += F::ONE;
        let error = hiding
            .verifier
            .verify(&proof, &[])
            .expect_err("a changed input-batch salt must be rejected");
        eprintln!("input round {round} (preprocessed is {preprocessed}): {error}");
    }
    let layers = hiding
        .proof
        .proof
        .opening_proof
        .1
        .commit_phase_openings
        .len();
    assert!(layers > 0);
    for step in [0, layers - 1] {
        let mut proof = clone_proof(&hiding.proof);
        let salts = &mut proof.proof.opening_proof.1.commit_phase_openings[step]
            .opening_proof
            .0;
        let last = salts.len() - 1;
        salts[last][0][GOLDILOCKS_D3_W12_ZK_SALT_ELEMS - 1] += F::ONE;
        let error = hiding
            .verifier
            .verify(&proof, &[])
            .expect_err("a changed FRI commit-phase salt must be rejected");
        eprintln!("commit-phase layer {step}: {error}");
    }
}

/// A changed out-of-domain opening (main trace, quotient chunk, randomization polynomial), a
/// changed random-codeword opening (every private round) and a changed query opening are each
/// rejected by the native verifier.
#[test]
fn tampered_opened_value_is_rejected() {
    let params = GoldilocksD3W12ZkParams::test();
    let layer = layer2(D3FriParams::test_params(), D3FriParams::test_params());
    let hiding = prove_hiding(params, &layer.circuit, &layer.traces);
    let reject = |proof: &ZkProof, what: &str| {
        let error = hiding
            .verifier
            .verify(proof, &[])
            .expect_err("a changed opening must be rejected");
        eprintln!("{what}: {error}");
    };

    let instances = hiding.proof.proof.opened_values.instances.len();
    for instance in 0..instances {
        let mut proof = clone_proof(&hiding.proof);
        proof.proof.opened_values.instances[instance]
            .base_opened_values
            .trace_local[0] += EF::ONE;
        reject(&proof, &format!("trace_local of table {instance}"));
    }
    {
        let mut proof = clone_proof(&hiding.proof);
        proof.proof.opened_values.instances[0]
            .base_opened_values
            .quotient_chunks[0][0] += EF::ONE;
        reject(&proof, "quotient chunk of table 0");
    }
    {
        let mut proof = clone_proof(&hiding.proof);
        proof.proof.opened_values.instances[0]
            .base_opened_values
            .random
            .as_mut()
            .unwrap()[0] += EF::ONE;
        reject(&proof, "randomization polynomial of table 0");
    }
    let preprocessed = batch_has_preprocessed(&hiding.proof).then_some(layout().preprocessed);
    let rounds = hiding.proof.proof.opening_proof.0.len();
    for round in (0..rounds).filter(|&round| Some(round) != preprocessed) {
        let mut proof = clone_proof(&hiding.proof);
        let points = &mut proof.proof.opening_proof.0[round][0];
        let last = points.len() - 1;
        points[last][params.num_random_codewords - 1] += EF::ONE;
        reject(&proof, &format!("random-codeword opening, round {round}"));
    }
    {
        let mut proof = clone_proof(&hiding.proof);
        let rows = &mut proof.proof.opening_proof.1.input_openings[layout().trace].opened_values;
        rows[0][0][0] += F::ONE;
        reject(&proof, "query opening of the main trace");
    }
    {
        let mut proof = clone_proof(&hiding.proof);
        let values = &mut proof.proof.opening_proof.1.commit_phase_openings[0].sibling_values;
        values[0][0] += EF::ONE;
        reject(&proof, "FRI commit-phase sibling value");
    }
}

/// The outer-wrap parameters reach 140 proven bits under unique decoding and set the hiding
/// budget the tables must meet.
#[test]
fn outer_wrap_parameters() {
    let params = GoldilocksD3W12ZkParams::outer_wrap();
    params.validate().unwrap();
    let rate = 0.5f64.powi(params.log_blowup as i32);
    let bits_per_query = -((1.0 + rate) / 2.0).log2();
    let proven = (params.num_queries as f64).mul_add(bits_per_query, params.query_pow_bits as f64);
    eprintln!("outer wrap {params:?}: {bits_per_query:.4} bits/query, {proven:.2} proven bits");
    assert!(proven >= 140.0, "{proven}");
    assert_eq!(params.hiding_budget(), Some(2 * (143 + 3 * 2)));
    assert_eq!(params.min_trace_height(), Some(512));
}

/// The hiding layer-2 proof at the outer-wrap parameters, against the non-hiding layer-2 proof at
/// the 140-bit recursion-layer parameters and the hiding one at those same parameters.
/// The inner proof is at lrup's parameters and layer 1 at the recursion-layer parameters.
#[test]
#[ignore = "slow: lrup's inner parameters and 140-bit layers; run with --ignored"]
fn hiding_layer2_at_outer_parameters() {
    let recursion = D3FriParams::recursion_layer_params();
    let layer = layer2(D3FriParams::lrup_inner_params(), recursion);
    let report = |name: &str, bytes: usize, prepare: Duration, prove: Duration, bits: &[usize]| {
        eprintln!(
            "== {name}: prepare {prepare:.2?}, prove {prove:.2?}, peak RSS {} MiB, {bytes} bytes, \
             degree bits {bits:?}",
            peak_rss_mib().map_or_else(|| "n/a".to_string(), |mib| mib.to_string()),
        );
    };

    reset_peak_rss();
    let plain = prove_layer_with_stats(&layer.layer1_config, &layer.circuit, &layer.traces);
    report(
        &format!("non-hiding layer 2 ({recursion:?})"),
        proof_bytes(&plain.proof),
        plain.prepare,
        plain.prove,
        &plain.proof.proof.degree_bits,
    );
    drop(plain);

    for params in [
        GoldilocksD3W12ZkParams::outer_wrap(),
        GoldilocksD3W12ZkParams {
            log_blowup: recursion.log_blowup,
            num_queries: recursion.num_queries,
            query_pow_bits: recursion.query_pow_bits,
            max_log_arity: recursion.max_log_arity,
            ..GoldilocksD3W12ZkParams::outer_wrap()
        },
    ] {
        reset_peak_rss();
        let hiding = prove_hiding(params, &layer.circuit, &layer.traces);
        report(
            &format!("hiding layer 2 ({params:?})"),
            proof_bytes(&hiding.proof),
            hiding.prepare,
            hiding.prove,
            &hiding.proof.proof.degree_bits,
        );
    }
}
