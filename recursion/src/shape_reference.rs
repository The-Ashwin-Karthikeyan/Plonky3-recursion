//! Shape references: structurally canonical proofs synthesized from trusted metadata alone.
//!
//! A recursive verifier's target allocation depends only on the *shape* of the proof it is
//! built from (opened-value widths, commitment and query counts, FRI rounds and arities, final
//! polynomial length, table metadata), never on its values: that is the contract of
//! [`crate::PreparedRecursive`]. Every one of those dimensions is a function of the verifying
//! key (the trusted AIRs, their degree bits, the lookups, the preprocessed metadata and the
//! PCS parameters). This module builds a proof with exactly those dimensions and every value
//! zero, so a parent circuit can be built from a child's verifying key without any proof of
//! the child.
//!
//! The synthesized proof is not valid and is never verified: it is only ever passed to the
//! shape-only trusted entry points
//! ([`crate::TrustedPcsRecursionBackend::capture_trusted_batch_shape_contract`],
//! [`crate::TrustedPcsRecursionBackend::build_trusted_batch_verifier_circuit_from_shape`]),
//! which run every structural check the reference path runs and skip only the reference's
//! native verification.
//!
//! Merkle multiproofs are left empty: their length depends on the queried indices (shared
//! siblings are deduplicated), they are not part of any allocation shape, and the in-circuit
//! Merkle paths are private run-time data restored from the real proof.

use alloc::string::ToString;
use alloc::vec;
use alloc::vec::Vec;

use p3_batch_stark::common::GlobalPreprocessed;
use p3_batch_stark::proof::OpenedValuesWithLookups;
use p3_batch_stark::{BatchCommitments, BatchOpenedValues, BatchProof, CommonData};
use p3_circuit_prover::batch_stark_prover::{
    BatchStarkProof, CircuitVerifier, NUM_PRIMITIVE_TABLES, NonPrimitiveTableEntry,
    lookups_for_circuit_table_air,
};
use p3_circuit_prover::field_params::ExtractBinomialW;
use p3_commit::{Mmcs, Pcs, UnivariateStarkPcs};
use p3_field::{Algebra, ExtensionField, Field, PrimeCharacteristicRing, PrimeField64};
use p3_fri::{BatchMultiOpening, CommitPhaseMultiStep, FriProof, fold_schedule};
use p3_lookup::logup::LogUpGadget;
use p3_lookup::{Lookup, LookupTerminal};
use p3_merkle_tree::PrunedMerklePaths;
use p3_symmetric::MerkleCap;
use p3_uni_stark::{
    OpenedValues, PreprocessedOpenedValues, SymbolicExpression, SymbolicExpressionExt, Val,
    validate_degree_bits,
};

use crate::backend::fri::FriRecursionConfig;
use crate::input_contract::stark_layout::{
    CommitmentRole, NativeStarkLayout, validate_preprocessed_metadata,
};
use crate::traits::{RecursiveAir, RecursiveLookupGadget, RecursivePcs};
use crate::verifier::{VerificationError, derive_instance_layout, trusted_batch_tables};

fn invalid(message: impl Into<alloc::string::String>) -> VerificationError {
    VerificationError::InvalidProofShape(message.into())
}

/// One committed matrix of a PCS opening, as the FRI proof sees it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FriShapeMatrix {
    /// Opened base-field columns per query (the matrix's committed width).
    pub width: usize,
    /// Log2 of the committed (LDE) height.
    pub log_lde_height: usize,
}

/// The FRI opening proof's dimensions, derived from a trusted layout and the native FRI
/// parameters (what [`FriRecursionConfig::shape_reference_pcs`] fills in).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FriShapeRequest {
    /// Each input commitment's matrices, in transcript (commitment ordinal) order.
    pub input_batches: Vec<Vec<FriShapeMatrix>>,
    /// Queries per round.
    pub num_queries: usize,
    /// Each commit-phase round's log arity (`p3_fri::fold_schedule`).
    pub phase_log_arities: Vec<usize>,
    /// Log2 of the largest committed height: the query index bit length.
    pub index_bit_len: usize,
    /// Coefficients of the final polynomial.
    pub final_poly_len: usize,
}

impl FriShapeRequest {
    /// Log2 of each commit-phase round's tree height (rows of `2^arity` siblings).
    pub fn phase_log_heights(&self) -> Vec<usize> {
        let mut current = self.index_bit_len;
        self.phase_log_arities
            .iter()
            .map(|&arity| {
                current -= arity;
                current
            })
            .collect()
    }
}

/// A config's PCS parts of a shape reference: one commitment per input commitment ordinal (the
/// preprocessed ordinal's is ignored: the verifying key supplies the real one) and the opening
/// proof.
pub struct FriShapeParts<Commitment, Proof> {
    pub input_commitments: Vec<Commitment>,
    pub opening_proof: Proof,
}

/// [`FriShapeParts`] for the Merkle-tree FRI PCS (`TwoAdicFriPcs` over `MerkleTreeMmcs` and its
/// `ExtensionMmcs`), with a cap of `2^min(cap_height, tree height)` zero roots per tree, zero
/// opened values and sibling rows, empty multiproofs and zero proof-of-work witnesses.
#[allow(clippy::type_complexity)]
pub fn merkle_fri_shape_parts<F, EF, IM, FM, const DIGEST_ELEMS: usize>(
    request: &FriShapeRequest,
    cap_height: usize,
) -> FriShapeParts<
    MerkleCap<F, [F; DIGEST_ELEMS]>,
    FriProof<EF, FM, F, Vec<BatchMultiOpening<F, IM>>>,
>
where
    F: Field,
    EF: ExtensionField<F>,
    IM: Mmcs<
            F,
            Commitment = MerkleCap<F, [F; DIGEST_ELEMS]>,
            MultiProof = PrunedMerklePaths<F, DIGEST_ELEMS>,
        >,
    FM: Mmcs<
            EF,
            Commitment = MerkleCap<F, [F; DIGEST_ELEMS]>,
            MultiProof = PrunedMerklePaths<F, DIGEST_ELEMS>,
        >,
{
    let cap = |tree_log_height: usize| {
        MerkleCap::new(vec![
            [F::ZERO; DIGEST_ELEMS];
            1 << cap_height.min(tree_log_height)
        ])
    };
    let empty = || PrunedMerklePaths {
        sibling_hashes: Vec::new(),
    };
    let input_commitments = request
        .input_batches
        .iter()
        .map(|batch| cap(batch.iter().map(|m| m.log_lde_height).max().unwrap_or(0)))
        .collect();
    let input_openings = request
        .input_batches
        .iter()
        .map(|batch| BatchMultiOpening {
            opened_values: vec![
                batch
                    .iter()
                    .map(|m| vec![F::ZERO; m.width])
                    .collect::<Vec<_>>();
                request.num_queries
            ],
            opening_proof: empty(),
        })
        .collect();
    let rounds = request.phase_log_arities.len();
    let opening_proof = FriProof {
        batch_pow_witness: F::ZERO,
        commit_phase_commits: request.phase_log_heights().into_iter().map(cap).collect(),
        commit_pow_witnesses: vec![F::ZERO; rounds],
        input_openings,
        commit_phase_openings: request
            .phase_log_arities
            .iter()
            .map(|&arity| CommitPhaseMultiStep {
                sibling_values: vec![vec![EF::ZERO; (1 << arity) - 1]; request.num_queries],
                opening_proof: empty(),
            })
            .collect(),
        final_poly: vec![EF::ZERO; request.final_poly_len],
        query_pow_witness: F::ZERO,
    };
    FriShapeParts {
        input_commitments,
        opening_proof,
    }
}

/// A zero-valued batch-STARK proof of `airs` at `degree_bits` (extended, as a proof carries
/// them) under `config`, with exactly the shape the native prover outputs: the opened-value
/// widths and quotient chunk counts of [`crate::verifier::batch_stark`]'s trusted layout, one
/// permutation commitment iff any AIR has lookups, a lookup terminal per AIR with lookups, and
/// the FRI proof of [`FriRecursionConfig::shape_reference_pcs`]. `lookups` must come from the
/// trusted AIRs. Non-hiding configs only.
pub fn batch_proof_shape_reference<SC, A, LG>(
    config: &SC,
    airs: &[A],
    degree_bits: &[usize],
    common: &CommonData<SC>,
    lookups: &[Vec<Lookup<Val<SC>>>],
    lookup_gadget: &LG,
) -> Result<BatchProof<SC>, VerificationError>
where
    SC: FriRecursionConfig,
    SC::Pcs: RecursivePcs<
            SC,
            SC::InputProof,
            SC::OpeningProof,
            SC::Commitment,
            <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Domain,
        >,
    A: RecursiveAir<Val<SC>, SC::Challenge, LG>,
    LG: RecursiveLookupGadget<SC::Challenge>,
    Val<SC>: PrimeField64,
    SC::Challenge: ExtensionField<Val<SC>> + PrimeCharacteristicRing,
{
    if SC::Pcs::ZK || config.is_zk() != 0 {
        return Err(invalid(
            "shape references are synthesized for non-hiding configs only",
        ));
    }
    let native = config
        .native_fri_validation_params()
        .ok_or_else(|| invalid("shape references need native FRI validation parameters"))?;
    let count = airs.len();
    if count == 0 || degree_bits.len() != count || lookups.len() != count {
        return Err(invalid("shape reference cardinality mismatch"));
    }
    for (index, &degree) in degree_bits.iter().enumerate() {
        validate_degree_bits(
            Some(index),
            degree,
            0,
            config.pcs().log_min_trace_height(),
            config.pcs().log_max_trace_height(),
        )
        .map_err(|error| invalid(error.to_string()))?;
    }
    if let Some(global) = &common.preprocessed {
        let metadata = global
            .instances
            .iter()
            .map(|entry| {
                entry
                    .as_ref()
                    .map(|meta| (meta.matrix_index, meta.width, meta.degree_bits))
            })
            .collect::<Vec<_>>();
        validate_preprocessed_metadata(&metadata, &global.matrix_to_instance, degree_bits)
            .map_err(|error| invalid(error.to_string()))?;
    }
    let pre_width = |index: usize| {
        common
            .preprocessed
            .as_ref()
            .and_then(|global| global.instances[index].as_ref().map(|meta| meta.width))
            .unwrap_or(0)
    };
    let instances = airs
        .iter()
        .zip(degree_bits)
        .zip(lookups)
        .enumerate()
        .map(|(index, ((air, &ext_log), lookup_set))| {
            derive_instance_layout(
                config,
                air,
                ext_log,
                pre_width(index),
                lookup_set,
                lookup_gadget,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let has_permutation = instances.iter().any(|i| i.permutation_width != 0);
    let layout = NativeStarkLayout::new(
        instances.clone(),
        common
            .preprocessed
            .as_ref()
            .map_or(&[][..], |global| global.matrix_to_instance.as_slice()),
        false,
        common.preprocessed.is_some(),
        has_permutation,
    )
    .map_err(|error| invalid(error.to_string()))?;

    // The FRI proof's dimensions, exactly as the context validator expects them.
    let log_blowup = native.log_blowup();
    let view = layout.opening_view();
    let input_batches: Vec<Vec<FriShapeMatrix>> = (0..view.commitment_count())
        .map(|ordinal| {
            view.matrices(ordinal)
                .map(|m| FriShapeMatrix {
                    width: m.width(),
                    log_lde_height: m.log_height() + log_blowup,
                })
                .collect()
        })
        .collect();
    let mut heights: Vec<usize> = input_batches
        .iter()
        .flatten()
        .map(|m| m.log_lde_height)
        .collect();
    heights.sort_unstable_by(|a, b| b.cmp(a));
    heights.dedup();
    let index_bit_len = *heights
        .first()
        .ok_or_else(|| invalid("shape reference has no committed matrix"))?;
    let log_final_height = log_blowup + native.log_final_poly_len();
    if index_bit_len < log_final_height {
        return Err(invalid(
            "committed heights are below the final polynomial's",
        ));
    }
    let request = FriShapeRequest {
        input_batches,
        num_queries: native.num_queries(),
        phase_log_arities: fold_schedule(&heights, log_final_height, native.max_log_arity()),
        index_bit_len,
        final_poly_len: 1 << native.log_final_poly_len(),
    };
    let FriShapeParts {
        input_commitments,
        opening_proof,
    } = config.shape_reference_pcs(&request)?;
    if input_commitments.len() != view.commitment_count() {
        return Err(invalid("shape reference PCS commitment count mismatch"));
    }
    let take = |role: CommitmentRole| {
        let ordinal = (0..view.commitment_count())
            .find(|&o| layout.commitment_role(o) == Some(role))
            .expect("the layout has this role");
        input_commitments[ordinal].clone()
    };
    let commitments = BatchCommitments {
        main: take(CommitmentRole::Trace),
        permutation: has_permutation.then(|| take(CommitmentRole::Permutation)),
        quotient_chunks: take(CommitmentRole::Quotient),
        random: None,
    };

    let zeros = |n: usize| vec![SC::Challenge::ZERO; n];
    let opened = instances
        .iter()
        .enumerate()
        .map(|(index, i)| OpenedValuesWithLookups {
            base_opened_values: OpenedValues {
                trace_local: zeros(i.trace_width),
                trace_next: i.trace_next.then(|| zeros(i.trace_width)),
                preprocessed: common
                    .preprocessed
                    .as_ref()
                    .and_then(|global| global.instances[index].as_ref())
                    .map(|meta| PreprocessedOpenedValues {
                        local: zeros(meta.width),
                        next: i.pre_next.then(|| zeros(meta.width)),
                    }),
                quotient_chunks: vec![zeros(i.challenge_width); i.quotient_chunks],
                random: None,
            },
            permutation_local: zeros(i.permutation_width),
            permutation_next: zeros(i.permutation_width),
        })
        .collect();
    let lookup_terminals = airs
        .iter()
        .enumerate()
        .map(|(index, air)| {
            air.declares_interactions(pre_width(index))
                .then_some(LookupTerminal(SC::Challenge::ZERO))
        })
        .collect();
    let any_lookup = lookups.iter().any(|set| !set.is_empty());
    Ok(BatchProof {
        commitments,
        opened_values: BatchOpenedValues { instances: opened },
        opening_proof,
        lookup_terminals,
        degree_bits: degree_bits.to_vec(),
        lookup_pow_witness: any_lookup.then_some(Val::<SC>::ZERO),
        ood_pow_witness: Val::<SC>::ZERO,
    })
}

/// The shape reference of a recursion-layer proof of `verifier`'s circuit, with a zero statement
/// of the right length: every dimension comes from the verifier (its relation's tables, heights,
/// packing and non-primitive manifest; its common data; its config's FRI parameters).
pub fn trusted_batch_shape_reference<SC>(
    verifier: &CircuitVerifier<SC>,
) -> Result<(BatchStarkProof<SC>, Vec<Val<SC>>), VerificationError>
where
    SC: FriRecursionConfig + 'static,
    SC::Pcs: RecursivePcs<
            SC,
            SC::InputProof,
            SC::OpeningProof,
            SC::Commitment,
            <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Domain,
        >,
    Val<SC>: PrimeField64 + p3_circuit_prover::config::StarkField,
    SC::Challenge: ExtensionField<Val<SC>> + PrimeCharacteristicRing + ExtractBinomialW<Val<SC>>,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    let relation = verifier.relation();
    let statement = vec![Val::<SC>::ZERO; verifier.statement_layout().schema().base_len()];
    let proof = match relation.ext_degree() {
        1 => layer_proof::<SC, 1>(verifier, &statement)?,
        2 => layer_proof::<SC, 2>(verifier, &statement)?,
        3 => layer_proof::<SC, 3>(verifier, &statement)?,
        4 => layer_proof::<SC, 4>(verifier, &statement)?,
        5 => layer_proof::<SC, 5>(verifier, &statement)?,
        degree => {
            return Err(invalid(alloc::format!(
                "unsupported trusted batch verifier ext_degree {degree}"
            )));
        }
    };
    let public_values = verifier
        .table_public_values(&statement)
        .map_err(|error| invalid(error.to_string()))?;
    let (w_binomial, alu_quintic_trinomial) = relation.reduction().w_and_trinomial();
    let non_primitives = relation
        .non_primitives()
        .iter()
        .zip(public_values.into_iter().skip(NUM_PRIMITIVE_TABLES))
        .map(|(entry, public_values)| NonPrimitiveTableEntry {
            op_type: entry.op_type().clone(),
            rows: entry.rows(),
            lanes: entry.lanes(),
            public_values,
            air_variant: entry.air_variant(),
        })
        .collect();
    Ok((
        BatchStarkProof {
            proof,
            table_packing: relation.table_packing().clone(),
            rows: *relation.rows(),
            alu_variant: relation.alu_variant(),
            ext_degree: relation.ext_degree(),
            w_binomial,
            alu_quintic_trinomial,
            non_primitives,
            stark_common: clone_common(verifier.common_data()),
        },
        statement,
    ))
}

fn layer_proof<SC, const TRACE_D: usize>(
    verifier: &CircuitVerifier<SC>,
    statement: &[Val<SC>],
) -> Result<BatchProof<SC>, VerificationError>
where
    SC: FriRecursionConfig + 'static,
    SC::Pcs: RecursivePcs<
            SC,
            SC::InputProof,
            SC::OpeningProof,
            SC::Commitment,
            <SC::Pcs as Pcs<SC::Challenge, SC::Challenger>>::Domain,
        >,
    Val<SC>: PrimeField64 + p3_circuit_prover::config::StarkField,
    SC::Challenge: ExtensionField<Val<SC>> + PrimeCharacteristicRing + ExtractBinomialW<Val<SC>>,
    SymbolicExpressionExt<Val<SC>, SC::Challenge>:
        Algebra<SymbolicExpression<Val<SC>>> + Algebra<SC::Challenge>,
{
    let config = verifier.config();
    let tables = trusted_batch_tables::<SC, TRACE_D>(verifier, statement)?;
    let lookups = tables
        .airs
        .iter()
        .zip(&tables.trace_lens)
        .map(|(air, &trace_len)| {
            lookups_for_circuit_table_air::<SC, TRACE_D>(
                &air.to_table_air(),
                trace_len,
                config.is_zk(),
            )
            .to_vec()
        })
        .collect::<Vec<_>>();
    batch_proof_shape_reference(
        config,
        &tables.airs,
        verifier.relation().trace_degree_bits(),
        verifier.common_data(),
        &lookups,
        &LogUpGadget,
    )
}

/// `CommonData` is not `Clone`; every field is.
fn clone_common<SC: p3_uni_stark::StarkGenericConfig>(common: &CommonData<SC>) -> CommonData<SC> {
    CommonData {
        preprocessed: common
            .preprocessed
            .as_ref()
            .map(|global| GlobalPreprocessed {
                commitment: global.commitment.clone(),
                instances: global.instances.clone(),
                matrix_to_instance: global.matrix_to_instance.clone(),
            }),
        lookups: common.lookups.clone(),
    }
}

/// `proof` with every value zero and every Merkle multiproof empty: what a proof looks like to
/// target allocation. A shape reference equals the zeroed form of every real proof of its
/// verifier (the multiproofs excepted, whose length depends on the queried indices); tests
/// compare the two byte for byte. Merkle-tree FRI configs ([`merkle_fri_shape_parts`]).
pub fn zeroed_batch_proof<SC, IM, FM, const DIGEST_ELEMS: usize>(
    proof: &BatchProof<SC>,
) -> BatchProof<SC>
where
    SC: p3_uni_stark::StarkGenericConfig,
    SC::Pcs: Pcs<
            SC::Challenge,
            SC::Challenger,
            Commitment = MerkleCap<Val<SC>, [Val<SC>; DIGEST_ELEMS]>,
            Proof = FriProof<SC::Challenge, FM, Val<SC>, Vec<BatchMultiOpening<Val<SC>, IM>>>,
        >,
    IM: Mmcs<
            Val<SC>,
            Commitment = MerkleCap<Val<SC>, [Val<SC>; DIGEST_ELEMS]>,
            MultiProof = PrunedMerklePaths<Val<SC>, DIGEST_ELEMS>,
        >,
    FM: Mmcs<
            SC::Challenge,
            Commitment = MerkleCap<Val<SC>, [Val<SC>; DIGEST_ELEMS]>,
            MultiProof = PrunedMerklePaths<Val<SC>, DIGEST_ELEMS>,
        >,
{
    let f0 = Val::<SC>::ZERO;
    let e0 = SC::Challenge::ZERO;
    let cap = |c: &MerkleCap<Val<SC>, [Val<SC>; DIGEST_ELEMS]>| {
        MerkleCap::new(vec![[f0; DIGEST_ELEMS]; c.num_roots()])
    };
    let ext = |v: &Vec<SC::Challenge>| vec![e0; v.len()];
    let empty = || PrunedMerklePaths {
        sibling_hashes: Vec::new(),
    };
    let c = &proof.commitments;
    let o = &proof.opening_proof;
    BatchProof {
        commitments: BatchCommitments {
            main: cap(&c.main),
            permutation: c.permutation.as_ref().map(cap),
            quotient_chunks: cap(&c.quotient_chunks),
            random: c.random.as_ref().map(cap),
        },
        opened_values: BatchOpenedValues {
            instances: proof
                .opened_values
                .instances
                .iter()
                .map(|i| {
                    let b = &i.base_opened_values;
                    OpenedValuesWithLookups {
                        base_opened_values: OpenedValues {
                            trace_local: ext(&b.trace_local),
                            trace_next: b.trace_next.as_ref().map(ext),
                            preprocessed: b.preprocessed.as_ref().map(|p| {
                                PreprocessedOpenedValues {
                                    local: ext(&p.local),
                                    next: p.next.as_ref().map(ext),
                                }
                            }),
                            quotient_chunks: b.quotient_chunks.iter().map(ext).collect(),
                            random: b.random.as_ref().map(ext),
                        },
                        permutation_local: ext(&i.permutation_local),
                        permutation_next: ext(&i.permutation_next),
                    }
                })
                .collect(),
        },
        opening_proof: FriProof {
            batch_pow_witness: f0,
            commit_phase_commits: o.commit_phase_commits.iter().map(cap).collect(),
            commit_pow_witnesses: vec![f0; o.commit_pow_witnesses.len()],
            input_openings: o
                .input_openings
                .iter()
                .map(|batch| BatchMultiOpening {
                    opened_values: batch
                        .opened_values
                        .iter()
                        .map(|q| q.iter().map(|row| vec![f0; row.len()]).collect())
                        .collect(),
                    opening_proof: empty(),
                })
                .collect(),
            commit_phase_openings: o
                .commit_phase_openings
                .iter()
                .map(|step| CommitPhaseMultiStep {
                    sibling_values: step.sibling_values.iter().map(ext).collect(),
                    opening_proof: empty(),
                })
                .collect(),
            final_poly: ext(&o.final_poly),
            query_pow_witness: f0,
        },
        lookup_terminals: proof
            .lookup_terminals
            .iter()
            .map(|t| t.as_ref().map(|_| LookupTerminal(e0)))
            .collect(),
        degree_bits: proof.degree_bits.clone(),
        lookup_pow_witness: proof.lookup_pow_witness.map(|_| f0),
        ood_pow_witness: f0,
    }
}

/// [`zeroed_batch_proof`] of a recursion-layer proof, with the Statement table's values (the
/// entry at `statement_instance`, a table index) zeroed too and the rest of the metadata kept.
pub fn zeroed_batch_stark_proof<SC, IM, FM, const DIGEST_ELEMS: usize>(
    proof: &BatchStarkProof<SC>,
    statement_instance: Option<usize>,
) -> BatchStarkProof<SC>
where
    SC: p3_uni_stark::StarkGenericConfig,
    SC::Pcs: Pcs<
            SC::Challenge,
            SC::Challenger,
            Commitment = MerkleCap<Val<SC>, [Val<SC>; DIGEST_ELEMS]>,
            Proof = FriProof<SC::Challenge, FM, Val<SC>, Vec<BatchMultiOpening<Val<SC>, IM>>>,
        >,
    IM: Mmcs<
            Val<SC>,
            Commitment = MerkleCap<Val<SC>, [Val<SC>; DIGEST_ELEMS]>,
            MultiProof = PrunedMerklePaths<Val<SC>, DIGEST_ELEMS>,
        >,
    FM: Mmcs<
            SC::Challenge,
            Commitment = MerkleCap<Val<SC>, [Val<SC>; DIGEST_ELEMS]>,
            MultiProof = PrunedMerklePaths<Val<SC>, DIGEST_ELEMS>,
        >,
{
    BatchStarkProof {
        proof: zeroed_batch_proof::<SC, IM, FM, DIGEST_ELEMS>(&proof.proof),
        table_packing: proof.table_packing.clone(),
        rows: proof.rows,
        alu_variant: proof.alu_variant,
        ext_degree: proof.ext_degree,
        w_binomial: proof.w_binomial,
        alu_quintic_trinomial: proof.alu_quintic_trinomial,
        non_primitives: proof
            .non_primitives
            .iter()
            .enumerate()
            .map(|(index, entry)| NonPrimitiveTableEntry {
                op_type: entry.op_type.clone(),
                rows: entry.rows,
                lanes: entry.lanes,
                public_values: if statement_instance == Some(NUM_PRIMITIVE_TABLES + index) {
                    vec![Val::<SC>::ZERO; entry.public_values.len()]
                } else {
                    entry.public_values.clone()
                },
                air_variant: entry.air_variant,
            })
            .collect(),
        stark_common: clone_common(&proof.stark_common),
    }
}

#[cfg(test)]
mod tests {
    use alloc::boxed::Box;
    use alloc::string::String;
    use alloc::vec::Vec;
    use alloc::{format, vec};

    use p3_circuit::{Circuit, CircuitBuilder, StatementExport};
    use p3_circuit_prover::batch_stark_prover::{
        BatchStarkProver, StatementAirBuilder, StatementPreprocessor, StatementProver,
    };
    use p3_circuit_prover::common::{NpoAirBuilder, NpoPreprocessor};
    use p3_circuit_prover::{ConstraintProfile, PreparedCircuitProver};
    use p3_test_utils::koala_bear_params::{Challenge, F};

    use super::*;
    use crate::prepared::input::compare_input_contract;
    use crate::prepared::test_common::{
        KoalaBearD4Backend, KoalaBearD4RecursionConfig,
        koala_bear_d4_recursion_config_and_backend_with_pow_bits,
    };
    use crate::{
        BatchOnly, PcsRecursionBackend, PreparedPcsRecursionBackend, RecursionInput,
        TrustedPcsRecursionBackend, VerifierCircuitResult,
    };

    type Cfg = KoalaBearD4RecursionConfig;
    type Backend = KoalaBearD4Backend;
    type Result_ = <Backend as PcsRecursionBackend<Cfg, BatchOnly, 4>>::VerifierResult;
    type Contract = <Backend as PreparedPcsRecursionBackend<Cfg, BatchOnly, 4>>::InputContract;

    /// A child circuit: `inputs` public inputs, the first squared `squarings` times; the
    /// statement is the inputs then the last square.
    struct Child {
        circuit: Circuit<Challenge>,
        prepared: PreparedCircuitProver<Cfg>,
        squarings: usize,
    }

    impl Child {
        fn new(config: &Cfg, inputs: usize, squarings: usize) -> Self {
            let mut builder = CircuitBuilder::<Challenge>::new();
            let xs: Vec<_> = (0..inputs).map(|_| builder.public_input()).collect();
            let mut y = xs[0];
            for _ in 0..squarings {
                y = builder.mul(y, y);
            }
            let mut exports: Vec<StatementExport> =
                xs.iter().map(|&x| StatementExport::Base(x)).collect();
            exports.push(StatementExport::Base(y));
            let schema = builder.set_statement_exports::<F>(&exports).unwrap();
            let circuit = builder.build().unwrap();
            let preprocessors: Vec<Box<dyn NpoPreprocessor<F>>> =
                vec![Box::new(StatementPreprocessor::new(schema.clone()))];
            let air_builders: Vec<Box<dyn NpoAirBuilder<Cfg, 4>>> =
                vec![Box::new(StatementAirBuilder::<4>::new(schema.clone()))];
            let mut prover = BatchStarkProver::new(config.clone());
            prover.register_table_prover(Box::new(StatementProver::<4>::new(schema)));
            let prepared = prover
                .prepare_circuit::<Challenge, 4>(
                    &circuit,
                    &preprocessors,
                    &air_builders,
                    ConstraintProfile::Standard,
                )
                .unwrap();
            Self {
                circuit,
                prepared,
                squarings,
            }
        }

        fn prove(&self, values: &[u64]) -> (BatchStarkProof<Cfg>, Vec<F>) {
            let values: Vec<F> = values.iter().copied().map(F::from_u64).collect();
            let mut y = values[0];
            for _ in 0..self.squarings {
                y = y * y;
            }
            let mut runner = self.circuit.runner();
            let public: Vec<Challenge> = values.iter().copied().map(Challenge::from).collect();
            runner.set_public_inputs(&public).unwrap();
            let proof = self.prepared.prove(&runner.run().unwrap()).unwrap();
            let mut statement = values;
            statement.push(y);
            (proof, statement)
        }

        fn verifier(&self) -> CircuitVerifier<Cfg> {
            self.prepared.verifier()
        }
    }

    /// Everything a circuit's layout and constants depend on.
    fn fingerprint(c: &Circuit<Challenge>) -> String {
        let mut tags: Vec<_> = c.tag_to_witness.iter().collect();
        tags.sort();
        let mut op_tags: Vec<_> = c.tag_to_op_id.iter().collect();
        op_tags.sort();
        format!(
            "{} {:?} {:?} {} {:?} {} {:?} {:?} {:?} {:?}",
            c.witness_count,
            c.ops,
            c.public_rows,
            c.public_flat_len,
            c.private_input_rows,
            c.private_flat_len,
            c.non_primitive_trace_generator_order,
            tags,
            op_tags,
            c.statement_schema(),
        )
    }

    /// A parent circuit over one child slot, pinned to `verifier`, built from `reference` or (with
    /// `None`) from the verifier's shape alone.
    fn parent(
        backend: &Backend,
        verifier: &CircuitVerifier<Cfg>,
        reference: Option<(&BatchStarkProof<Cfg>, &[F])>,
    ) -> Result<(Circuit<Challenge>, Result_), VerificationError> {
        let mut b = CircuitBuilder::<Challenge>::new();
        PcsRecursionBackend::<Cfg, BatchOnly, 4>::prepare_circuit(
            backend,
            verifier.config(),
            &mut b,
        )?;
        let result = match reference {
            Some((proof, statement)) => {
                <Backend as TrustedPcsRecursionBackend<Cfg, BatchOnly, 4>>::build_trusted_batch_verifier_circuit(
                    backend, verifier, proof, statement, &mut b,
                )?
            }
            None => <Backend as TrustedPcsRecursionBackend<Cfg, BatchOnly, 4>>::build_trusted_batch_verifier_circuit_from_shape(
                backend, verifier, &mut b,
            )?,
        };
        <Backend as TrustedPcsRecursionBackend<Cfg, BatchOnly, 4>>::constrain_trusted_preprocessing(
            backend,
            &mut b,
            &result,
            verifier.common_data().preprocessed.as_ref().map(|g| &g.commitment),
        )?;
        Ok((b.build().unwrap(), result))
    }

    fn contracts(
        backend: &Backend,
        verifier: &CircuitVerifier<Cfg>,
        proof: &BatchStarkProof<Cfg>,
        statement: &[F],
    ) -> (Contract, Contract) {
        let reference = <Backend as TrustedPcsRecursionBackend<Cfg, BatchOnly, 4>>::capture_trusted_batch_input_contract(
            backend, verifier, proof, statement,
        )
        .unwrap();
        let shape = <Backend as TrustedPcsRecursionBackend<Cfg, BatchOnly, 4>>::capture_trusted_batch_shape_contract(
            backend, verifier,
        )
        .unwrap();
        (reference, shape)
    }

    /// The shape path builds exactly the reference path's circuit and contract, for two child
    /// circuits of different shapes, and the shape-built parent runs on the real child.
    #[test]
    fn shape_path_equals_reference_path() {
        let (config, backend) = koala_bear_d4_recursion_config_and_backend_with_pow_bits(0);
        for (inputs, squarings, values) in [(2, 0, vec![7, 9]), (3, 40, vec![3, 5, 11])] {
            let child = Child::new(&config, inputs, squarings);
            let verifier = child.verifier();
            let (proof, statement) = child.prove(&values);
            verifier.verify(&proof, &statement).unwrap();

            let (reference, shape) = contracts(&backend, &verifier, &proof, &statement);
            compare_input_contract(&reference, &shape).unwrap();

            let (from_reference, _) =
                parent(&backend, &verifier, Some((&proof, &statement))).unwrap();
            let (from_shape, result) = parent(&backend, &verifier, None).unwrap();
            assert_eq!(fingerprint(&from_reference), fingerprint(&from_shape));

            // The real child validates against the shape contract and runs in the shape-built
            // parent.
            <Backend as TrustedPcsRecursionBackend<Cfg, BatchOnly, 4>>::validate_trusted_batch_input(
                &backend, &verifier, &shape, &proof, &statement,
            )
            .unwrap();
            let prev: RecursionInput<'_, Cfg, BatchOnly> = RecursionInput::BatchStark {
                proof: &proof,
                common_data: verifier.common_data(),
                table_public_inputs: verifier.table_public_values(&statement).unwrap(),
            };
            let public = <Result_ as VerifierCircuitResult<Cfg, BatchOnly>>::pack_public_inputs(
                &result, &prev,
            )
            .unwrap();
            let private = <Result_ as VerifierCircuitResult<Cfg, BatchOnly>>::pack_private_inputs(
                &result, &prev,
            )
            .unwrap();
            let mut runner = from_shape.runner();
            runner.set_public_inputs(&public).unwrap();
            runner.set_private_inputs(&private).unwrap();
            <Backend as TrustedPcsRecursionBackend<Cfg, BatchOnly, 4>>::set_private_data_for_trusted_batch(
                &backend,
                &verifier,
                &proof,
                &statement,
                &mut runner,
                <Result_ as VerifierCircuitResult<Cfg, BatchOnly>>::op_ids(&result),
            )
            .unwrap();
            runner.run().unwrap();
        }
    }

    /// The shape reference is exactly a real proof of its verifier with every value zeroed
    /// (and the value-dependent multiproofs emptied), byte for byte, for two child shapes.
    #[test]
    fn shape_reference_equals_a_zeroed_real_proof() {
        use p3_test_utils::koala_bear_params::{ChallengeMmcs, DIGEST_ELEMS, MyMmcs};
        let (config, _) = koala_bear_d4_recursion_config_and_backend_with_pow_bits(0);
        for (inputs, squarings, values) in [(2, 0, vec![7, 9]), (3, 40, vec![3, 5, 11])] {
            let child = Child::new(&config, inputs, squarings);
            let verifier = child.verifier();
            let (real, statement) = child.prove(&values);
            let (synth, zero) = trusted_batch_shape_reference(&verifier).unwrap();
            assert_eq!(zero, vec![F::ZERO; statement.len()]);
            let zeroed = zeroed_batch_stark_proof::<Cfg, MyMmcs, ChallengeMmcs, DIGEST_ELEMS>(
                &real,
                verifier.statement_layout().table_instance(),
            );
            assert_eq!(
                postcard::to_allocvec(&zeroed).unwrap(),
                postcard::to_allocvec(&synth).unwrap(),
                "{inputs} inputs"
            );
            // And the real proof is not trivially zero: the comparison is not vacuous.
            assert_ne!(
                postcard::to_allocvec(&real).unwrap(),
                postcard::to_allocvec(&synth).unwrap()
            );
        }
    }

    /// A contract from another circuit's shape is refused for this circuit's proofs, and a config
    /// that cannot describe its FRI shape is refused on the shape path.
    #[test]
    fn mismatched_shapes_are_refused() {
        let (config, backend) = koala_bear_d4_recursion_config_and_backend_with_pow_bits(0);
        let a = Child::new(&config, 2, 0);
        let b = Child::new(&config, 3, 40);
        let (va, vb) = (a.verifier(), b.verifier());
        let (proof_a, statement_a) = a.prove(&[7, 9]);
        let shape_a = <Backend as TrustedPcsRecursionBackend<Cfg, BatchOnly, 4>>::capture_trusted_batch_shape_contract(&backend, &va).unwrap();
        let shape_b = <Backend as TrustedPcsRecursionBackend<Cfg, BatchOnly, 4>>::capture_trusted_batch_shape_contract(&backend, &vb).unwrap();
        assert!(compare_input_contract(&shape_a, &shape_b).is_err());
        assert!(
            <Backend as TrustedPcsRecursionBackend<Cfg, BatchOnly, 4>>::validate_trusted_batch_input(
                &backend, &va, &shape_b, &proof_a, &statement_a,
            )
            .is_err()
        );
        <Backend as TrustedPcsRecursionBackend<Cfg, BatchOnly, 4>>::validate_trusted_batch_input(
            &backend,
            &va,
            &shape_a,
            &proof_a,
            &statement_a,
        )
        .unwrap();

        // Without native FRI parameters there is no shape to synthesize.
        let blind = Child::new(&config.without_native_fri_snapshot(), 2, 0);
        assert!(trusted_batch_shape_reference(&blind.verifier()).is_err());
        assert!(parent(&backend, &blind.verifier(), None).is_err());
    }
}
