# Fork notes

This is a fork of [Plonky3-recursion](https://github.com/Plonky3/Plonky3-recursion),
kept on the `starkunsat` branch of
`The-Ashwin-Karthikeyan/Plonky3-recursion`.

## Purpose

The fork adds what the lrup recursion project needs from the library:
recursion over **Goldilocks with the cubic trinomial extension** (`D = 3`,
`X^3 = X + 1`) and **Poseidon2 width 12** (`W12`) hashing. Upstream supports
Goldilocks only at `D = 2` / Poseidon2 width 8, and its only non-binomial
extension is KoalaBear's quintic trinomial.

Each change is one work package, kept small and rebasable: no reformatting of
untouched code, upstream style mirrored, and generic changes kept suitable for
upstream pull requests.

## Upstream base

- Upstream: <https://github.com/Plonky3/Plonky3-recursion>
- Base commit: `3a69ba61f713c8400b14eb3d8f0e52caa13512c7`

## License

Unchanged. The fork stays dual-licensed under MIT or Apache-2.0, like upstream
(`LICENSE-MIT`, `LICENSE-APACHE`). Fork changes are contributed under the same
terms.

## Changelog

### WP1: cubic trinomial ALU and reduction kind

**What changed.**

- `circuit-prover/src/air/alu_air.rs`: new `AluExtMulKind::CubicTrinomial`
  (`D = 3`, `X^3 - X - 1`). `ext_mul_cubic_trinomial` builds the constraint by
  calling `p3_field::extension::trinomial_cubic_mul` on the AIR expression type,
  the same routine native `CubicTrinomialExtensionField` multiplication uses.
  New constructors `new_cubic_trinomial` and
  `new_cubic_trinomial_with_preprocessed`, a dispatch arm in `eval`, and the
  debug asserts. Constraint degree is unchanged (3).
- `AluExtMulKind` helpers: `has_trinomial(d)`, `resolve` generalised (see
  below), `w_and_trinomial()` (the inverse of `resolve`, replacing five copies of
  the same match), and `is_canonical_for_degree(d)`.
- The proof flag `alu_quintic_trinomial` now means "the trinomial reduction for
  this degree" (`D = 3`: cubic, `D = 5`: quintic). The field and its serde name
  are unchanged, so existing serialized proofs and artifacts still parse and
  mean the same thing. `resolve(d, w, flag)` returns the cubic trinomial for
  `d = 3`, the quintic for `d = 5`, and `None` for the flag at any other degree
  (previously the flag was masked with `D == 5 &&` at every call site and
  ignored elsewhere).
- `circuit-prover/src/field_params.rs`: `ExtractBinomialW` for
  `CubicTrinomialExtensionField<F: CubicTrinomialExtendable>` (`w = None`,
  trinomial). The trait method `alu_is_quintic_trinomial` is renamed
  `alu_is_trinomial`.
- The `D == 5 && flag` guards (`common.rs`, `batch_stark_prover.rs`,
  `recursion/src/verifier/batch_stark.rs`) now pass the flag straight to
  `resolve`.
- Tightened validators: the trusted built-in artifact import
  (`batch_stark_prover.rs`) and the artifact relation descriptor
  (`recursion/src/artifact/descriptor.rs`) accept only the canonical reduction
  per degree, so a binomial relation is rejected at `D = 3` (Goldilocks has no
  binomial cubic) as well as `D = 5`. The descriptor previously accepted a
  binomial at `D = 5`.
- In-circuit verifier (`create_alu_air`): the proof-controlled flag must equal
  the verifier field's `alu_is_trinomial()`, so a proof cannot swap a binomial
  relation for a trinomial one.
- Artifact wire format: the cubic trinomial is reduction tag `3` (tags 0, 1 and
  2 are unchanged).
- Tests: a Goldilocks D3 assurance test against native arithmetic, negatives for
  a mutated `out` and for a binomial-reduced product, a constraint-degree check,
  the shape golden, `field_params`, `resolve`, and rejection of binomial
  relations at `D = 3` in both validators.

**Why.** The ALU is the first piece of Goldilocks D3 support. Degree-3 dispatch
in circuit-prover, the W12 Poseidon2 table and the recursion backend come in
later packages, so a full D3 batch proof is not possible yet.

**Upstreamable.** Yes. The change is generic: it adds a reduction kind for any
field implementing `CubicTrinomialExtendable` and does not change behaviour for
existing degrees, apart from rejecting relations that were already unusable (a
binomial at `D = 5` in the descriptor, the trinomial flag at a degree without a
trinomial).

### WP2: degree-3 dispatch in circuit-prover

**What changed.**

- `circuit-prover/src/batch_stark_prover.rs`: `D = 3` is accepted by
  `BatchStarkProof::validate`, by the public
  `CircuitVerifier::from_independently_trusted_builtin_artifact` (which returned
  `UnsupportedDegree` for 3) and by `dispatch_by_ext_degree!`, the single degree
  list behind `prove_all_tables`, the prepared prover and `verify_all_tables`.
  The `UnsupportedDegree` / `UnsupportedExtDegree` messages list the new degree.
- The non-primitive dispatch in `prove` gets a `3 =>` arm that reinterprets
  `Traces<EF>` as `Traces<CubicTrinomialExtensionField<Val>>`. Unlike the other
  arms it checks the type first: unless `EF` is exactly that field (`TypeId`
  equality, and `EF::DIMENSION == 3`), it returns `RelationMismatch` before the
  `unsafe` cast.
- `circuit-prover/src/common.rs`: `TrustedBuiltinArtifactRelation::try_new`
  accepts `ext_degree == 3`.
- `circuit-prover/src/batch_stark_prover/dynamic_air.rs`:
  `TableProver::batch_instance_d3`, with a default `None` like
  `batch_instance_d5`; `impl_table_prover_batch_instances_from_base!` implements
  it for every table prover built from it (Recompose, Statement, Keccak, BLAKE3).
- `recompose.rs`, `statement.rs`: the Goldilocks preprocessors downcast
  `PreprocessedColumns<CubicTrinomialExtensionField<Goldilocks>, 3>`. The
  Poseidon1/2, Keccak and BLAKE3 preprocessors do not yet (Poseidon2 is WP4).
- Tests: a primitive-only Goldilocks D3 batch proof (Const, Public, ALU with
  MUL, MUL_ADD and a Horner chain over a non-base constant, over a cubic
  challenge field and the Goldilocks W8 MMCS of `config::goldilocks()`), proved and
  verified; the verifier rejects the wrong field, a flipped trinomial flag and a
  stray `w`. A tampered MUL output coefficient and a tampered public value are
  both rejected. Also the trusted path (`prepare_circuit`, `CircuitVerifier::verify`,
  the built-in artifact import at D3) and Recompose with coefficient lookups plus
  Statement at D3.

**Why.** With the cubic ALU from WP1, this lets circuit-prover prove and verify
its primitive tables, Recompose and Statement over Goldilocks D3. The Poseidon2
W12 table (WP4) and the recursion backend (WP5) are still missing, so in-circuit
verification at D3 is not possible yet.

**Upstreamable.** Yes. Degree 3 joins the supported list for any field
implementing `CubicTrinomialExtendable`. Behaviour at the existing degrees is
unchanged, and the new trait method has a default.
