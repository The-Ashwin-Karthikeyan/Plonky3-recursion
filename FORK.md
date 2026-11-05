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

### WP3: Goldilocks D3 / Poseidon2 width-12 configuration

**What changed.**

- `circuit/src/ops/poseidon2_perm/config.rs`: new `Poseidon2Config::GOLDILOCKS_D3_W12`
  (Goldilocks, `D = 3`, width 12, S-box degree 7 with one register, 4 half-full and 22
  partial rounds). The existing geometry rules give an arity-2 shape with four cubic limbs:
  `rate_ext = capacity_ext = 2`, so the rate and the digest are 6 base elements, and binary
  Merkle rows are accepted. Stable names `goldilocks_d3_w12`, `goldilocks_d3_w12_challenger`
  and `goldilocks_d3_w12_shared`, with parsing.
- `circuit/src/ops/poseidon2_perm/trace.rs`: `GoldilocksD3Width12` `Poseidon2Params`, exported
  from `p3_circuit::ops`.
- `circuit/src/builder/circuit_builder.rs`: `enable_poseidon2_perm_width_12`, the width-12
  counterpart of `enable_poseidon2_perm_width_8` (packed cubic limbs, plus the challenger
  table).
- `poseidon2-circuit-air/src/public_types.rs`: the `Poseidon2CircuitAirGoldilocksD3Width12`
  alias, `goldilocks_d3_width12_round_constants`, `goldilocks_d3_width12_default_air` and
  `..._default_air_with_preprocessed`, and the column-split assert.
- Round constants: p3-goldilocks' reference tables, not a seeded RNG.
  `RoundConstants::new(GOLDILOCKS_POSEIDON2_RC_12_EXTERNAL_INITIAL,
  GOLDILOCKS_POSEIDON2_RC_12_INTERNAL, GOLDILOCKS_POSEIDON2_RC_12_EXTERNAL_FINAL)`, so the AIR
  computes exactly `default_goldilocks_poseidon2_12()`. The D2/W8 configuration keeps its
  historical seeded constants.
- `recursion/src/challenger/circuit.rs`: `CircuitChallenger::new_goldilocks_d3()` for the 12/6
  challenger.
- Tests:
  - config geometry and names;
  - a constants and known-answer test (`[0..11]` maps to p3-goldilocks' vector, starting
    `0xf292ab67c0f14b03`) on the native permutation, the AIR trace and an in-circuit
    permutation;
  - the AIR trace matches native on random sponge and Merkle rows, the constraints hold over
    `CubicTrinomialExtensionField<Goldilocks>`, and a tampered output is rejected;
  - constraint degree is the same in every table role;
  - `recursion/tests/goldilocks_d3_w12.rs` executes circuits (no proving) against native p3:
    the leaf sponge vs `PaddingFreeSponge<_, 12, 6, 6>` for widths 1-13, the compression vs
    `TruncatedPermutation<_, 2, 6, 12>` in both directions, mixed-height MMCS openings, and a
    challenger transcript vs `DuplexChallenger<_, _, 12, 6>` (observe, extension observe,
    `sample`, `sample_ext`, `sample_bits`, PoW), with tamper negatives.

**Why.** The circuit side needs Goldilocks Poseidon2 width 12 over the cubic extension: the
permutation, its AIR and its lane geometry. Proving these tables at `D = 3` needs the degree-3
dispatch (WP2) and the Poseidon2 prover integration (WP4).

**Upstreamable.** Yes. It adds one configuration and leaves existing configurations, names and
serialized keys unchanged.

### WP4: Poseidon2 width-12 prover integration at D3

**What changed.**

- `circuit-prover/src/batch_stark_prover/poseidon2.rs`:
  - a `GoldilocksD3Width12` AIR variant with every dispatch arm (trace generation, roles,
    widths, `Clone`, the prover, symbolic and verifier evaluation, preprocessed trace), built
    with `goldilocks_d3_width12_default_air[_with_preprocessed]`. `air_wrapper_for_config`
    and the width lookups handle `GOLDILOCKS_D3_W12`, its challenger table and its shared
    challenger table, so none of them reaches the `unreachable!`/`panic!` fallback.
    Preprocessing uses `extract_preprocessed_from_operations_with_role::<4, 2, ..>` with
    witness scale 3 and Poseidon degree 3, as the D2/W8 shape does with 2.
  - `Poseidon2ProverD3`, the copy of `Poseidon2ProverD2` for degree-3 circuits. It overrides
    `batch_instance_d3` (the trait default is `None`, which would silently drop the table),
    accepts the committed path only at degree 3, and needs `CubicTrinomialExtendable` rather
    than a binomial bound.
  - The D3 downcasts in `Poseidon2Preprocessor` and `Poseidon2SharedPreprocessor`, a `3 =>`
    arm in `poseidon2_config_for_air_builder`, `NpoAirBuilder<SC, 3>` for
    `Poseidon2AirBuilder<3>` and `Poseidon2AirBuilderForConfig<3>`, and no
    `BinomiallyExtendable` bound on `poseidon2_air_try_build`.
  - Casts. The D3 evaluation arms reinterpret the folder as the folder of the new
    `GoldilocksD3W12Config` (not the D2 `GoldilocksConfig`) and the symbolic builder as
    `InteractionSymbolicBuilder<Goldilocks, CubicTrinomialExtensionField<Goldilocks>>`. Each
    first asserts that the builder's base field is Goldilocks and its challenge field is the
    cubic trinomial extension (dimension 3 and `TypeId`), and panics otherwise. Every folder
    field is a function of those two fields only, so after the check the cast renames
    identical types. As for the other variants, the casts are layout-safe only while the
    Poseidon2 AIR emits base-field constraints: it reaches the folder only through
    `AirBuilder`, so the extension-constraint parts are never touched. Each site says so. The
    preprocessed-trace, preprocessed-AIR and trace-materialization casts are over the base
    field and check `Val<SC> == Goldilocks` (`TypeId`).
- `circuit-prover/src/batch_stark_prover.rs`: the three D3 configs in `supported_poseidon2`,
  `RegisterPoseidon2ForExt<3>` (registers `Poseidon2ProverD3`), and
  `poseidon2_table_provers_d3` / `poseidon2_air_builders_d3`.
  `poseidon2_air_builders_for_configs::<_, 3>` works as is.
- `circuit-prover/src/config.rs`: `goldilocks_d3_w12()` and `GoldilocksD3W12Config`:
  `default_goldilocks_poseidon2_12()`, `PaddingFreeSponge<_, 12, 6, 6>`,
  `TruncatedPermutation<_, 2, 6, 12>`, a binary MMCS with cap height 0,
  `DuplexChallenger<_, _, 12, 6>` and the cubic challenge field (lrup's native shape), with
  the benchmark high-arity FRI parameters of the other factories.
- `batch_instance_d3` forwarded by the test wrappers that forward `batch_instance_d5`
  (`recursion/src/prepared/input.rs`, `circuit-prover/tests/assurance_algebraic.rs`,
  `circuit-prover/tests/trusted_statement.rs`).
- Tests:
  - the Poseidon2 width and shared-shape tests and the committed-materialization test cover
    the D3 configs (plain and shared); the D3 AIR evaluates symbolically over the cubic
    challenge field, and the cast guard rejects the binomial quadratic one;
  - `circuit-prover`: a two-row sponge and a 2-to-1 compression, checked against
    `PaddingFreeSponge<_, 12, 6, 6>` and `TruncatedPermutation<_, 2, 6, 12>`, proved over
    `goldilocks_d3_w12()` through the public D3 factories (`register_poseidon2_table::<3>`
    with the prepared prover, `poseidon2_table_provers_d3` with `prove_all_tables`) and
    verified; a forged permutation input in the trace is rejected;
  - `recursion/tests/goldilocks_d3_w12.rs` proves at D3 with `BatchStarkProver` and verifies:
    the known-answer permutation, two-row leaf sponges and Merkle rows in both directions
    (plus a mixed-height injection); the challenger table next to the ordinary table; and
    everything in the shared challenger table. Each table is materialized both from the
    committed preprocessing and through `batch_instance_d3` alone (the committed path
    declined), and the proof must contain it, so a D3 prover without `batch_instance_d3`
    fails these tests;
  - negatives: a forged permutation output (ordinary, challenger and shared tables, on both
    materialization paths) and a forged Merkle sibling written into the trace. In release
    builds each proof is produced and the verifier rejects it.

**Why.** With WP2 and WP3, this lets circuit-prover prove and verify circuits that use the
W12 permutation over `CubicTrinomialExtensionField<Goldilocks>`. In-circuit verification of
D3 proofs needs the recursion backend (WP5).

**Upstreamable.** Yes. It adds one table variant, prover and config, and leaves the existing
configurations unchanged.

### WP5: recursion backend for D3

**What changed.**

- `recursion/src/backend/fri.rs`:
  - `PcsRecursionBackend<SC, A, 3>` for `FriRecursionBackendForExt<3, ..>`, a copy of the
    `D = 2` backend. `Val<SC>` is bound by `CubicTrinomialExtendable` (no binomial bound), the
    tables are proved by `Poseidon2ProverD3` and `RecomposeProver::<3>`, and the AIR builders
    are `poseidon2_air_builders_for_configs::<SC, 3>` plus `RecomposeAirBuilder::<3>`. Hashing
    follows the Goldilocks D2/W8 path with `GOLDILOCKS_D3_W12` (cubic limbs), not the KoalaBear
    D5 path. There is no degree-3 Poseidon1 prover, so `prepare_circuit`, `validate_input` and
    `build_verifier_circuit` reject a challenger config that is not a degree-3 Poseidon2 one.
  - `GOLDILOCKS_D3_W12` joins the configs whose challenger and ordinary rows share one
    physical table (`goldilocks_d3_w12_shared`), like `GOLDILOCKS_D2_W8`.
  - `impl_prepared_fri_backend!` for `D = 3` (prepared and trusted backends), with the macro's
    field-bound parameter renamed from `$binomial_bound` to `$field_bound`.
  - `3 =>` arms in the batch-degree dispatches: native layout planning, verifier-circuit
    construction, and the trusted batch tables, preflight, circuit and private data.
- `recursion/src/backend/transcript.rs`: `3 =>` arm for the batch-layer transcript replay.
- `recursion/src/prepared/input.rs`: degree 3 accepted by the built-in input contract, with a
  `3 =>` arm for the public-input reconstruction.
- `recursion/src/verifier/errors.rs`: the error-conversion test uses degree 7, not 3, as its
  unsupported degree.
- Tests (`recursion/tests/goldilocks_d3_recursion.rs`, a new test target): a custom
  `FriRecursionConfig` over `GoldilocksD3W12Config` with small FRI parameters in lrup's shape
  (`max_log_arity` 3, `log_final_poly_len` 0, query PoW 4 bits, cap height 0).
  - A native batch proof of two toy AIRs (8 and 16 rows, a preprocessed column, a global
    lookup between them, a public value) is verified in-circuit with `verify_batch_circuit`.
    The verification circuit is proved at `D = 3` with the tables the D3 backend registers (the
    shared W12 table and `recompose/coeff`) and verified natively.
  - A changed opened value, a changed Merkle sibling (input batch and commit phase), a bad query
    PoW witness and an unbalanced global lookup each make the circuit fail to execute.
  - The D3 backend captures and validates the prepared input contract of that circuit proof,
    builds its verifier circuit with `build_next_layer_circuit` and runs it with the backend's
    private data. It rejects a challenger config of another degree.

**Why.** With WP1-WP4, this lets the in-circuit verifier check batch proofs over
`CubicTrinomialExtensionField<Goldilocks>` with W12 hashing, and lets circuit-prover prove that
verification at `D = 3`. The built-in suite registry and its D3 suite are WP6.

**Upstreamable.** Yes. Degree 3 joins the supported batch degrees for any field implementing
`CubicTrinomialExtendable`; the existing degrees are unchanged.

### WP9: D3 end-to-end gate (and WP6 test config)

**What changed.** Tests only; no library code.

- `recursion/tests/common/goldilocks_d3_config.rs` (new, shared by the D3 test targets through
  `#[path]`): the custom `D3RecursionConfig: FriRecursionConfig` over `GoldilocksD3W12Config`,
  moved out of `goldilocks_d3_recursion.rs` and parameterised by `D3FriParams` (log blowup,
  query count, query PoW bits, maximum log arity). Everything else is fixed to lrup's native
  shape: reference W12 permutation, `PaddingFreeSponge<_, 12, 6, 6>`,
  `TruncatedPermutation<_, 2, 6, 12>`, cap height 0, `DuplexChallenger<_, _, 12, 6>`,
  `log_final_poly_len` 0, no commit or batch PoW, no lookup or out-of-domain grinding.
  - `D3FriParams::lrup_inner_params()`: lrup's inner config (log blowup 1, 256 queries, 22-bit
    query PoW, max log arity 3).
  - `D3FriParams::recursion_layer_params()`: a 128-bit recursion-layer config (log blowup 2, 157
    queries, 22-bit query PoW, max log arity 3).
  - `D3FriParams::test_params()`: cheap parameters in the same shape (8 queries, 4-bit PoW).
  - Shared helpers: the D3 backend, `prove_layer_with_stats` (prove a verifier circuit at
    `D = 3` and verify it natively, with timings) and `layer_input` (the next-layer input of a
    layer proof). Restoring the FRI query paths in `set_fri_private_data` now returns an error
    instead of panicking, so a tampered proof is refused cleanly.
- `recursion/tests/goldilocks_d3_recursion.rs` uses the shared config (unchanged behaviour).
- `recursion/tests/goldilocks_d3_e2e.rs` (new test target `goldilocks_d3_e2e`):
  - The inner proof is a native batch proof of three toy AIRs with mixed heights (2^3, 2^5,
    2^7): a preprocessed AIR with a public value, an AIR with a degree-3 constraint (two
    quotient chunks), and an AIR receiving both on two global buses.
  - Layer 1 verifies it in-circuit (`verify_batch_circuit`) and proves that circuit at `D = 3`.
    Layer 2 verifies the layer-1 proof in-circuit (the D3 backend's
    `build_next_layer_circuit`) and proves that circuit at `D = 3`. Both layer proofs verify
    natively.
  - Negatives, each also rejected by the native verifier: a changed opened value and a bad query
    PoW witness (circuit execution fails); a changed Merkle sibling, input batch and commit
    phase (circuit execution fails); a proof of a trace that violates the degree-3 constraint,
    with honest FRI (in release builds; the native verifier fails the out-of-domain check of that
    AIR, the query paths restore, and the circuit fails execution on a connection); a layer-1
    proof with a changed opened value in any table (its paths do not restore, and with the honest
    paths the layer-2 circuit fails execution).
  - An ignored test, `two_layers_at_lrup_parameters`, runs the inner proof at
    `lrup_inner_params()` and both layers at `recursion_layer_params()`, printing each layer's
    table heights, times and peak memory.

**Why.** It checks the whole D3 path end to end, two proved layers deep, in lrup's config shape,
and records the sizes later recursion work plans with. The built-in D3 suite (persisted
verifying keys) is still to come.

**Upstreamable.** The tests could be, together with WP1-WP5.
