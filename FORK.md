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

### WP8: coefficient-bound leaf packing for every extension degree

**What changed.**

- `recursion/src/pcs/mmcs.rs`: one packing policy, `base_coeff_packing`, replaces
  `use_coeff_bound_binary_base_opening` and the WHIR-only D2/D4 rule. Whenever the permutation
  absorbs extension limbs (`d() > 1`; `d() == EF::DIMENSION` in every supported configuration),
  a Merkle leaf's opened values and salts are packed into limbs with coefficient-bound
  recomposition (`recompose/coeff`), which publishes each base coefficient on the
  `WitnessChecks` bus. Before, only non-hiding binary BabyBear/KoalaBear D4/W16 Poseidon2 leaves
  (and WHIR D2/D4 base queries) did; Goldilocks D2 and D3, Poseidon1, the W24 shapes, salted
  leaves and arity-4 leaves used the ALU `mul_add` chain.
- The policy applies to `verify_batch_circuit` (any field, salted or not, any permutation role),
  `verify_whir_base_batch_circuit`, the salted path of
  `verify_batch_circuit_from_extension_opened` (flattened extension values plus salt) and the
  arity-4 leaf digest behind `verify_batch_circuit_arity4`. `D = 1` permutations, which read each
  lifted base value as its own lane, and `EF = F` are unchanged.
- These entry points now need `enable_recompose` whenever `D > 1` and return
  `RecomposeCoeffLookupsUnavailable` without it. Every recursion backend already enables the
  table and proves its `recompose/coeff` rows. A packed limb costs one `recompose/coeff` row
  instead of `D` ALU `mul_add` rows, and a partial-chunk carry is unpacked through the same
  table, so affected circuits have fewer ALU rows, more recompose rows and different
  preprocessed columns (and therefore verifying keys). In WP9's two-layer gate at lrup's
  parameters, layer 1 goes from 133,046 ALU / 279 `recompose/coeff` rows to 125,878 / 4,375 and
  layer 2 from 262,803 / 2,090 to 203,457 / 29,879 (recompose degree bits 9 → 13 and 12 → 15;
  Poseidon2 rows unchanged, layer 2 gains one leaf permutation per query, 37,523 → 37,680). One
  run on a shared machine: layer 2 proves in 39.4 s instead of 22.4 s, peak RSS 1,504 MiB
  instead of 1,463 MiB.
- Tests: `recursion/tests/mmcs_leaf_coeff_binding.rs` (own `[[test]]` target), a regression
  test that leaf packing binds each base coefficient. At Goldilocks D2/W8 (binary and salted),
  D2/W16 (arity 4) and D3/W12 (binary and salted, proved with the D3 Poseidon2 prover of WP4)
  the honest row proves and verifies, while a witness that changes two coefficients of one limb
  but keeps the limb is refused by the runner, and a trace whose downstream reader sees such
  values does not verify. `mmcs_leaf_hash_binding.rs` (doc, salted leaves now coefficient-bound,
  fail-closed without the table), `arity4_leaf_hash_binding.rs`, `arity4_mmcs_bus_balance.rs`
  (registers the `recompose/coeff` table), `zk_hiding_mmcs.rs` (the salt mutation edits the
  `recompose/coeff` row) and the WHIR packing unit tests (the public route packs like WHIR for
  every family) follow the new policy.

**Why.** The opened values feed the FRI reduction coefficient by coefficient, so the leaf hash
should bind each one individually, for every field and leaf shape. Goldilocks D3/W12 needs this,
and tying the rule to the packed degree alone replaces a per-field, per-role allow list.

**Upstreamable.** Yes. The change is generic and adds no table. It changes circuit shapes, and so
verifying keys and fixed-key artifacts, for the geometries listed above.

### WP7: D3 differential tests

**What changed.** Tests only; no library code. Most of the differential suite came with WP1-WP5
(listed there); this package audits it against the plan and closes the remaining gaps.

- Constants known answers. lrup's `poseidon_perm_known_answer` (lrup's `poseidon_perm()` is
  `default_goldilocks_poseidon2_12()`) checks four inputs: zero, `[0, 1, ..., 11]`, all `p - 1`
  and a mixed vector. The fork pinned only `[0, 1, ..., 11]`; it now pins all four as hex
  literals (the first two equal lrup's own literals, the other two were computed with the same
  reference permutation):
  - `poseidon2-circuit-air` (`goldilocks_d3_width12::known_answer_on_air_trace_and_native_permutation`):
    the native reference permutation and the W12 AIR trace's output columns both reproduce every
    literal, and the AIR constraints hold on those rows;
  - `recursion/tests/goldilocks_d3_w12.rs` (`permutation_known_answer_native_and_in_circuit`):
    the native reference and the in-circuit W12 permutation (one fresh sponge row per input,
    all twelve outputs connected) both reproduce them, and a circuit expecting one changed
    output coefficient fails.
- ALU negative (`circuit-prover/src/air/alu_air.rs`, `cubic_trinomial_rejects_binomial_product`):
  a MUL output reduced with a binomial `x^3 = W` is now checked for `W = 1` and `W = 7` (it was
  `W = 1` only). The cubic-trinomial AIR rejects each; the binomial AIR with that `W` accepts
  it, so the rejection comes from the reduction alone; and that binomial AIR rejects the honest
  trinomial product.
- MMCS (`goldilocks_d3_w12.rs`, `check_all_openings`, used by the sponge, compression and
  mixed-height tests): every native opening is also verified with the native
  `MerkleTreeMmcs::verify_batch`, and besides a changed root, the circuit must now reject a
  changed opened value (first and last) and a changed Merkle sibling coefficient (first and
  last level).

**Coverage of the plan's differential tests (2.8).**

| Test | Where |
| --- | --- |
| Constants known answers vs lrup's `poseidon_perm()` | `poseidon2-circuit-air` `goldilocks_d3_width12` (constants, AIR trace); `goldilocks_d3_w12.rs` (in-circuit; proved in `proving::permutation_sponge_and_merkle_rows_prove_and_verify`) |
| W12 AIR trace vs native | `goldilocks_d3_width12::air_trace_matches_native_on_random_rows_and_constraints_hold` (random, sponge-chain and Merkle rows; tampered output rejected) |
| ALU D3 assurance and negatives | `alu_air.rs`: `assurance_alu_reference_goldilocks_d3`, `cubic_trinomial_ext_mul_matches_native`, `cubic_trinomial_rejects_mutated_out`, `cubic_trinomial_rejects_binomial_product`; proved D3 batch with a tampered MUL output (WP2) |
| Sponge vs `PaddingFreeSponge<_, 12, 6, 6>`, widths 1-13 | `goldilocks_d3_w12.rs` `sponge_matches_padding_free_sponge_for_widths_1_to_13`; proved two-row sponges (WP4) |
| Compression vs `TruncatedPermutation`, both directions | `goldilocks_d3_w12.rs` `compression_matches_truncated_permutation_in_both_directions`; proved Merkle rows (WP4) |
| Challenger transcript (observe, `sample`, `sample_ext`, `sample_bits`, PoW) | `goldilocks_d3_w12.rs` `challenger_transcript_matches_native_duplex_challenger` (plus a failing PoW witness); proved in `proving::challenger_table_proves_and_verifies` and `shared_challenger_table_proves_and_verifies` |
| MMCS commit/verify | `goldilocks_d3_w12.rs` `mmcs_openings_with_mixed_heights`; leaf coefficient binding in `mmcs_leaf_coeff_binding.rs` (WP8) |

**Why.** The plan's differential tests compare every D3/W12 building block with the native
Plonky3 code lrup uses, so a divergence fails here before it fails in recursion.

**Upstreamable.** The tests could be, together with WP1-WP5; the lrup cross-reference in the
known-answer comments would be dropped.

### WP10: salted hiding config at D3

**What changed.**

- `circuit-prover/src/config.rs`: `goldilocks_d3_w12_zk(params, os_entropy)`, the salted hiding
  counterpart of `goldilocks_d3_w12()` (same field, cubic challenge field, reference W12
  permutation, `PaddingFreeSponge<_, 12, 6, 6>`, `TruncatedPermutation<_, 2, 6, 12>`, cap height
  0, `DuplexChallenger<_, _, 12, 6>`, `log_final_poly_len` 0, no commit, batch, lookup or
  out-of-domain grinding). It mirrors the KoalaBear D4 salted factory
  (`recursion/src/builtin_config/fri.rs`):
  - `GoldilocksD3W12HidingMmcs`: `MerkleTreeHidingMmcs` over the W12 sponge and compression,
    with `GOLDILOCKS_D3_W12_ZK_SALT_ELEMS` = 4 Goldilocks salt elements (256 bits) per leaf. It is
    the input MMCS and, through `ExtensionMmcs`, the FRI commit-phase MMCS, so every commitment
    is salted.
  - `GoldilocksD3W12ZkPcs`: `HidingFriPcs` (random codewords, trace randomization to degree
    `2N`, quotient-chunk masks, a randomization polynomial) over those MMCSs;
    `GoldilocksD3W12ZkConfig` the `StarkConfig`.
  - Randomness: the input salts, the FRI salts and the PCS masks come from three
    `GoldilocksD3W12ZkRng` (`StdRng`, ChaCha12) generators, each seeded by its own draw from the
    caller's OS entropy source (`rand::rngs::SysRng` in a `std` caller; this crate is `no_std`
    and its `rand` has no OS-entropy feature). There is no constructor that takes a seed.
  - `GoldilocksD3W12ZkParams` (log blowup, queries, query PoW bits, maximum log arity, random
    codewords) with `outer_wrap()` (rate 1/8, 128 queries, 22-bit query PoW, arity up to 8,
    3 random codewords: 128.2 proven bits under unique decoding) and `test()`. `validate()`
    refuses fewer random codewords than the extension degree. `hiding_budget()` is p3-fri's
    per-matrix budget at two opening points, `2 * (queries + 3 * 2)`, and `min_trace_height()` the
    power of two above it (512 rows at `outer_wrap()`). `pad_table_packing` raises a
    `TablePacking`'s minimum height to it; `check_table_packing` refuses a packing below it.
    `HidingFriPcs` itself refuses any shorter table at commitment, opening and verification.
  - `GoldilocksD3W12ZkError`, and unit tests: the parameter checks and budget, the packing
    helpers, three 32-byte seeds drawn per config, a failing entropy source reported as an error.
- The circuit's preprocessed commitment is salted from the input MMCS's stream at preparation.
  Its contents are public (p3-fri pads it with zero rows, not random ones), and the verifier takes
  it from the trusted preparation (`CircuitVerifier`), so it is not recomputable from the circuit
  alone. A fixed verifying-key artifact for a hiding circuit (7.5) needs a deterministic
  preprocessing commitment.
- `recursion/tests/common/goldilocks_d3_toy.rs`: the toy AIRs, the inner proof, layer 1 and the
  layer-2 builder of `goldilocks_d3_e2e.rs`, moved out unchanged (now `pub`) so both D3 targets
  share them. `goldilocks_d3_e2e.rs` keeps its tests and measurements.
- `recursion/tests/goldilocks_d3_zk.rs` (new test target `goldilocks_d3_zk`): the layer-2 circuit
  of WP9 (inner proof, layer 1 proved without hiding, layer 2 built by the D3 backend) is proved
  under the hiding config, with the D3 tables (shared W12 Poseidon2, `recompose/coeff`) and
  tables padded to the hiding budget, and verified natively. Every config is seeded from
  `/dev/urandom`. Tests:
  - the proof verifies and has the hiding structure (randomization commitment and openings,
    three random-codeword values per private opening point, salts, doubled degrees);
  - two proofs of the same statement and witness from one preparation, and a third from a
    separately seeded config, share no commitment root, Merkle sibling digest, salt (input batch
    or FRI), out-of-domain value, random-codeword opening, FRI sibling value, final polynomial or
    query opening, compared value by value over the whole proof structure. Excluded as public:
    the preprocessed commitment and the preprocessed round's openings, public values, table
    shape metadata and proof-of-work nonces. Within a proof the input and FRI salts never meet;
    the separately seeded config's preprocessed commitment differs;
  - a table below the hiding budget is refused (packing check; the PCS at preprocessing with an
    unpadded packing), the padded packing proves, and two random codewords are refused;
  - a changed salt (every input round, first and last FRI layer) and a changed opened value
    (main trace of every table, quotient chunk, randomization polynomial, random-codeword opening
    of every private round, query row, FRI sibling value) are rejected by the native verifier;
  - the outer-wrap parameters reach 128 proven bits;
  - an ignored measurement, `hiding_layer2_at_outer_parameters`. One single-threaded run on a
    shared machine, layer 2 over an inner proof at lrup's parameters and layer 1 at
    `recursion_layer_params()`: non-hiding at 2/157/22, prove 39.6 s, peak RSS 1,497 MiB,
    1,253,968 bytes; hiding at `outer_wrap()` (3/128/22), prove 136.3 s, 6,650 MiB,
    1,651,079 bytes; hiding at 2/157/22, prove 71.6 s, 3,562 MiB, 1,934,519 bytes. Hiding pads
    the two small tables to 512 rows and doubles every committed degree (degree bits
    `[9, 6, 16, 16, 15]` become `[10, 10, 17, 17, 16]`). Pruned Merkle paths make the byte size
    vary slightly from proof to proof.

**Why.** `--zk` wraps the root proof in one hiding proof (plan Phase 6), which must be hiding on
its own: every commitment salted, every revealed evaluation masked, randomness from the OS, with
the hiding budget covering every opening. The library's salted mode existed only for KoalaBear D4.

**Upstreamable.** The factory could be, with WP1-WP5. A built-in suite (persisted verifying keys)
is still to come.
