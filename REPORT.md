# Final Report — `zebra-chain-arith`

This report covers the kernel-checked Lean 4 verification of the
arithmetic and parsing layer of [`zebra-chain`](https://github.com/ZcashFoundation/zebra).

## Scope

The verified targets are three families that every Zcash node routes every
block and transaction through:

| Family | Rust source | Lean module |
|---|---|---|
| `Height` arithmetic | `zebra-chain/src/block/height.rs` | `ZebraChainArith/Height.lean` |
| `Amount` arithmetic | `zebra-chain/src/amount.rs` | `ZebraChainArith/Amount.lean` |
| `CompactSize64` serialization | `zebra-chain/src/serialization/compact_size.rs` | `ZebraChainArith/CompactSize.lean` |

Concrete test vectors taken from the Rust doctests are in
`ZebraChainArith/TestVectors.lean` and are `decide`-checked.

## Methodology

There are two parallel Lean projects in this repo:

1. **The hand-translated proofs (top-level).** The primary verification.
   Each Rust item is mapped to a corresponding Lean definition; theorems
   are stated about the Lean definitions and proved using Mathlib tactics
   (`omega`, `linarith`, `simp`, `decide`, structural induction).

2. **The Aeneas-extracted proofs ([`aeneas-pipeline/`](aeneas-pipeline/)).**
   A separate Lean project that ingests definitions emitted by the
   `Charon → Aeneas → Lean` pipeline. The Rust extraction crate at
   [`rust-crate/`](rust-crate/) is the source.

### Hand-translation (top-level project)

The `i64` and `i128` widening from the Rust source is modelled as `Int`
arithmetic, with explicit upper-bound hypotheses where the Rust type widths
matter:

- `Height`: heights ≤ `MAX_AS_U32 = 2^31 - 1` (Zcash protocol bound).
- `Amount`: values in `[lo, hi]` per the `Constraint` instance; `i128`
  widening for `Mul<u64>` is exact in `Int`.
- `CompactSize64`: `n ≤ U64_MAX = 2^64 - 1` for the band-4 round-trip and
  the universal round-trip.

### Aeneas extraction (`aeneas-pipeline/`)

[`rust-crate/`](rust-crate/) is a self-contained Rust crate that mirrors
the load-bearing semantic content of the three target modules from
`zebra-chain`, in a form Aeneas can ingest. The Rust `byteorder` and
`io::Read`/`io::Write` boundary is replaced by `&[u8]` and `Vec<u8>` —
the small adaptation the original proposal called out as the
extraction-crate shim.

[`aeneas-pipeline/`](aeneas-pipeline/) is a Lean project that imports the
Aeneas-emitted definitions and proves a handful of representative examples
against them in Aeneas's `Result`-monadic style over `Std.U32`/`Std.I64`
types. To regenerate the extraction:

```sh
cd rust-crate
~/aeneas/charon/bin/charon cargo --preset=aeneas
mkdir -p ../aeneas-pipeline/AeneasPipeline
~/aeneas/bin/aeneas -backend lean -dest /tmp/out zebra_chain_arith.llbc
cp /tmp/out/ZebraChainArith.lean ../aeneas-pipeline/AeneasPipeline/Extracted.lean
cd ../aeneas-pipeline && lake build
```

### What the combined methodology does *and* does not provide

- ✅ **Mechanical Rust-to-Lean lift via Aeneas.** The Aeneas pipeline
  proves the principle: the Rust source in `rust-crate/` is mechanically
  lifted to Lean and is amenable to proof.
- ⚠️ **Partial drift detection.** When the Rust crate changes, the
  emitted Lean changes, and the Aeneas-side proofs would break. This
  catches drift between the *Rust extraction crate* and *its Lean
  extract*. It does NOT yet catch drift between the live
  `zebra-chain/src/...` source and our `rust-crate/`. Closing that final
  gap needs a CI step that diffs `rust-crate/src/{amount,compact_size,
  height}.rs` against pinned snippets of `zebra-chain`.
- ⚠️ **No byte-level I/O modelling.** The encoder/decoder operate over
  `List Nat` (top-level proofs) or `Vec u8` (Aeneas). The
  `byteorder::Reader`/`Writer` boundary in `zebra-chain` is treated as a
  thin trusted shim.

## Result

**45 theorems** kernel-checked across the three modules, plus 27 concrete
test vectors verified by `decide`. No `sorry`. No user-introduced axioms.
No unproved theorems. Every result depends only on Lean 4's three
foundational axioms (`propext`, `Quot.sound`, `Classical.choice`), which
all Mathlib proofs share.

### Per-module theorem inventory

#### `Height` (11 theorems)
| Name | Statement |
|---|---|
| `tryFromU32_iff` | `try_from` succeeds iff `n ≤ MAX_AS_U32` |
| `subH_eq` | `Sub<Height,Height>` is the signed integer difference |
| `add_result_bounded` | `add` result, when present, is in `[0, MAX_AS_U32]` |
| `sub_result_bounded` | Same for `sub` |
| `add_sub_eq` | Round-trip `(h + d) − d = h` |
| `add_monotone` | `add` is monotone in the diff |
| `subH_antisymm` | `subH a b = -(subH b a)` |
| `subH_self` | `subH a a = 0` |
| `tryFromU32_valid` | Idempotence on valid inputs |
| `add_zero_identity` | `add h 0 = some h` |
| `sub_zero_identity` | `sub h 0 = some h` |

#### `Amount` (21 theorems)
| Name | Statement |
|---|---|
| `validate_negativeAllowed_iff` | Validate iff in `[-MAX, MAX]` |
| `validate_nonNegative_iff` | Validate iff in `[0, MAX]` |
| `validate_negativeOrZero_iff` | Validate iff in `[-MAX, 0]` |
| `checkedAdd_iff` | `checkedAdd` succeeds iff sum in range |
| `checkedAdd_in_range` | Closure under range |
| `checkedSub_iff` | `checkedSub` succeeds iff diff in range |
| `checkedSub_in_range` | Closure under range |
| `mulU64_iff` | `Mul<u64>` succeeds iff product in range |
| `neg_inverse` | `a + neg a = 0` |
| `neg_negativeAllowed_closed` | `NegativeAllowed` survives negation |
| `divU64_zero` | Division by zero rejected |
| `divU64_nonNegative_closed` | NonNegative + positive divisor stays in range |
| `sum_empty` | `Sum` of empty list is `some 0` |
| `sum_singleton_nonNegative` | `Sum` of one element |
| `sum_value` | `Sum` result equals the integer sum (general lists) |
| `sum_in_range` | `Sum` result is in range when present (general lists) |
| `checkedAdd_comm` | `checkedAdd` is commutative |
| `neg_zero` | `neg 0 = 0` |
| `neg_neg_eq` | `neg` is involutive |
| `checkedSub_as_add` | `sub a b = add a (neg b)` |
| `checkedAdd_zero` | `checkedAdd a 0 = validate a` |

#### `CompactSize` (15 theorems)
| Name | Statement |
|---|---|
| `roundtrip_band1` | Encoder/decoder round-trip on `[0, 0xfc]` |
| `roundtrip_band2` | Round-trip on `[0xfd, 0xffff]` |
| `roundtrip_band3` | Round-trip on `[0x10000, 0xffffffff]` |
| `roundtrip_band4` | Round-trip on `[0x100000000, U64_MAX]` |
| `roundtrip_universal` | Single statement covering all `n ≤ U64_MAX` |
| `encode_length` | Encoder length is in `{1, 3, 5, 9}` |
| `decode_total` | Decoder is total (never panics) |
| `decode_empty` | Empty input rejected |
| `encode_nonempty` | Encoder output is non-empty |
| `encode_first_byte_canonical` | First byte is in `{0..0xfc, 0xfd, 0xfe, 0xff}` |
| `canonicity_band2` | Decoder rejects non-minimal 3-byte encodings |
| `canonicity_band3` | Decoder rejects non-minimal 5-byte encodings |
| `canonicity_band4` | Decoder rejects non-minimal 9-byte encodings |
| `messageTryFrom_iff` | `CompactSizeMessage::try_from` succeeds iff under cap |
| `messageTryFrom_rejects_overlimit` | Memory-DoS preallocation values rejected |

## Reproducing

Requires [`elan`](https://github.com/leanprover/elan).

```sh
lake exe cache get          # fetches Mathlib's prebuilt artifacts
lake build                  # kernel-checks every theorem
lake env lean ZebraChainArith/Check.lean   # prints the axiom set of every theorem
```

CI runs the same sequence on every push and pull request
(`.github/workflows/lean_action_ci.yml`).

## Limitations

1. **Hand-translation drift.** As above — no automated invariant tying the
   Lean model to live `zebra-chain` source.
2. **I/O abstraction.** The encoder/decoder model bytes as `List Nat`. The
   `byteorder::Reader`/`Writer` boundary in the Rust source is not modelled.
3. **`Amount::Sum` only verified up to the Mathlib `List.foldr`
   equivalence.** The Rust impl uses `try_fold` (left-fold-with-short-circuit);
   our model uses right-fold for proof tractability. For an additive
   operation that commutes with the constraint check, the two are
   equivalent on all in-range inputs, but the equivalence is not separately
   proved.
4. **`Amount` constraint markers are encoded as an `inductive` enum** rather
   than as a trait + instances. Adding a constraint (e.g. for a new pool)
   would require extending the `Constraint` inductive type and re-proving
   the case splits. The Rust trait-based design is more open; the Lean
   inductive is more closed but simpler to prove against.

## Roadmap

This pilot covers the consensus-critical *arithmetic and parsing* layer.
Natural follow-on targets, in rough order of marginal value:

1. **Replace hand-translation with Aeneas.** Eliminates the drift gap and
   restores the credibility claim the original grant proposal made for the
   pipeline-based approach.
2. **`Work` 256-bit reciprocal** (`work/difficulty.rs::Work::try_from`) and
   `CompactDifficulty::to_expanded` / `to_compact`. Bit-vector reasoning;
   higher bug density than the integer layer.
3. **`BlockHeight` activation logic over all `NetworkUpgrade` variants.**
   Compile-time exhaustiveness on the Lean side, matching the Rust
   exhaustive match.
4. **`Merkle` tree over transactions** — structural correctness and
   inclusion-proof invariants.
5. **Cryptographic primitives layer** (Pedersen, note commitments, Sapling
   and Orchard circuits). Requires substantial additional infrastructure.
