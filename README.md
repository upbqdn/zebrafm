# zebrafm — Lean 4 proofs for [Zebra](https://github.com/ZcashFoundation/zebra)

Kernel-checked Lean 4 theorems for the consensus + protocol surface of the
Zcash Foundation's Zebra full node, covering **`zebra-chain`,
`zebra-consensus`, `zebra-network`, `zebra-state`, `zebra-rpc`,
`zebra-script`, `tower-batch-control`, `tower-fallback`, and `zebrad`**.

- **1935 theorems across 80 modules** (`lake build` passes 909 jobs).
- The original pilot scope (Amount / CompactSize / Height) is in
  [`Zebrafm/Height.lean`](Zebrafm/Height.lean) /
  [`Zebrafm/Amount.lean`](Zebrafm/Amount.lean) /
  [`Zebrafm/CompactSize.lean`](Zebrafm/CompactSize.lean) — that's the
  18-theorem ZCG-grant-shaped core; the rest extends across the whole
  consensus surface, subsidy schedule, ZIP-defined rules, network message
  caps, mempool admission, RPC error codes, state DB format, and more.
- See [REPORT.md](REPORT.md) for the per-module inventory, [FINDINGS.md](FINDINGS.md)
  for the 207 adversarially-extracted findings (including ones the
  verification surfaced about the Lean models themselves), and
  [ROADMAP.md](ROADMAP.md) for what's still open.

All theorems are kernel-checked with **no `sorry`**, **no user-introduced
axioms**, and **no unproved theorems**. They depend only on the three Lean 4
foundational axioms (`propext`, `Quot.sound`, `Classical.choice`), as every
Mathlib proof does.

## What is verified

The Rust targets are hand-translated to Lean 4. Each Rust item maps to a Lean
definition; the `i64` / `i128` widening from the Rust source is modelled as
`Int` arithmetic, with explicit upper-bound hypotheses where the production
type sizes matter (e.g. `U64_MAX` in `CompactSize64`).

### `Height` ([`Zebrafm/Height.lean`](Zebrafm/Height.lean))

The Rust target is `zebra-chain/src/block/height.rs`.

| Rust | Lean model |
|---|---|
| `Height(u32)` | `Nat`, with `MAX_AS_U32 = 2^31 - 1` |
| `HeightDiff = i64` | `Int` |
| `Height::try_from<u32>` | `tryFromU32` |
| `impl Add<HeightDiff> for Height` | `add` |
| `impl Sub<HeightDiff> for Height` | `sub` |
| `impl Sub<Height> for Height` | `subH` |

Theorems:
- `tryFromU32_iff` — succeeds iff in `[0, MAX_AS_U32]`.
- `subH_eq` — equals the signed integer difference.
- `add_result_bounded`, `sub_result_bounded` — every `Some` result is in
  `[0, MAX_AS_U32]`.
- `add_sub_eq` — round-trip `(h + d) − d = h` for valid `h`.
- `add_monotone` — monotone in the diff.
- `subH_antisymm`, `subH_self` — antisymmetry and reflexivity.
- `tryFromU32_valid`, `add_zero_identity`, `sub_zero_identity` — identity laws.

### `Amount` ([`Zebrafm/Amount.lean`](Zebrafm/Amount.lean))

The Rust target is `zebra-chain/src/amount.rs`.

| Rust | Lean model |
|---|---|
| `Amount<C>(i64, PhantomData<C>)` | `Int` |
| `MAX_MONEY = 21_000_000 * COIN` | `MAX_MONEY` |
| `NegativeAllowed`, `NonNegative`, `NegativeOrZero` | `Constraint` cases |
| `Constraint::validate` | `Constraint.validate` |
| `impl Add<Amount<C>>` / `Sub<Amount<C>>` | `checkedAdd` / `checkedSub` |
| `impl Mul<u64>` | `mulU64` |
| `impl Div<u64>` | `divU64` |
| `impl Neg` | `neg` |
| `impl Sum<Amount<C>> for Result<Amount<C>>` | `sumFold` |

Theorems:
- `validate_*_iff` — `validate` succeeds iff in the constraint's range
  (`NegativeAllowed`, `NonNegative`, `NegativeOrZero`).
- `checkedAdd_iff` / `checkedSub_iff` — succeeds iff result is in range.
- `checkedAdd_in_range` / `checkedSub_in_range` — closure under the range.
- `mulU64_iff` — `i128`-widened multiplication is in range iff the product is.
- `neg_inverse` — `a + neg a = 0`.
- `neg_negativeAllowed_closed` — symmetric range survives negation.
- `divU64_zero` — division by zero returns `none`.
- `divU64_nonNegative_closed` — division by a positive `u64` is closed under
  `NonNegative`.
- `sum_empty`, `sum_singleton_nonNegative` — `Sum`-as-`checkedAdd`-fold.
- `checkedAdd_comm`, `neg_zero`, `neg_neg_eq`, `checkedSub_as_add`,
  `checkedAdd_zero` — algebraic laws.

### `CompactSize64` ([`Zebrafm/CompactSize.lean`](Zebrafm/CompactSize.lean))

The Rust target is `zebra-chain/src/serialization/compact_size.rs`.

| Rust | Lean model |
|---|---|
| `CompactSize64::zcash_serialize` | `encode` |
| `CompactSize64::zcash_deserialize` | `decode` |
| four bands (`[0, 0xfc]`, `[0xfd, 0xffff]`, `[0x10000, 0xffffffff]`, `> 0xffffffff`) | preserved in `encode`/`decode` |
| `CompactSizeMessage::try_from<usize>` | `messageTryFrom` |
| `MAX_PROTOCOL_MESSAGE_LEN` cap | `MAX_PROTOCOL_MESSAGE_LEN` |

Theorems:
- `roundtrip_band1`/`band2`/`band3`/`band4` — encoder/decoder round-trip per
  band.
- `roundtrip_universal` — single statement covering all `n ≤ U64_MAX`.
- `encode_length` — encoder length is in `{1, 3, 5, 9}`.
- `decode_total` — decoder is total (never panics).
- `decode_empty` — empty input rejected.
- `encode_nonempty`, `encode_first_byte_canonical` — well-formedness of the
  encoder output.
- `canonicity_band2`/`band3`/`band4` — **the decoder rejects non-minimal
  encodings.** This is the CVE-2012-2459 class of consensus-critical
  malleability bug.
- `messageTryFrom_iff` — `CompactSizeMessage::try_from` succeeds iff
  `n ≤ MAX_PROTOCOL_MESSAGE_LEN`.
- `messageTryFrom_rejects_overlimit` — explicit rejection of memory-DoS
  preallocation values.

## Reproducing

Requires [`elan`](https://github.com/leanprover/elan).

```sh
lake exe cache get  # fetches Mathlib's prebuilt artifacts
lake build           # kernel-checks every theorem in the project
```

To print the axiom dependency of each theorem:

```sh
lake env lean Zebrafm/Check.lean
```

## Modelling notes

- The encoders and decoders are modelled as **pure** functions over `Nat` /
  `List Nat`. The Rust `byteorder` reader/writer side of the I/O boundary is
  not modelled — the proofs cover the semantic content of the encoding only.
- The model is **hand-translated** from the Rust source. There is no automated
  drift detection: if `zebra-chain` changes the implementation, the proofs do
  not automatically catch it. A continuous-integration step that diffs the
  current `zebra-chain` source against the model anchor would close that gap.
- `Amount`'s `i128` widening for `Mul<u64>` is collapsed into `Int` arithmetic,
  which is exact for any `i64 × u64` input — matching the Rust source's
  intended semantics.
- `CompactSize64::encode`'s upper bound is `U64_MAX` (mirroring Rust's `u64`
  type), enforced as a hypothesis on the band-4 round-trip and on
  `roundtrip_universal`.
