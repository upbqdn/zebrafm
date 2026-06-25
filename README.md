# zebra-chain-arith — Lean 4 proofs for `zebra-chain` arithmetic

Formal verification of a small slice of [zebra-chain](https://github.com/ZcashFoundation/zebra)
arithmetic, hand-translated to Lean 4 and proved with kernel-checked theorems.

This repository is a single-AI-session experiment to see how the first phase of
[ZCG grant #324](https://github.com/ZcashCommunityGrants/zcashcommunitygrants/issues/324)
(Runtime Verification's proposed pipeline-based verification of `Amount`,
`CompactSize64`, and `Height`) compares to what an LLM produces unaided. It
covers the `Height` family only — the easiest of the three the grant proposes.
It is **not** a substitute for a funded engagement.

## What is verified

The Rust target is `zebra-chain/src/block/height.rs`, specifically:

| Rust | Lean model |
|---|---|
| `Height(u32)` | `Nat` (with `MAX_AS_U32 = 2^31 - 1` as the implicit invariant) |
| `HeightDiff = i64` | `Int` |
| `Height::try_from<u32>` | `Zebra.Height.tryFromU32` |
| `impl Add<HeightDiff> for Height` | `Zebra.Height.add` |
| `impl Sub<HeightDiff> for Height` | `Zebra.Height.sub` |
| `impl Sub<Height> for Height` | `Zebra.Height.subH` |

The `i64`-widened arithmetic in Rust is modelled as `Int` arithmetic in Lean,
matching the *intended* semantics. The arithmetic in the Rust code can only
diverge from this model if `lhs + rhs` overflows `i64`, which requires inputs
no Zebra-derived `Height` ever holds.

## Theorems

Defined in [`ZebraChainArith/Height.lean`](ZebraChainArith/Height.lean):

1. `tryFromU32_iff` — `tryFromU32 n` is `some` iff `n ≤ MAX_AS_U32`.
2. `subH_eq` — `subH` is the signed integer difference.
3. `add_result_bounded` — every `Some` result of `add` is in `[0, MAX_AS_U32]`.
4. `sub_result_bounded` — same for `sub`.
5. `add_sub_eq` — for `h ≤ MAX_AS_U32`, `(h + d) - d = h` whenever the addition
   succeeds (round-trip).
6. `add_monotone` — `add` is monotone in its difference argument.

All theorems are kernel-checked with no `sorry`, no user-introduced axioms, and
no unproved theorems. They depend only on the three Lean 4 foundational axioms
(`propext`, `Quot.sound`, `Classical.choice`), as every Mathlib proof does.

## Reproducing

Requires `elan` (`https://github.com/leanprover/elan`).

```sh
lake exe cache get  # downloads Mathlib's prebuilt artifacts
lake build           # builds the project, kernel-checks all theorems
```

Or, to print the axiom list each theorem depends on:

```sh
lake env lean ZebraChainArith/Check.lean
```

## Scope and limitations

This covers exactly one of the three families ZCG #324 proposes (`Height`), and
fewer than half of the theorems the grant promises. It does **not**:

- include `Amount` arithmetic or `CompactSize64` round-trip;
- include the consensus-critical CompactSize canonicity property;
- use Aeneas to lift the Rust source into Lean automatically (the model here is
  hand-written, so any drift between `zebra-chain` and this model is silent);
- replace the credibility, methodology selection, and independent review that a
  funded engagement provides.

It is a single-session data point on what an LLM produces with no prior
verification setup — useful for grant scoping, not a deliverable.
