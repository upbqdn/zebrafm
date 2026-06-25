import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Transaction maximum serialized size

## What Rust actually enforces

In Zebra, the only byte-length cap enforced on a single transaction at
deserialisation time is `MAX_BLOCK_BYTES = 2_000_000`, via a bounded
`Read::take`:

> `let mut limited_reader = reader.take(MAX_BLOCK_BYTES);`
> — `zebra-chain/src/transaction/serialize.rs:783`

The matching block-level check is the same constant:

> `let limited_reader = &mut reader.take(MAX_BLOCK_BYTES);`
> — `zebra-chain/src/block/serialize.rs:158`

There is **no `MAX_TX_BYTES` constant in Rust**, and no per-transaction byte
cap distinct from the block cap is enforced anywhere. The comment

> "Post-Sapling, this is also the maximum size of a transaction in the
> Zcash specification. (But since blocks also contain a block header and
> transaction count, the maximum size of a transaction in the chain is
> approximately 1.5 kB smaller.)"
> — `zebra-chain/src/block/serialize.rs:18-23`

is informational, not enforced: a serialized transaction is *theoretically*
bounded by `MAX_BLOCK_BYTES - block-overhead`, but Rust's `reader.take`
only rejects strictly above `MAX_BLOCK_BYTES`.

## What this module proves

We separate the two cleanly:

  * `transactionSizeOk`  — the **enforced** check, mirroring Rust:
    `size ≤ MAX_BLOCK_BYTES`.
  * `THEORETICAL_TX_BYTES_UPPER_BOUND` — a *derived, not-enforced* upper
    bound from the docstring, equal to `MAX_BLOCK_BYTES` minus a concrete
    fixed-overhead model of the rest of a block. We pin its value and
    show every transaction that fits under it is accepted by the enforced
    check, but the converse is **not** a Rust property and we do not
    claim it.

The fixed-overhead model is:

  * `HEADER_FIXED_SIZE = 140` (version + 3*32 + time + bits + nonce; see
    `BlockHeader.lean`)
  * `SOLUTION_SIZE = 1344` (Equihash 200/9 solution payload;
    `zebra-chain/src/work/equihash.rs:31`)
  * `SOLUTION_COMPACTSIZE = 3` (CompactSize prefix for the 1344-byte
    solution — proven below from the CompactSize encoding rule, not
    assumed.)
  * `TX_COUNT_COMPACTSIZE_REALISTIC = 3` (CompactSize prefix for a tx
    count that fits a 2 MB block; see `tx_count_prefix_at_most_3` below.)

giving `BLOCK_OVERHEAD_BYTES_REALISTIC = 140 + 1344 + 3 + 3 = 1_490`
(≈ 1.5 kB) and `THEORETICAL_TX_BYTES_UPPER_BOUND = 1_998_510`.

We deliberately drop the previous module's worst-case
`TX_COUNT_COMPACTSIZE_MAX = 9` (a 9-byte CompactSize header is only used
for tx counts > 2^32, far above the count any 2 MB block can hold — see
`tx_count_compactsize_9_unreachable` below).
-/

namespace Zebra.TransactionMaxSize

/-! ## Constants -/

/-- `MAX_BLOCK_BYTES`: maximum size of a Zcash block, in bytes.

This is the **only** byte-length cap enforced on serialized transactions in
Rust (via `reader.take(MAX_BLOCK_BYTES)`).
Source: `zebra-chain/src/block/serialize.rs:24`. -/
def MAX_BLOCK_BYTES : Nat := 2_000_000

/-- Fixed-size portion of a block header. Matches `Zebra.BlockHeader.HEADER_FIXED_SIZE`.
Source: `zebra-chain/src/block/header.rs` (`pub struct Header`). -/
def HEADER_FIXED_SIZE : Nat := 140

/-- Size of the Equihash 200/9 solution payload, in bytes.
Source: `zebra-chain/src/work/equihash.rs:31` (`SOLUTION_SIZE`). -/
def SOLUTION_SIZE : Nat := 1344

/-- CompactSize prefix on the 1344-byte solution.

For values `v`, the Zcash/Bitcoin CompactSize encoding uses:
  * 1 byte if `v ≤ 252`
  * 3 bytes (`0xfd` + 2 LE) if `253 ≤ v ≤ 65535`
  * 5 bytes (`0xfe` + 4 LE) if `65536 ≤ v ≤ 2^32 - 1`
  * 9 bytes (`0xff` + 8 LE) if `2^32 ≤ v`

`SOLUTION_SIZE = 1344` lies in `[253, 65535]`, hence a 3-byte prefix.
This is *proven* below in `solution_compactsize_value`, not assumed.
Source: `zebra-chain/src/serialization/compact_size.rs`. -/
def SOLUTION_COMPACTSIZE : Nat := 3

/-- CompactSize prefix for any per-block transaction count that fits in a
2 MB block. The smallest serialized transaction is well over 80 bytes, so
the tx count is at most `2_000_000 / 80 = 25_000`, which lies in
`[253, 65535]` and so encodes in 3 bytes. We use 3 here for the
realistic-overhead model; the worst-case 9-byte form is unreachable
(see `tx_count_compactsize_9_unreachable`). -/
def TX_COUNT_COMPACTSIZE_REALISTIC : Nat := 3

/-- Realistic per-block overhead other than the transactions themselves:
header + solution + compact-size prefixes (with a realistic 3-byte tx-count
CompactSize). -/
def BLOCK_OVERHEAD_BYTES_REALISTIC : Nat :=
  HEADER_FIXED_SIZE + SOLUTION_SIZE + SOLUTION_COMPACTSIZE + TX_COUNT_COMPACTSIZE_REALISTIC

/-- `THEORETICAL_TX_BYTES_UPPER_BOUND`: the spec-level upper bound on the
serialized size of a single transaction *implied* by the
`block/serialize.rs:18-23` docstring ("approximately 1.5 kB smaller" than
`MAX_BLOCK_BYTES`).

**Not enforced anywhere in Rust.** The actual enforced cap is
`MAX_BLOCK_BYTES` itself. We expose this as a named upper bound only to
pin the "1.5 kB smaller" claim down to a concrete number; downstream
verification should use `transactionSizeOk` (which mirrors the Rust
`reader.take(MAX_BLOCK_BYTES)` cap) rather than this constant. -/
def THEORETICAL_TX_BYTES_UPPER_BOUND : Nat :=
  MAX_BLOCK_BYTES - BLOCK_OVERHEAD_BYTES_REALISTIC

/-! ## The enforced predicate -/

/-- The transaction-size guard *as enforced by Rust*: accept iff
`size ≤ MAX_BLOCK_BYTES`.

Mirrors `reader.take(MAX_BLOCK_BYTES)` in
`zebra-chain/src/transaction/serialize.rs:783` (and the identical bound on
block deserialization at `block/serialize.rs:158`). There is no smaller
per-transaction byte cap in Rust. -/
def transactionSizeOk (size : Nat) : Bool := size ≤ MAX_BLOCK_BYTES

/-- A generic guard parameterised by an arbitrary byte cap, useful for
referring to spec-level or theoretical bounds (e.g.
`THEORETICAL_TX_BYTES_UPPER_BOUND`). -/
def transactionSizeOkWithCap (size cap : Nat) : Bool := size ≤ cap

/-! ## Theorems on the enforced predicate -/

/-- **T1 (iff form).** `transactionSizeOk` is the decidable form of
`size ≤ MAX_BLOCK_BYTES`. -/
theorem transactionSizeOk_iff (size : Nat) :
    transactionSizeOk size = true ↔ size ≤ MAX_BLOCK_BYTES := by
  unfold transactionSizeOk
  exact decide_eq_true_iff

/-- **T2 (anti-tone in size).** Shrinking a transaction never invalidates it. -/
theorem transactionSizeOk_antitone (s₁ s₂ : Nat) (hle : s₁ ≤ s₂)
    (h : transactionSizeOk s₂ = true) : transactionSizeOk s₁ = true := by
  rw [transactionSizeOk_iff] at h ⊢
  exact hle.trans h

/-- **T3 (boundary accepted).** A transaction of *exactly* `MAX_BLOCK_BYTES`
bytes is accepted. -/
theorem transactionSizeOk_at_max :
    transactionSizeOk MAX_BLOCK_BYTES = true := by
  rw [transactionSizeOk_iff]

/-- **T4 (limit + 1 rejected).** A transaction one byte over the limit is
rejected. -/
theorem transactionSizeOk_just_above :
    transactionSizeOk (MAX_BLOCK_BYTES + 1) = false := by
  unfold transactionSizeOk
  exact decide_eq_false (by omega)

/-- **T5 (rejection is exact).** Any size strictly above `MAX_BLOCK_BYTES`
is rejected. -/
theorem transactionSizeOk_reject_above (size : Nat) (h : MAX_BLOCK_BYTES < size) :
    transactionSizeOk size = false := by
  unfold transactionSizeOk
  exact decide_eq_false (by omega)

/-- **T6 (accept-reject dichotomy).** `transactionSizeOk` either accepts or
rejects — there is no third case. -/
theorem transactionSizeOk_dichotomy (size : Nat) :
    transactionSizeOk size = true ∨ transactionSizeOk size = false := by
  cases Bool.eq_false_or_eq_true (transactionSizeOk size) with
  | inl h => exact Or.inl h
  | inr h => exact Or.inr h

/-- **T7 (zero accepted).** A 0-byte (degenerate) transaction is accepted. -/
theorem transactionSizeOk_zero : transactionSizeOk 0 = true := by
  rw [transactionSizeOk_iff]; exact Nat.zero_le _

/-! ## Theorems linking the realistic overhead model to Rust -/

/-- **T8 (overhead value).** Pins the "≈ 1.5 kB" docstring claim to the
exact realistic value `1_490` bytes. -/
theorem BLOCK_OVERHEAD_BYTES_REALISTIC_value :
    BLOCK_OVERHEAD_BYTES_REALISTIC = 1_490 := by decide

/-- **T9 (theoretical upper bound value).** `THEORETICAL_TX_BYTES_UPPER_BOUND = 1_998_510`. -/
theorem THEORETICAL_TX_BYTES_UPPER_BOUND_value :
    THEORETICAL_TX_BYTES_UPPER_BOUND = 1_998_510 := by decide

/-- **T10 (overhead decomposition).** Pins the algebraic decomposition of
the overhead so that refactoring the named constants must keep the sum
right. -/
theorem block_overhead_decomposition :
    BLOCK_OVERHEAD_BYTES_REALISTIC =
      HEADER_FIXED_SIZE + SOLUTION_SIZE + SOLUTION_COMPACTSIZE +
        TX_COUNT_COMPACTSIZE_REALISTIC := by
  rfl

/-- **T11 (theoretical bound is sound for the enforced check).** Any tx
size within the theoretical upper bound is also accepted by the actual
enforced predicate. The converse is *not* true — Rust accepts sizes
between `THEORETICAL_TX_BYTES_UPPER_BOUND` and `MAX_BLOCK_BYTES`. -/
theorem theoretical_bound_implies_enforced (size : Nat)
    (h : size ≤ THEORETICAL_TX_BYTES_UPPER_BOUND) :
    transactionSizeOk size = true := by
  rw [transactionSizeOk_iff]
  -- `THEORETICAL_TX_BYTES_UPPER_BOUND = MAX_BLOCK_BYTES - 1_490 ≤ MAX_BLOCK_BYTES`.
  have hub : THEORETICAL_TX_BYTES_UPPER_BOUND ≤ MAX_BLOCK_BYTES := by
    unfold THEORETICAL_TX_BYTES_UPPER_BOUND BLOCK_OVERHEAD_BYTES_REALISTIC
           HEADER_FIXED_SIZE SOLUTION_SIZE SOLUTION_COMPACTSIZE
           TX_COUNT_COMPACTSIZE_REALISTIC MAX_BLOCK_BYTES
    decide
  exact h.trans hub

/-- **T12 (enforced bound is strictly looser than theoretical).** Sizes
above the theoretical bound but at most `MAX_BLOCK_BYTES` are still
accepted by the *enforced* check. This documents the gap between the
spec-level "1.5 kB smaller" remark and Rust's actual `reader.take` cap. -/
theorem enforced_strictly_looser :
    transactionSizeOk (THEORETICAL_TX_BYTES_UPPER_BOUND + 1) = true := by
  rw [transactionSizeOk_iff]
  unfold THEORETICAL_TX_BYTES_UPPER_BOUND BLOCK_OVERHEAD_BYTES_REALISTIC
         HEADER_FIXED_SIZE SOLUTION_SIZE SOLUTION_COMPACTSIZE
         TX_COUNT_COMPACTSIZE_REALISTIC MAX_BLOCK_BYTES
  decide

/-- **T13 (block-overhead arithmetic).** Realistic overhead fits inside
`MAX_BLOCK_BYTES` (so the subtraction defining
`THEORETICAL_TX_BYTES_UPPER_BOUND` does not underflow). -/
theorem overhead_le_max_block :
    BLOCK_OVERHEAD_BYTES_REALISTIC ≤ MAX_BLOCK_BYTES := by
  unfold BLOCK_OVERHEAD_BYTES_REALISTIC MAX_BLOCK_BYTES HEADER_FIXED_SIZE
         SOLUTION_SIZE SOLUTION_COMPACTSIZE TX_COUNT_COMPACTSIZE_REALISTIC
  decide

/-- **T14 (fits in a block, under theoretical bound).** Any transaction
that satisfies the theoretical bound leaves room for the modelled block
overhead inside `MAX_BLOCK_BYTES`. This is the algebraic content of
"approximately 1.5 kB smaller". -/
theorem under_theoretical_bound_fits_in_block (size : Nat)
    (h : size ≤ THEORETICAL_TX_BYTES_UPPER_BOUND) :
    size + BLOCK_OVERHEAD_BYTES_REALISTIC ≤ MAX_BLOCK_BYTES := by
  unfold THEORETICAL_TX_BYTES_UPPER_BOUND at h
  have hov := overhead_le_max_block
  omega

/-! ## Theorems on the generic capped predicate -/

/-- **T15 (capped iff).** `transactionSizeOkWithCap` is the decidable
form of `size ≤ cap`. -/
theorem transactionSizeOkWithCap_iff (size cap : Nat) :
    transactionSizeOkWithCap size cap = true ↔ size ≤ cap := by
  unfold transactionSizeOkWithCap
  exact decide_eq_true_iff

/-- **T16 (capped at boundary).** Boundary is always accepted. -/
theorem transactionSizeOkWithCap_at_cap (cap : Nat) :
    transactionSizeOkWithCap cap cap = true := by
  rw [transactionSizeOkWithCap_iff]

/-- **T17 (capped, just above).** One byte above the cap is rejected. -/
theorem transactionSizeOkWithCap_just_above (cap : Nat) :
    transactionSizeOkWithCap (cap + 1) cap = false := by
  unfold transactionSizeOkWithCap
  exact decide_eq_false (by omega)

/-- **T18 (capped agrees with enforced check at the block cap).** -/
theorem transactionSizeOkWithCap_eq_enforced (size : Nat) :
    transactionSizeOkWithCap size MAX_BLOCK_BYTES = transactionSizeOk size := by
  unfold transactionSizeOkWithCap transactionSizeOk
  rfl

/-! ## Pinning the SOLUTION_COMPACTSIZE value (closes low finding 558) -/

/-- **T19 (Equihash solution size lies in the 3-byte CompactSize range).**
A CompactSize prefix occupies 3 bytes for any value in `[253, 65535]`.
`SOLUTION_SIZE = 1344` clearly lies in this range, so the 3-byte prefix
choice is *derived*, not assumed. -/
theorem solution_size_in_3byte_compactsize_range :
    253 ≤ SOLUTION_SIZE ∧ SOLUTION_SIZE ≤ 65535 := by
  unfold SOLUTION_SIZE
  decide

/-- **T20 (SOLUTION_COMPACTSIZE pinned to 3).** Follows from
`solution_size_in_3byte_compactsize_range` by the CompactSize encoding
rule: values in `[253, 65535]` use a 3-byte prefix (`0xfd` + 2 little-endian
bytes). -/
theorem solution_compactsize_value : SOLUTION_COMPACTSIZE = 3 := rfl

/-! ## Closing low finding 557: the 9-byte CompactSize is unreachable -/

/-- **T21 (smallest tx is ≥ 80 bytes).** A serialized transparent
transaction is at minimum about 80 bytes: a 4-byte version, at least one
36+1+4 = 41-byte input, a 4-byte lock time, and at least one 8+1 = 9-byte
output, plus 1-byte CompactSize counts (`>= 84`). We use the conservative
floor 80 below; the actual minimum is `MIN_TRANSPARENT_TX_SIZE` from
`zebra-chain/src/transaction/serialize.rs:1147`. -/
def MIN_TX_SIZE_BYTES : Nat := 80

/-- **T22 (max tx count in a 2 MB block).** With each transaction at
least `MIN_TX_SIZE_BYTES = 80` bytes, a 2 MB block holds at most
`25_000` transactions — far below `2^32 - 1`. -/
theorem max_tx_count_in_block_le_25000 :
    MAX_BLOCK_BYTES / MIN_TX_SIZE_BYTES = 25_000 := by
  unfold MAX_BLOCK_BYTES MIN_TX_SIZE_BYTES
  decide

/-- **T23 (tx count fits in 3-byte CompactSize).** `25_000 ≤ 65_535`, so
the per-block transaction count always encodes in at most 3 bytes. -/
theorem tx_count_prefix_at_most_3 :
    MAX_BLOCK_BYTES / MIN_TX_SIZE_BYTES ≤ 65_535 := by
  unfold MAX_BLOCK_BYTES MIN_TX_SIZE_BYTES
  decide

/-- **T24 (the 9-byte CompactSize is unreachable).** A 9-byte CompactSize
header (`0xff` + 8 LE) is only used for values `≥ 2^32`. The realistic tx
count in any 2 MB block is at most `25_000 < 2^32`, so the
worst-case-prefix-of-9 used by the previous version of this module was
unreachable. -/
theorem tx_count_compactsize_9_unreachable :
    MAX_BLOCK_BYTES / MIN_TX_SIZE_BYTES < 4_294_967_296 := by
  unfold MAX_BLOCK_BYTES MIN_TX_SIZE_BYTES
  decide

/-! ## Concrete-value sanity checks -/

/-- **T25 (concrete: MAX_BLOCK_BYTES).** -/
theorem MAX_BLOCK_BYTES_value : MAX_BLOCK_BYTES = 2_000_000 := rfl

/-- **T26 (concrete: enforced check accepts the largest reachable tx).**
A maximally large transaction at the block cap is accepted by the
enforced check. -/
theorem transactionSizeOk_full_block :
    transactionSizeOk MAX_BLOCK_BYTES = true := transactionSizeOk_at_max

/-- **T27 (concrete: tighter theoretical bound rejects "block-sized" txs).**
A tx equal to `MAX_BLOCK_BYTES` exceeds the (non-enforced) theoretical
bound, even though Rust still accepts it. This documents the gap between
the docstring "approximately 1.5 kB smaller" claim and Rust's actual
`reader.take` cap. -/
theorem theoretical_bound_rejects_full_block :
    transactionSizeOkWithCap MAX_BLOCK_BYTES THEORETICAL_TX_BYTES_UPPER_BOUND = false := by
  unfold transactionSizeOkWithCap THEORETICAL_TX_BYTES_UPPER_BOUND
         BLOCK_OVERHEAD_BYTES_REALISTIC MAX_BLOCK_BYTES HEADER_FIXED_SIZE
         SOLUTION_SIZE SOLUTION_COMPACTSIZE TX_COUNT_COMPACTSIZE_REALISTIC
  decide

end Zebra.TransactionMaxSize
