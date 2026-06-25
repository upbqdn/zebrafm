import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Transaction maximum serialized size

Post-Sapling, a single Zcash transaction is constrained to fit inside one block.
The block-level cap is `MAX_BLOCK_BYTES = 2_000_000`, but a block also carries a
header and a CompactSize transaction count, so the per-transaction cap is
strictly smaller:

> Post-Sapling, this is also the maximum size of a transaction in the Zcash
> specification. (But since blocks also contain a block header and transaction
> count, the maximum size of a transaction in the chain is approximately 1.5 kB
> smaller.)
> — `zebra-chain/src/block/serialize.rs:18`

We pin down "approximately 1.5 kB smaller" with a concrete fixed overhead model
matching the Rust layout:

  * `HEADER_FIXED_SIZE = 140` (version + 3*32 + time + bits + nonce; see
    `BlockHeader.lean`)
  * `SOLUTION_SIZE = 1344` (Equihash 200/9 solution payload;
    `zebra-chain/src/work/equihash.rs:31`)
  * `SOLUTION_COMPACTSIZE = 3` (CompactSize prefix for the 1344-byte solution)
  * `TX_COUNT_COMPACTSIZE_MAX = 9` (worst-case CompactSize for the tx count)

giving `BLOCK_OVERHEAD_BYTES = 140 + 1344 + 3 + 9 = 1_496` (i.e. ~1.5 kB) and
`MAX_TX_BYTES = MAX_BLOCK_BYTES - BLOCK_OVERHEAD_BYTES = 1_998_504`.

The `transactionSizeOk` predicate accepts a candidate transaction size iff
`size ≤ MAX_TX_BYTES`, mirroring the `reader.take(MAX_BLOCK_BYTES)` and
preallocation guards in `zebra-chain/src/serialization/constraint.rs`.

We prove the predicate is:
  * **decidable** (a `Bool`-valued comparison),
  * **monotone (anti-tone) in size** (shrinking a tx never breaks the check),
  * **boundary-accepting** at exactly `MAX_TX_BYTES`,
  * **rejecting** at `MAX_TX_BYTES + 1`,

plus a handful of concrete sanity values.
-/

namespace Zebra.TransactionMaxSize

/-! ## Constants -/

/-- `MAX_BLOCK_BYTES`: maximum size of a Zcash block, in bytes.
Source: `zebra-chain/src/block/serialize.rs:24` -/
def MAX_BLOCK_BYTES : Nat := 2_000_000

/-- Fixed-size portion of a block header. Matches `Zebra.BlockHeader.HEADER_FIXED_SIZE`.
Source: `zebra-chain/src/block/header.rs:27` (`pub struct Header`) -/
def HEADER_FIXED_SIZE : Nat := 140

/-- Size of the Equihash 200/9 solution payload, in bytes.
Source: `zebra-chain/src/work/equihash.rs:31` (`SOLUTION_SIZE`) -/
def SOLUTION_SIZE : Nat := 1344

/-- CompactSize prefix on the 1344-byte solution: `0xfd` + 2 little-endian bytes.
Source: `zebra-chain/src/serialization/compact_size.rs` (CompactSize encoding;
values in `[253, 65535]` take 3 bytes). -/
def SOLUTION_COMPACTSIZE : Nat := 3

/-- Worst-case CompactSize prefix for the per-block transaction count: `0xff`
plus 8 little-endian bytes. In practice the prefix is 1 byte (≤ 252 txs); we use
the worst case so the overhead bound is an upper bound. -/
def TX_COUNT_COMPACTSIZE_MAX : Nat := 9

/-- Total per-block overhead other than the transactions themselves:
header + solution + compact-size prefixes. -/
def BLOCK_OVERHEAD_BYTES : Nat :=
  HEADER_FIXED_SIZE + SOLUTION_SIZE + SOLUTION_COMPACTSIZE + TX_COUNT_COMPACTSIZE_MAX

/-- `MAX_TX_BYTES`: an upper bound on the serialized size of a single
transaction that can fit in a block. Equals `MAX_BLOCK_BYTES - BLOCK_OVERHEAD_BYTES`.
Source: `zebra-chain/src/block/serialize.rs:18-23` (docstring on `MAX_BLOCK_BYTES`). -/
def MAX_TX_BYTES : Nat := MAX_BLOCK_BYTES - BLOCK_OVERHEAD_BYTES

/-! ## Predicate -/

/-- The transaction-size guard: accept iff `size ≤ MAX_TX_BYTES`.
Source: `zebra-chain/src/serialization/constraint.rs` (bounded-length checks)
and `zebra-chain/src/block/serialize.rs:158` (`reader.take(MAX_BLOCK_BYTES)`). -/
def transactionSizeOk (size : Nat) : Bool := size ≤ MAX_TX_BYTES

/-- A generic guard parameterised by the block-overhead estimate, useful for
clients that compute the overhead exactly (e.g. with a 1-byte tx-count prefix
when fewer than 253 transactions are present). -/
def transactionSizeOkWithOverhead (size overhead : Nat) : Bool :=
  size + overhead ≤ MAX_BLOCK_BYTES

/-! ## Theorems -/

/-- **T1 (decidable).** `transactionSizeOk` is just a comparison: it agrees with
`size ≤ MAX_TX_BYTES` as a proposition. This pins down decidability and is the
workhorse rewrite the rest of the file uses. -/
theorem transactionSizeOk_iff (size : Nat) :
    transactionSizeOk size = true ↔ size ≤ MAX_TX_BYTES := by
  unfold transactionSizeOk
  exact decide_eq_true_iff

/-- **T2 (anti-tone in size).** Shrinking a transaction never invalidates it. -/
theorem transactionSizeOk_antitone (s₁ s₂ : Nat) (hle : s₁ ≤ s₂)
    (h : transactionSizeOk s₂ = true) : transactionSizeOk s₁ = true := by
  rw [transactionSizeOk_iff] at h ⊢
  exact hle.trans h

/-- **T3 (boundary accepted).** A transaction of *exactly* `MAX_TX_BYTES`
bytes is accepted. -/
theorem transactionSizeOk_at_max :
    transactionSizeOk MAX_TX_BYTES = true := by
  rw [transactionSizeOk_iff]

/-- **T4 (limit + 1 rejected).** A transaction one byte over the limit is
rejected. -/
theorem transactionSizeOk_just_above :
    transactionSizeOk (MAX_TX_BYTES + 1) = false := by
  unfold transactionSizeOk
  exact decide_eq_false (by omega)

/-- **T5 (rejection is exact).** Any size strictly above `MAX_TX_BYTES` is
rejected. -/
theorem transactionSizeOk_reject_above (size : Nat) (h : MAX_TX_BYTES < size) :
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

/-- **T7 (fits in a block).** Any accepted transaction, together with the
block overhead, still fits inside `MAX_BLOCK_BYTES`. This is the *reason* the
per-transaction limit is set this way. -/
theorem accepted_tx_fits_in_block (size : Nat)
    (h : transactionSizeOk size = true) :
    size + BLOCK_OVERHEAD_BYTES ≤ MAX_BLOCK_BYTES := by
  rw [transactionSizeOk_iff] at h
  unfold MAX_TX_BYTES at h
  -- `size ≤ MAX_BLOCK_BYTES - BLOCK_OVERHEAD_BYTES` together with the concrete
  -- inequality `BLOCK_OVERHEAD_BYTES ≤ MAX_BLOCK_BYTES` gives the bound.
  have hov : BLOCK_OVERHEAD_BYTES ≤ MAX_BLOCK_BYTES := by
    unfold BLOCK_OVERHEAD_BYTES MAX_BLOCK_BYTES HEADER_FIXED_SIZE SOLUTION_SIZE
           SOLUTION_COMPACTSIZE TX_COUNT_COMPACTSIZE_MAX
    decide
  omega

/-- **T8 (overhead variant boundary).** The overhead-parameterised predicate
accepts exactly at the boundary `size + overhead = MAX_BLOCK_BYTES`. -/
theorem transactionSizeOkWithOverhead_at_boundary (overhead : Nat)
    (h : overhead ≤ MAX_BLOCK_BYTES) :
    transactionSizeOkWithOverhead (MAX_BLOCK_BYTES - overhead) overhead = true := by
  unfold transactionSizeOkWithOverhead
  -- `(MAX_BLOCK_BYTES - overhead) + overhead = MAX_BLOCK_BYTES ≤ MAX_BLOCK_BYTES`.
  have : MAX_BLOCK_BYTES - overhead + overhead = MAX_BLOCK_BYTES := by omega
  rw [this]
  exact decide_eq_true (le_refl _)

/-- **T9 (overhead variant rejects one past boundary).** -/
theorem transactionSizeOkWithOverhead_just_above (overhead : Nat)
    (h : overhead ≤ MAX_BLOCK_BYTES) :
    transactionSizeOkWithOverhead (MAX_BLOCK_BYTES - overhead + 1) overhead = false := by
  unfold transactionSizeOkWithOverhead
  have : MAX_BLOCK_BYTES - overhead + 1 + overhead = MAX_BLOCK_BYTES + 1 := by omega
  rw [this]
  exact decide_eq_false (by omega)

/-- **T10 (overhead-variant agrees with the canonical predicate).** With the
worst-case overhead `BLOCK_OVERHEAD_BYTES`, the parameterised predicate
coincides with `transactionSizeOk`. -/
theorem transactionSizeOkWithOverhead_eq_canonical (size : Nat) :
    transactionSizeOkWithOverhead size BLOCK_OVERHEAD_BYTES =
      transactionSizeOk size := by
  unfold transactionSizeOkWithOverhead transactionSizeOk MAX_TX_BYTES
  -- `size + overhead ≤ B ↔ size ≤ B - overhead`, given `overhead ≤ B`.
  have hov : BLOCK_OVERHEAD_BYTES ≤ MAX_BLOCK_BYTES := by
    unfold BLOCK_OVERHEAD_BYTES MAX_BLOCK_BYTES HEADER_FIXED_SIZE SOLUTION_SIZE
           SOLUTION_COMPACTSIZE TX_COUNT_COMPACTSIZE_MAX
    decide
  by_cases hs : size + BLOCK_OVERHEAD_BYTES ≤ MAX_BLOCK_BYTES
  · have h1 : size ≤ MAX_BLOCK_BYTES - BLOCK_OVERHEAD_BYTES := by omega
    simp [hs, h1]
  · have h1 : ¬ size ≤ MAX_BLOCK_BYTES - BLOCK_OVERHEAD_BYTES := by omega
    simp [hs, h1]

/-- **T11 (tighter overhead also accepts the canonical max).** When the real
tx-count CompactSize fits in 1 byte (the common case: ≤ 252 transactions in the
block), the actual overhead is 8 bytes smaller than the worst case. Any
transaction accepted by the canonical (worst-case-overhead) predicate is then
also accepted by the tighter predicate. -/
theorem canonical_accepted_under_smaller_overhead (size overhead : Nat)
    (hov : overhead ≤ BLOCK_OVERHEAD_BYTES)
    (h : transactionSizeOk size = true) :
    transactionSizeOkWithOverhead size overhead = true := by
  rw [transactionSizeOk_iff] at h
  unfold MAX_TX_BYTES at h
  unfold transactionSizeOkWithOverhead
  have hbig : BLOCK_OVERHEAD_BYTES ≤ MAX_BLOCK_BYTES := by
    unfold BLOCK_OVERHEAD_BYTES MAX_BLOCK_BYTES HEADER_FIXED_SIZE SOLUTION_SIZE
           SOLUTION_COMPACTSIZE TX_COUNT_COMPACTSIZE_MAX
    decide
  exact decide_eq_true (by omega)

/-! ## Concrete-value sanity checks -/

/-- **T12 (concrete: overhead is ≈ 1.5 kB).** Pins the docstring claim
"approximately 1.5 kB smaller" to the exact value `1_496` bytes. -/
theorem BLOCK_OVERHEAD_BYTES_value : BLOCK_OVERHEAD_BYTES = 1_496 := by decide

/-- **T13 (concrete: per-tx cap).** `MAX_TX_BYTES = 1_998_504`. -/
theorem MAX_TX_BYTES_value : MAX_TX_BYTES = 1_998_504 := by decide

/-- **T14 (concrete: 1-byte tx-count case).** With a 1-byte CompactSize tx count
(blocks of ≤ 252 transactions), the per-tx cap rises by 8 to `1_998_512`. -/
theorem max_tx_with_small_tx_count :
    MAX_BLOCK_BYTES - (HEADER_FIXED_SIZE + SOLUTION_SIZE + SOLUTION_COMPACTSIZE + 1)
      = 1_998_512 := by decide

/-- **T15 (concrete: empty tx accepted).** A 0-byte (degenerate) transaction
fits in any block. -/
theorem transactionSizeOk_zero : transactionSizeOk 0 = true := by
  rw [transactionSizeOk_iff]; exact Nat.zero_le _

/-- **T16 (concrete: tx the size of a whole block is rejected).** A "tx" of
size `MAX_BLOCK_BYTES` is way over the per-tx cap. -/
theorem transactionSizeOk_full_block : transactionSizeOk MAX_BLOCK_BYTES = false := by
  unfold transactionSizeOk MAX_TX_BYTES MAX_BLOCK_BYTES BLOCK_OVERHEAD_BYTES
         HEADER_FIXED_SIZE SOLUTION_SIZE SOLUTION_COMPACTSIZE TX_COUNT_COMPACTSIZE_MAX
  decide

/-- **T17 (concrete: block-overhead decomposition).** Pins the algebraic
decomposition of the overhead so refactors of the named constants must keep
the sum right. -/
theorem block_overhead_decomposition :
    BLOCK_OVERHEAD_BYTES =
      HEADER_FIXED_SIZE + SOLUTION_SIZE + SOLUTION_COMPACTSIZE + TX_COUNT_COMPACTSIZE_MAX := by
  rfl

end Zebra.TransactionMaxSize
