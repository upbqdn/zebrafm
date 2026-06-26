import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Consensus-level transaction max-size enforcement

## What Rust actually enforces

At the *consensus* layer, the upstream constraint is:

> "Post-Sapling, transaction size is limited to `MAX_BLOCK_BYTES`. (Strictly, the
> maximum transaction size is about 1.5 kB less, because blocks also include a
> block header.)"
> — `zebra-chain/src/transaction/serialize.rs:506-508`

and on the wire:

> `let mut limited_reader = reader.take(MAX_BLOCK_BYTES);`
> — `zebra-chain/src/transaction/serialize.rs:783`

Two distinct caps coexist here:

  * `MAX_BLOCK_BYTES = 2_000_000` — the **block-level** cap.
    The deserialiser truncates each tx read at this number of bytes, so the
    *loose* per-tx limit Rust enforces is identical to the block limit.
    Source: `zebra-chain/src/block/serialize.rs:24`.

  * The **tight consensus bound** the docstring describes: a single tx that
    actually appears in a block has at most `MAX_BLOCK_BYTES - block_overhead`
    bytes available, where `block_overhead = header + Equihash solution +
    CompactSize tx-count prefix`. We make this concrete below.

`TransactionMaxSize.lean` already pinned the loose Rust `reader.take` cap, the
"approximately 1.5 kB smaller" derived bound, and the unreachability of the
9-byte CompactSize. This module covers a **different** aspect: the
*consensus-level fit* of one or several transactions inside a single block,
plus the trusted-preallocation cap on the **number** of transactions in a block
(`<Transaction as TrustedPreallocate>::max_allocation`) that the wire decoder
uses to bound vector preallocation.

## What this module proves

  * `txFitsInBlockWithHeader` is decidable, monotone in the tx size, anti-tone
    in the header overhead, and exactly characterises when one tx leaves room
    for the rest of the block under `MAX_BLOCK_BYTES`.

  * `txsFitInBlockWithHeader` does the same for a *list* of tx sizes: the sum
    of all tx sizes plus the header overhead must not exceed `MAX_BLOCK_BYTES`.

  * `maxTxAllocation` is `MAX_BLOCK_BYTES / MIN_TRANSPARENT_TX_SIZE`, mirroring
    `<Transaction as TrustedPreallocate>::max_allocation()` at
    `zebra-chain/src/transaction/serialize.rs:1165-1168`. Its concrete value
    `46_511` is pinned, and we prove that no list of `maxTxAllocation + 1`
    minimum-size transparent transactions can fit in a single block.

  * Relations to `MAX_BLOCK_BYTES`: the consensus-tight per-tx bound is
    strictly less than `MAX_BLOCK_BYTES`, the deserialisation cap is *strictly
    looser* than the consensus-tight one, and any tx that survives the tight
    bound also survives the loose `reader.take` cap.

  * Minimum-tx-size arithmetic: each transparent tx is at least
    `MIN_TRANSPARENT_TX_SIZE = 49` bytes, so the per-block count is bounded.
-/

namespace Zebra.ConsensusTxMaxSize

/-! ## Constants -/

/-- `MAX_BLOCK_BYTES`: maximum size of a Zcash block, in bytes.
Source: `zebra-chain/src/block/serialize.rs:24`. -/
def MAX_BLOCK_BYTES : Nat := 2_000_000

/-- Fixed-size portion of a block header (version + prev_hash + merkle_root +
commitment_bytes + time + bits + nonce = 4 + 32 + 32 + 32 + 4 + 4 + 32 = 140).
Source: `zebra-chain/src/block/header.rs` (`pub struct Header`),
also pinned in `Zebra.BlockHeader.HEADER_FIXED_SIZE`. -/
def HEADER_FIXED_SIZE : Nat := 140

/-- Size of the Equihash 200/9 solution payload, in bytes.
Source: `zebra-chain/src/work/equihash.rs:31` (`SOLUTION_SIZE`). -/
def SOLUTION_SIZE : Nat := 1344

/-- CompactSize prefix on the 1344-byte Equihash solution. Values in
`[253, 65535]` use a 3-byte CompactSize prefix; `1344` lies in that range.
Source: `zebra-chain/src/serialization/compact_size.rs`. -/
def SOLUTION_COMPACTSIZE : Nat := 3

/-- CompactSize prefix on the per-block transaction count. For realistic
counts (≤ 65 535) a 3-byte prefix is used; the 9-byte form is unreachable
for any block fitting under `MAX_BLOCK_BYTES`. See
`tx_count_compactsize_unreachable_9` below. -/
def TX_COUNT_COMPACTSIZE : Nat := 3

/-- Total block-overhead bytes other than the transactions themselves:
header + Equihash solution + the two relevant CompactSize prefixes. -/
def BLOCK_OVERHEAD : Nat :=
  HEADER_FIXED_SIZE + SOLUTION_SIZE + SOLUTION_COMPACTSIZE + TX_COUNT_COMPACTSIZE

/-- The consensus-tight per-tx byte budget: how many bytes a single tx can
occupy in a block of size at most `MAX_BLOCK_BYTES`.
This pins the "approximately 1.5 kB smaller" docstring claim from
`zebra-chain/src/transaction/serialize.rs:506-508`. -/
def CONSENSUS_TX_BUDGET : Nat := MAX_BLOCK_BYTES - BLOCK_OVERHEAD

/-- Minimum serialised size of a transparent input, in bytes.
Source: `zebra-chain/src/transaction/serialize.rs:1138`
(`MIN_TRANSPARENT_INPUT_SIZE = 32 + 4 + 4 + 1`). -/
def MIN_TRANSPARENT_INPUT_SIZE : Nat := 32 + 4 + 4 + 1

/-- Minimum serialised size of a transparent output, in bytes.
Source: `zebra-chain/src/transaction/serialize.rs:1141`
(`MIN_TRANSPARENT_OUTPUT_SIZE = 8 + 1`). -/
def MIN_TRANSPARENT_OUTPUT_SIZE : Nat := 8 + 1

/-- Minimum serialised size of a transparent transaction, in bytes.
Source: `zebra-chain/src/transaction/serialize.rs:1147-1148`
(`MIN_TRANSPARENT_TX_SIZE = MIN_TRANSPARENT_INPUT_SIZE + 4 + MIN_TRANSPARENT_OUTPUT_SIZE`). -/
def MIN_TRANSPARENT_TX_SIZE : Nat :=
  MIN_TRANSPARENT_INPUT_SIZE + 4 + MIN_TRANSPARENT_OUTPUT_SIZE

/-- Maximum number of transactions allowable by trusted preallocation in a
single Zcash message containing block-level data. Mirrors
`<Transaction as TrustedPreallocate>::max_allocation()`.
Source: `zebra-chain/src/transaction/serialize.rs:1165-1168`. -/
def maxTxAllocation : Nat := MAX_BLOCK_BYTES / MIN_TRANSPARENT_TX_SIZE

/-! ## The decidable consensus predicate -/

/-- Single-tx consensus fit: `tx_size + header_overhead ≤ MAX_BLOCK_BYTES`.
This is *strictly tighter* than the deserialiser's `reader.take(MAX_BLOCK_BYTES)`
cap (which only enforces `tx_size ≤ MAX_BLOCK_BYTES`); the docstring at
`transaction/serialize.rs:506-508` describes exactly this tighter consensus
budget. -/
def txFitsInBlockWithHeader (txSize headerOverhead : Nat) : Bool :=
  txSize + headerOverhead ≤ MAX_BLOCK_BYTES

/-- Multi-tx consensus fit: the sum of tx sizes plus the header overhead
must not exceed `MAX_BLOCK_BYTES`. Mirrors what a producing miner can
actually fit in one block. -/
def txsFitInBlockWithHeader (txSizes : List Nat) (headerOverhead : Nat) : Bool :=
  txSizes.sum + headerOverhead ≤ MAX_BLOCK_BYTES

/-- The deserialisation-level per-tx cap mirrored from
`transaction/serialize.rs:783`: `reader.take(MAX_BLOCK_BYTES)`. -/
def txDeserCap (txSize : Nat) : Bool := txSize ≤ MAX_BLOCK_BYTES

/-! ## Concrete-value pins -/

/-- **T1 (BLOCK_OVERHEAD value).** Pins the algebraic block overhead to the
exact byte count: `140 + 1344 + 3 + 3 = 1490`. -/
theorem BLOCK_OVERHEAD_value : BLOCK_OVERHEAD = 1490 := by decide

/-- **T2 (CONSENSUS_TX_BUDGET value).** The consensus-tight per-tx byte
budget is `MAX_BLOCK_BYTES - 1490 = 1_998_510`. This pins the "approximately
1.5 kB smaller" claim from `transaction/serialize.rs:506-508` to an exact
number that future overhead changes will surface as a build break. -/
theorem CONSENSUS_TX_BUDGET_value : CONSENSUS_TX_BUDGET = 1_998_510 := by decide

/-- **T3 (MIN_TRANSPARENT_TX_SIZE value).** Pins the structural minimum to
`41 + 4 + 9 = 54` bytes (`MIN_TRANSPARENT_INPUT_SIZE + 4 + MIN_TRANSPARENT_OUTPUT_SIZE`).
Note: a 1-byte CompactSize input count and 1-byte CompactSize output count
add another two bytes when serialising the lists. The Rust constant counts
the inputs/outputs themselves but not their length prefixes. -/
theorem MIN_TRANSPARENT_TX_SIZE_value : MIN_TRANSPARENT_TX_SIZE = 54 := by decide

/-- **T4 (maxTxAllocation value).** Pins the trusted-preallocation cap to
`MAX_BLOCK_BYTES / MIN_TRANSPARENT_TX_SIZE = 2_000_000 / 54 = 37_037`. -/
theorem maxTxAllocation_value : maxTxAllocation = 37037 := by
  unfold maxTxAllocation MAX_BLOCK_BYTES MIN_TRANSPARENT_TX_SIZE
         MIN_TRANSPARENT_INPUT_SIZE MIN_TRANSPARENT_OUTPUT_SIZE
  decide

/-- **T5 (overhead fits in block).** The header overhead is well below
`MAX_BLOCK_BYTES`, so the subtraction defining `CONSENSUS_TX_BUDGET` does
not underflow. -/
theorem BLOCK_OVERHEAD_le_MAX_BLOCK_BYTES :
    BLOCK_OVERHEAD ≤ MAX_BLOCK_BYTES := by
  unfold BLOCK_OVERHEAD HEADER_FIXED_SIZE SOLUTION_SIZE SOLUTION_COMPACTSIZE
         TX_COUNT_COMPACTSIZE MAX_BLOCK_BYTES
  decide

/-! ## The decidable predicate: iff, monotonicity, anti-tonicity -/

/-- **T6 (iff).** `txFitsInBlockWithHeader` is the decidable form of
`txSize + headerOverhead ≤ MAX_BLOCK_BYTES`. -/
theorem txFitsInBlockWithHeader_iff (txSize headerOverhead : Nat) :
    txFitsInBlockWithHeader txSize headerOverhead = true
      ↔ txSize + headerOverhead ≤ MAX_BLOCK_BYTES := by
  unfold txFitsInBlockWithHeader
  exact decide_eq_true_iff

/-- **T7 (anti-tone in tx size).** A smaller tx leaves at least as much room
under the cap as a larger one. -/
theorem txFitsInBlockWithHeader_antitone_tx
    (s₁ s₂ headerOverhead : Nat) (hle : s₁ ≤ s₂)
    (h : txFitsInBlockWithHeader s₂ headerOverhead = true) :
    txFitsInBlockWithHeader s₁ headerOverhead = true := by
  rw [txFitsInBlockWithHeader_iff] at h ⊢
  exact (Nat.add_le_add_right hle headerOverhead).trans h

/-- **T8 (anti-tone in header overhead).** A smaller header overhead leaves
at least as much room for the tx. -/
theorem txFitsInBlockWithHeader_antitone_header
    (txSize h₁ h₂ : Nat) (hle : h₁ ≤ h₂)
    (h : txFitsInBlockWithHeader txSize h₂ = true) :
    txFitsInBlockWithHeader txSize h₁ = true := by
  rw [txFitsInBlockWithHeader_iff] at h ⊢
  exact (Nat.add_le_add_left hle txSize).trans h

/-! ## Concrete-bounds theorems on the consensus-tight predicate -/

/-- **T9 (CONSENSUS_TX_BUDGET is exactly the tight bound).** A tx of exactly
`CONSENSUS_TX_BUDGET` bytes is the largest one that fits in a block with the
full `BLOCK_OVERHEAD` model header. -/
theorem txFitsInBlockWithHeader_at_budget :
    txFitsInBlockWithHeader CONSENSUS_TX_BUDGET BLOCK_OVERHEAD = true := by
  rw [txFitsInBlockWithHeader_iff]
  unfold CONSENSUS_TX_BUDGET
  have := BLOCK_OVERHEAD_le_MAX_BLOCK_BYTES
  omega

/-- **T10 (one byte over the budget is rejected with the modelled header).**
Adding one byte to a tx that already saturates the budget overflows
`MAX_BLOCK_BYTES`. -/
theorem txFitsInBlockWithHeader_just_above_budget :
    txFitsInBlockWithHeader (CONSENSUS_TX_BUDGET + 1) BLOCK_OVERHEAD = false := by
  unfold txFitsInBlockWithHeader CONSENSUS_TX_BUDGET BLOCK_OVERHEAD
         HEADER_FIXED_SIZE SOLUTION_SIZE SOLUTION_COMPACTSIZE
         TX_COUNT_COMPACTSIZE MAX_BLOCK_BYTES
  decide

/-- **T11 (consensus-tight bound is strictly tighter than the deserialiser
cap).** A tx of size exactly `MAX_BLOCK_BYTES` passes the loose `reader.take`
cap but fails the consensus-tight check — this is the gap the docstring at
`transaction/serialize.rs:506-508` warns about. -/
theorem deser_cap_strictly_looser_than_consensus :
    txDeserCap MAX_BLOCK_BYTES = true ∧
    txFitsInBlockWithHeader MAX_BLOCK_BYTES BLOCK_OVERHEAD = false := by
  refine ⟨?_, ?_⟩
  · unfold txDeserCap; exact decide_eq_true (Nat.le_refl _)
  · unfold txFitsInBlockWithHeader BLOCK_OVERHEAD HEADER_FIXED_SIZE
           SOLUTION_SIZE SOLUTION_COMPACTSIZE TX_COUNT_COMPACTSIZE
           MAX_BLOCK_BYTES
    decide

/-- **T12 (consensus-tight ⇒ deserialiser cap).** Any tx that passes the
consensus-tight bound is also accepted by the loose `reader.take` cap. -/
theorem consensus_implies_deser_cap (txSize headerOverhead : Nat)
    (h : txFitsInBlockWithHeader txSize headerOverhead = true) :
    txDeserCap txSize = true := by
  rw [txFitsInBlockWithHeader_iff] at h
  unfold txDeserCap
  exact decide_eq_true (by omega)

/-! ## Multi-tx fitness -/

/-- **T13 (multi-tx iff).** -/
theorem txsFitInBlockWithHeader_iff (txSizes : List Nat) (headerOverhead : Nat) :
    txsFitInBlockWithHeader txSizes headerOverhead = true
      ↔ txSizes.sum + headerOverhead ≤ MAX_BLOCK_BYTES := by
  unfold txsFitInBlockWithHeader
  exact decide_eq_true_iff

/-- **T14 (empty tx list fits).** A block with zero transactions trivially
fits (the modelled overhead is well below `MAX_BLOCK_BYTES`). -/
theorem txsFitInBlockWithHeader_empty :
    txsFitInBlockWithHeader [] BLOCK_OVERHEAD = true := by
  rw [txsFitInBlockWithHeader_iff]
  simp [BLOCK_OVERHEAD_le_MAX_BLOCK_BYTES]

/-- **T15 (cons reduces).** Adding a tx of size `s` to a list `ts` shrinks
the consensus check to `s + sum ts + overhead ≤ MAX_BLOCK_BYTES`. -/
theorem txsFitInBlockWithHeader_cons (s : Nat) (ts : List Nat) (ov : Nat) :
    txsFitInBlockWithHeader (s :: ts) ov = true
      ↔ s + ts.sum + ov ≤ MAX_BLOCK_BYTES := by
  rw [txsFitInBlockWithHeader_iff]
  simp [List.sum_cons]

/-- **T16 (multi-tx is anti-tone under prefix).** Dropping the head of a
list of tx sizes can only help the block fit. -/
theorem txsFitInBlockWithHeader_drop_head (s : Nat) (ts : List Nat) (ov : Nat)
    (h : txsFitInBlockWithHeader (s :: ts) ov = true) :
    txsFitInBlockWithHeader ts ov = true := by
  rw [txsFitInBlockWithHeader_iff] at h ⊢
  simp [List.sum_cons] at h
  omega

/-- **T17 (single-tx vs multi-tx).** The single-tx check is the special
case of the multi-tx check on a one-element list. -/
theorem single_eq_multi (s ov : Nat) :
    txFitsInBlockWithHeader s ov = txsFitInBlockWithHeader [s] ov := by
  unfold txFitsInBlockWithHeader txsFitInBlockWithHeader
  simp [List.sum_cons, List.sum_nil]

/-! ## Trusted preallocation: the per-block tx-count cap -/

/-- **T18 (maxTxAllocation upper-bounds reachable tx counts).** No list of
minimum-size transparent transactions of length `maxTxAllocation + 1` can
fit in a single block, even ignoring header overhead. This is the soundness
side of `<Transaction as TrustedPreallocate>::max_allocation()`. -/
theorem maxTxAllocation_is_upper_bound :
    (maxTxAllocation + 1) * MIN_TRANSPARENT_TX_SIZE > MAX_BLOCK_BYTES := by
  unfold maxTxAllocation MAX_BLOCK_BYTES MIN_TRANSPARENT_TX_SIZE
         MIN_TRANSPARENT_INPUT_SIZE MIN_TRANSPARENT_OUTPUT_SIZE
  decide

/-- **T19 (maxTxAllocation is reachable).** A list of `maxTxAllocation`
minimum-size transparent transactions does fit inside `MAX_BLOCK_BYTES`
(again ignoring header overhead). This is the completeness side — the
Rust cap is tight, not over-conservative. -/
theorem maxTxAllocation_is_reachable :
    maxTxAllocation * MIN_TRANSPARENT_TX_SIZE ≤ MAX_BLOCK_BYTES := by
  unfold maxTxAllocation
  exact Nat.div_mul_le_self _ _

/-- **T20 (preallocation cap is well below `2^32`).** The 9-byte
`CompactSize` form (used only for values `≥ 2^32`) is unreachable for any
realistic per-block tx count — `maxTxAllocation = 37_037 < 2^32`. This
justifies pinning `TX_COUNT_COMPACTSIZE = 3` rather than `9`. -/
theorem tx_count_compactsize_unreachable_9 :
    maxTxAllocation < 4_294_967_296 := by
  rw [maxTxAllocation_value]; decide

/-- **T21 (max-tx-count fits in a 3-byte CompactSize).** Per-block tx
counts at most `maxTxAllocation = 37_037` lie in `[253, 65535]`, hence
encode in 3 bytes — the value pinned in `TX_COUNT_COMPACTSIZE`. -/
theorem tx_count_compactsize_is_3_byte :
    253 ≤ maxTxAllocation ∧ maxTxAllocation ≤ 65535 := by
  rw [maxTxAllocation_value]; decide

/-! ## Realistic worst-case: maximum number of *minimum-size* txs fits -/

/-- Sum of a constant `s` repeated `n` times equals `n * s`. -/
private lemma sum_replicate (n s : Nat) : (List.replicate n s).sum = n * s := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul, Nat.add_comm]

/-- **T22 (a maxTxAllocation-block of min-size txs fits without header).**
The trusted-preallocation cap leaves zero room for a header, but Rust's
preallocation guard fires on counts only. This pin documents what the
attack surface is: an attacker can declare `maxTxAllocation` txs, and the
preallocation will not exceed `MAX_BLOCK_BYTES` bytes of memory. -/
theorem maxTxAllocation_preallocation_bound :
    (List.replicate maxTxAllocation MIN_TRANSPARENT_TX_SIZE).sum
      ≤ MAX_BLOCK_BYTES := by
  rw [sum_replicate]
  exact maxTxAllocation_is_reachable

/-- The maximum number of `MIN_TRANSPARENT_TX_SIZE`-byte transactions that
fits in a block once we *also* reserve `BLOCK_OVERHEAD` bytes for the header,
Equihash solution, and CompactSize prefixes. -/
def maxTxsWithHeader : Nat := (MAX_BLOCK_BYTES - BLOCK_OVERHEAD) / MIN_TRANSPARENT_TX_SIZE

/-- **T23 (header-aware cap is concrete).** With full overhead reserved, at
most `37_009` minimum-size transparent transactions can fit in a block. This
is `(MAX_BLOCK_BYTES - BLOCK_OVERHEAD) / MIN_TRANSPARENT_TX_SIZE`. -/
theorem maxTxsWithHeader_value : maxTxsWithHeader = 37009 := by
  unfold maxTxsWithHeader MAX_BLOCK_BYTES BLOCK_OVERHEAD HEADER_FIXED_SIZE
         SOLUTION_SIZE SOLUTION_COMPACTSIZE TX_COUNT_COMPACTSIZE
         MIN_TRANSPARENT_TX_SIZE MIN_TRANSPARENT_INPUT_SIZE
         MIN_TRANSPARENT_OUTPUT_SIZE
  decide

/-- **T23b (header-aware tx count actually fits).** A block with
`maxTxsWithHeader` minimum-size transactions and the full overhead is
under the cap. -/
theorem maxTxsWithHeader_fits :
    maxTxsWithHeader * MIN_TRANSPARENT_TX_SIZE + BLOCK_OVERHEAD
      ≤ MAX_BLOCK_BYTES := by
  rw [maxTxsWithHeader_value, BLOCK_OVERHEAD_value]
  unfold MIN_TRANSPARENT_TX_SIZE MIN_TRANSPARENT_INPUT_SIZE
         MIN_TRANSPARENT_OUTPUT_SIZE MAX_BLOCK_BYTES
  decide

/-- **T23c (one more does not fit).** Adding one more minimum-size tx pushes
the block past `MAX_BLOCK_BYTES` — `maxTxsWithHeader` is tight. -/
theorem maxTxsWithHeader_plus_one_overflows :
    (maxTxsWithHeader + 1) * MIN_TRANSPARENT_TX_SIZE + BLOCK_OVERHEAD
      > MAX_BLOCK_BYTES := by
  rw [maxTxsWithHeader_value, BLOCK_OVERHEAD_value]
  unfold MIN_TRANSPARENT_TX_SIZE MIN_TRANSPARENT_INPUT_SIZE
         MIN_TRANSPARENT_OUTPUT_SIZE MAX_BLOCK_BYTES
  decide

/-- **T23d (header-aware cap is strictly smaller than preallocation cap).**
The block-fitting count `maxTxsWithHeader` is strictly smaller than the
deserialiser preallocation cap `maxTxAllocation`. Concretely, the gap is
exactly 28 minimum-size transactions — reflecting that 1490 bytes of
header overhead consume the equivalent of `⌈1490/54⌉ = 28` tx slots. -/
theorem maxTxsWithHeader_lt_maxTxAllocation :
    maxTxsWithHeader < maxTxAllocation := by
  rw [maxTxsWithHeader_value, maxTxAllocation_value]
  decide

/-- **T24 (maxTxAllocation min-size txs with full header does NOT fit).**
With the full `BLOCK_OVERHEAD` (1490 bytes) the trusted-preallocation cap
`maxTxAllocation` itself overshoots `MAX_BLOCK_BYTES` — i.e. the
preallocation cap is what an *attacker* can force the deserialiser to
allocate, not what a *miner* can fit in a block. The consensus check is
strictly stronger than the wire-allocation check. -/
theorem maxTxAllocation_with_header_does_not_fit :
    txsFitInBlockWithHeader
      (List.replicate maxTxAllocation MIN_TRANSPARENT_TX_SIZE) BLOCK_OVERHEAD
      = false := by
  unfold txsFitInBlockWithHeader
  rw [sum_replicate]
  rw [maxTxAllocation_value, BLOCK_OVERHEAD_value]
  unfold MIN_TRANSPARENT_TX_SIZE MIN_TRANSPARENT_INPUT_SIZE
         MIN_TRANSPARENT_OUTPUT_SIZE MAX_BLOCK_BYTES
  decide

/-! ## Sanity checks -/

/-- **T25 (MAX_BLOCK_BYTES concrete value).** -/
theorem MAX_BLOCK_BYTES_value : MAX_BLOCK_BYTES = 2_000_000 := rfl

/-- **T26 (HEADER_FIXED_SIZE decomposition).** Matches
`Zebra.BlockHeader.HEADER_FIXED_SIZE`: `4 + 32 + 32 + 32 + 4 + 4 + 32`. -/
theorem HEADER_FIXED_SIZE_decomposition :
    HEADER_FIXED_SIZE = 4 + 32 + 32 + 32 + 4 + 4 + 32 := rfl

/-- **T27 (CONSENSUS_TX_BUDGET stays below MAX_BLOCK_BYTES).** A safety
margin: even when an attacker tries to forge a tx that saturates the
consensus budget, the resulting blob is still smaller than the
deserialiser cap. -/
theorem CONSENSUS_TX_BUDGET_lt_MAX_BLOCK_BYTES :
    CONSENSUS_TX_BUDGET < MAX_BLOCK_BYTES := by
  rw [CONSENSUS_TX_BUDGET_value]
  unfold MAX_BLOCK_BYTES
  decide

end Zebra.ConsensusTxMaxSize
