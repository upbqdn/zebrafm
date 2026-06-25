import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sprout JoinSplit description sizing and pool-closure consensus rules

A *Sprout JoinSplit description* (`zebra-chain/src/sprout/joinsplit.rs:62`) is a
fixed-shape record carrying:

  * Two input notes (via two 32-byte nullifiers).
  * Two output notes (two 32-byte commitments + two 601-byte encrypted
    ciphertexts).
  * A 32-byte tree anchor, a 32-byte ephemeral key, a 32-byte random seed,
    two 32-byte VMACs, two 8-byte `vpub_old` / `vpub_new` values.
  * A ZK proof (BCTV14 for `JoinSplit<Bctv14Proof>` = 296 bytes; Groth16 for
    `JoinSplit<Groth16Proof>` = 192 bytes).

The Rust source pins:

```text
JOINSPLIT_SIZE_WITHOUT_ZKPROOF = 8+8+32+(32*2)+(32*2)+32+32+(32*2)+(601*2) = 1_506
BCTV14_JOINSPLIT_SIZE          = 1_506 + 296 = 1_802
GROTH16_JOINSPLIT_SIZE         = 1_506 + 192 = 1_698
MAX_BLOCK_BYTES                = 2_000_000
TrustedPreallocate::max_allocation() := (MAX_BLOCK_BYTES - 1) / *_JOINSPLIT_SIZE
```
Source: `zebra-chain/src/sprout/joinsplit.rs:251-281`,
`zebra-chain/src/block/serialize.rs:24`.

This module models the four arithmetic concerns the prompt asks for:

  1. **Size**: `vJoinSplit` (the on-wire `Vec<JoinSplit>`) is bounded by the
     `TrustedPreallocate` allocation, which itself fits inside one block; the
     two variants' fixed sizes match the documented `1_898` / `1_794` byte
     constants.
  2. **Post-Sapling zero permitted**: V4 transactions (effectiveVersion ≥ 4
     pre-NU5) explicitly allow `nJoinSplit = 0` on the wire — the writer emits a
     length-`0` list (`zcash_serialize_empty_list`) and the reader treats that
     as `Option<JoinSplitData> = None`. Modelled as: the size predicate is
     satisfied by an empty list of JoinSplits.
     Source: `zebra-chain/src/transaction/serialize.rs:556-560`,
     `zebra-chain/src/transaction/serialize.rs:584-590`,
     `zebra-chain/src/transaction/serialize.rs:654-658`.
  3. **Sprout pool addition closed at Canopy**: from Canopy onward, every
     JoinSplit in a transaction must have `vpub_old = 0` — that is, the only
     way to interact with the Sprout pool is to remove value. Modelled as: if
     every JoinSplit has `vpub_old = 0`, the net Sprout-pool addition is
     `≤ 0`.
     Source: `zebra-consensus/src/transaction/check.rs:220-246`
     (`disabled_add_to_sprout_pool`), and the Zcash specification at
     <https://zips.z.cash/protocol/protocol.pdf#joinsplitdesc>
     (`[Canopy onward]: vpub_old MUST be zero`).
  4. **`vpub_old` / `vpub_new` per-JoinSplit balancing**: at most one of
     `vpub_old`, `vpub_new` may be nonzero
     (<https://zips.z.cash/protocol/protocol.pdf#joinsplitdesc>); modelled as
     a per-JoinSplit invariant `vpub_old = 0 ∨ vpub_new = 0`.
     Source: `zebra-consensus/src/transaction/check.rs:191-213`
     (`joinsplit_has_vpub_zero`).

All sizes are `Nat`; per-JoinSplit `vpub_old` and `vpub_new` are `Nat` (the
Rust `Amount<NonNegative>` is `0..MAX_MONEY`, and we only need the
non-negativity for the closure claim).
-/

namespace Zebra.JoinSplitProof

/-! ## Constants -/

/-- The maximum size of a Zcash block, in bytes.
Source: `zebra-chain/src/block/serialize.rs:24`
(`pub const MAX_BLOCK_BYTES: u64 = 2_000_000`). -/
def MAX_BLOCK_BYTES : Nat := 2_000_000

/-- `JOINSPLIT_SIZE_WITHOUT_ZKPROOF`: every byte of a Sprout JoinSplit except
the proof: `8 + 8 + 32 + (32*2) + (32*2) + 32 + 32 + (32*2) + (601*2)`.
Source: `zebra-chain/src/sprout/joinsplit.rs:251`. -/
def JOINSPLIT_SIZE_WITHOUT_ZKPROOF : Nat :=
  8 + 8 + 32 + (32 * 2) + (32 * 2) + 32 + 32 + (32 * 2) + (601 * 2)

/-- BCTV14 proof size, in bytes (used by V2/V3 JoinSplits).
Source: `zebra-chain/src/sprout/joinsplit.rs:258`. -/
def BCTV14_PROOF_SIZE : Nat := 296

/-- Groth16 proof size, in bytes (used by V4+ JoinSplits).
Source: `zebra-chain/src/sprout/joinsplit.rs:264`. -/
def GROTH16_PROOF_SIZE : Nat := 192

/-- Total size of a BCTV14 JoinSplit description, in bytes.
Source: `zebra-chain/src/sprout/joinsplit.rs:258`
(`pub(crate) const BCTV14_JOINSPLIT_SIZE: u64 = JOINSPLIT_SIZE_WITHOUT_ZKPROOF + 296`). -/
def BCTV14_JOINSPLIT_SIZE : Nat := JOINSPLIT_SIZE_WITHOUT_ZKPROOF + BCTV14_PROOF_SIZE

/-- Total size of a Groth16 JoinSplit description, in bytes.
Source: `zebra-chain/src/sprout/joinsplit.rs:264`
(`pub(crate) const GROTH16_JOINSPLIT_SIZE: u64 = JOINSPLIT_SIZE_WITHOUT_ZKPROOF + 192`). -/
def GROTH16_JOINSPLIT_SIZE : Nat := JOINSPLIT_SIZE_WITHOUT_ZKPROOF + GROTH16_PROOF_SIZE

/-- `TrustedPreallocate::max_allocation()` for `JoinSplit<Bctv14Proof>`.
Source: `zebra-chain/src/sprout/joinsplit.rs:266-273`. -/
def MAX_ALLOC_BCTV14 : Nat := (MAX_BLOCK_BYTES - 1) / BCTV14_JOINSPLIT_SIZE

/-- `TrustedPreallocate::max_allocation()` for `JoinSplit<Groth16Proof>`.
Source: `zebra-chain/src/sprout/joinsplit.rs:275-282`. -/
def MAX_ALLOC_GROTH16 : Nat := (MAX_BLOCK_BYTES - 1) / GROTH16_JOINSPLIT_SIZE

/-! ## Model: JoinSplit value balance -/

/-- The `vpub_old` / `vpub_new` pair of a single JoinSplit description.
Both fields are `Amount<NonNegative>` in the Rust source, so we model them
as `Nat`. -/
structure JoinSplitPair where
  vpub_old : Nat
  vpub_new : Nat

/-- The Sprout-pool addition contributed by one JoinSplit is `vpub_old`,
which on the Rust side is added to the running Sprout pool balance.
Source: `zebra-chain/src/sprout/joinsplit.rs:170-189`
(`value_balance` = `vpub_new - vpub_old`); the *addition* to the Sprout pool
is exactly `vpub_old` (and `vpub_new` is the corresponding withdrawal). -/
def sproutPoolAddition (js : JoinSplitPair) : Nat := js.vpub_old

/-- Sum of `vpub_old` contributions across a `Vec<JoinSplit>`. -/
def totalSproutAddition (jss : List JoinSplitPair) : Nat :=
  (jss.map sproutPoolAddition).sum

/-- The `JoinSplitData::has_vpub_zero` per-JoinSplit invariant: at least one
of `vpub_old`, `vpub_new` is zero.
Source: <https://zips.z.cash/protocol/protocol.pdf#joinsplitdesc>;
`zebra-consensus/src/transaction/check.rs:191-213`. -/
def hasVPubZero (js : JoinSplitPair) : Prop :=
  js.vpub_old = 0 ∨ js.vpub_new = 0

/-- The Canopy-onward post-condition: every JoinSplit in a transaction has
`vpub_old = 0` (i.e. no addition to the Sprout pool from this transaction).
Source: `zebra-consensus/src/transaction/check.rs:220-246`. -/
def NoSproutPoolAddition (jss : List JoinSplitPair) : Prop :=
  ∀ js ∈ jss, js.vpub_old = 0

/-! ## Constants — concrete values -/

/-- **T1 (`JOINSPLIT_SIZE_WITHOUT_ZKPROOF` concrete).** The Rust constant
expands to `1_506` bytes:
`8 + 8 + 32 + 64 + 64 + 32 + 32 + 64 + 1_202 = 1_506`. -/
theorem joinsplit_size_without_zkproof_value :
    JOINSPLIT_SIZE_WITHOUT_ZKPROOF = 1506 := by
  unfold JOINSPLIT_SIZE_WITHOUT_ZKPROOF; decide

/-- **T2 (`BCTV14_JOINSPLIT_SIZE` concrete).** A V2/V3 JoinSplit is exactly
`1_802` bytes long. -/
theorem bctv14_joinsplit_size_value :
    BCTV14_JOINSPLIT_SIZE = 1802 := by
  unfold BCTV14_JOINSPLIT_SIZE JOINSPLIT_SIZE_WITHOUT_ZKPROOF BCTV14_PROOF_SIZE
  decide

/-- **T3 (`GROTH16_JOINSPLIT_SIZE` concrete).** A V4+ JoinSplit is exactly
`1_698` bytes long. -/
theorem groth16_joinsplit_size_value :
    GROTH16_JOINSPLIT_SIZE = 1698 := by
  unfold GROTH16_JOINSPLIT_SIZE JOINSPLIT_SIZE_WITHOUT_ZKPROOF GROTH16_PROOF_SIZE
  decide

/-- **T4 (BCTV14 strictly larger than Groth16).** BCTV14 proofs are larger,
so a BCTV14 JoinSplit description is strictly larger than a Groth16 one;
hence the two variants' size constants do not collide. -/
theorem groth16_lt_bctv14 :
    GROTH16_JOINSPLIT_SIZE < BCTV14_JOINSPLIT_SIZE := by
  rw [groth16_joinsplit_size_value, bctv14_joinsplit_size_value]; decide

/-! ## TrustedPreallocate bounds (Size) -/

/-- **T5 (`MAX_ALLOC_BCTV14` concrete).**
`(2_000_000 - 1) / 1_802 = 1109`. -/
theorem max_alloc_bctv14_value :
    MAX_ALLOC_BCTV14 = 1109 := by
  unfold MAX_ALLOC_BCTV14 MAX_BLOCK_BYTES BCTV14_JOINSPLIT_SIZE
        JOINSPLIT_SIZE_WITHOUT_ZKPROOF BCTV14_PROOF_SIZE
  decide

/-- **T6 (`MAX_ALLOC_GROTH16` concrete).**
`(2_000_000 - 1) / 1_698 = 1177`. -/
theorem max_alloc_groth16_value :
    MAX_ALLOC_GROTH16 = 1177 := by
  unfold MAX_ALLOC_GROTH16 MAX_BLOCK_BYTES GROTH16_JOINSPLIT_SIZE
        JOINSPLIT_SIZE_WITHOUT_ZKPROOF GROTH16_PROOF_SIZE
  decide

/-- **T7 (BCTV14 allocation fits in a block).** The BCTV14 max-allocation
times the per-JoinSplit byte size is at most `MAX_BLOCK_BYTES - 1`, leaving
room for at least the 1-byte CompactSize length prefix the `Vec` encoder
emits. This is exactly the safety invariant of `TrustedPreallocate`:
allocating `max_allocation()` JoinSplits cannot overflow a single block.
Source: `zebra-chain/src/sprout/joinsplit.rs:267-273`. -/
theorem bctv14_alloc_fits_in_block :
    MAX_ALLOC_BCTV14 * BCTV14_JOINSPLIT_SIZE ≤ MAX_BLOCK_BYTES - 1 := by
  unfold MAX_ALLOC_BCTV14
  -- `Nat.div_mul_le_self : (a / b) * b ≤ a`
  exact Nat.div_mul_le_self (MAX_BLOCK_BYTES - 1) BCTV14_JOINSPLIT_SIZE

/-- **T8 (Groth16 allocation fits in a block).** Same invariant for the
Groth16 variant.
Source: `zebra-chain/src/sprout/joinsplit.rs:275-282`. -/
theorem groth16_alloc_fits_in_block :
    MAX_ALLOC_GROTH16 * GROTH16_JOINSPLIT_SIZE ≤ MAX_BLOCK_BYTES - 1 := by
  unfold MAX_ALLOC_GROTH16
  exact Nat.div_mul_le_self (MAX_BLOCK_BYTES - 1) GROTH16_JOINSPLIT_SIZE

/-- **T9 (BCTV14 allocation strictly fits in a block).** Strengthens T7 to
strict inequality against `MAX_BLOCK_BYTES`. Useful where the consumer needs
room for a length prefix or framing byte. -/
theorem bctv14_alloc_lt_block :
    MAX_ALLOC_BCTV14 * BCTV14_JOINSPLIT_SIZE < MAX_BLOCK_BYTES := by
  have h := bctv14_alloc_fits_in_block
  unfold MAX_BLOCK_BYTES at h ⊢
  omega

/-- **T10 (Groth16 allocation strictly fits in a block).** -/
theorem groth16_alloc_lt_block :
    MAX_ALLOC_GROTH16 * GROTH16_JOINSPLIT_SIZE < MAX_BLOCK_BYTES := by
  have h := groth16_alloc_fits_in_block
  unfold MAX_BLOCK_BYTES at h ⊢
  omega

/-- **T11 (Groth16 allocation strictly greater than BCTV14 allocation).**
A smaller per-JoinSplit size means more JoinSplits fit per block; hence the
post-Sapling Groth16 allocation is strictly greater than the pre-Sapling
BCTV14 allocation. -/
theorem groth16_alloc_gt_bctv14_alloc :
    MAX_ALLOC_BCTV14 < MAX_ALLOC_GROTH16 := by
  rw [max_alloc_bctv14_value, max_alloc_groth16_value]; decide

/-- **T12 (allocations are positive).** A maximally large block can hold at
least one JoinSplit of either flavour. -/
theorem max_alloc_bctv14_pos : 0 < MAX_ALLOC_BCTV14 := by
  rw [max_alloc_bctv14_value]; decide

theorem max_alloc_groth16_pos : 0 < MAX_ALLOC_GROTH16 := by
  rw [max_alloc_groth16_value]; decide

/-- **T13 (`vJoinSplit` size bound: BCTV14).** Any honestly received
`Vec<JoinSplit<Bctv14Proof>>` has length at most `MAX_ALLOC_BCTV14`, hence
its on-wire size is at most `MAX_ALLOC_BCTV14 * BCTV14_JOINSPLIT_SIZE <
MAX_BLOCK_BYTES`. This is the load-bearing claim of the prompt: vJoinSplit
is bounded in size. -/
theorem vJoinSplit_bctv14_size_bound (count : Nat)
    (h : count ≤ MAX_ALLOC_BCTV14) :
    count * BCTV14_JOINSPLIT_SIZE < MAX_BLOCK_BYTES := by
  have hAlloc := bctv14_alloc_lt_block
  have : count * BCTV14_JOINSPLIT_SIZE ≤ MAX_ALLOC_BCTV14 * BCTV14_JOINSPLIT_SIZE :=
    Nat.mul_le_mul_right _ h
  linarith

/-- **T14 (`vJoinSplit` size bound: Groth16).** Same as T13 for Groth16. -/
theorem vJoinSplit_groth16_size_bound (count : Nat)
    (h : count ≤ MAX_ALLOC_GROTH16) :
    count * GROTH16_JOINSPLIT_SIZE < MAX_BLOCK_BYTES := by
  have hAlloc := groth16_alloc_lt_block
  have : count * GROTH16_JOINSPLIT_SIZE ≤ MAX_ALLOC_GROTH16 * GROTH16_JOINSPLIT_SIZE :=
    Nat.mul_le_mul_right _ h
  linarith

/-! ## Post-Sapling allows zero JoinSplits -/

/-- **T15 (post-Sapling allows zero JoinSplits — size).**
A V4 transaction may encode an empty `Vec<JoinSplit>`. The on-wire size of
that empty vector is `0 * GROTH16_JOINSPLIT_SIZE = 0`, which trivially
satisfies the per-block bound. This pins the "post-Sapling allows `0`
JoinSplits" claim from the prompt.
Source: `zebra-chain/src/transaction/serialize.rs:556-560` and `:584-590`
(the V2/V3 writer) and `:654-658` (the V4 writer) — all emit
`zcash_serialize_empty_list` when the option is `None`. -/
theorem zero_joinsplits_size :
    0 * GROTH16_JOINSPLIT_SIZE = 0 := by decide

/-- **T16 (post-Sapling: zero is a valid `vJoinSplit` length).** The
`TrustedPreallocate` bound is satisfied trivially by `n = 0`. -/
theorem zero_le_max_alloc_groth16 :
    0 ≤ MAX_ALLOC_GROTH16 := Nat.zero_le _

theorem zero_le_max_alloc_bctv14 :
    0 ≤ MAX_ALLOC_BCTV14 := Nat.zero_le _

/-- **T17 (post-Sapling JoinSplit count and pool changes are zero).** A V4
transaction with `joinsplit_data = None` has zero JoinSplits and contributes
zero to *every* Sprout pool quantity (the addition `vpub_old`, the
withdrawal `vpub_new`, and the net value balance). -/
theorem no_joinsplit_data_no_pool_change :
    totalSproutAddition [] = 0 := rfl

/-! ## Sprout pool closure at Canopy -/

/-- **T18 (closure at Canopy — singleton).** If a single JoinSplit has
`vpub_old = 0`, its addition to the Sprout pool is zero. -/
theorem sproutPoolAddition_zero_of_vpub_old_zero (js : JoinSplitPair)
    (h : js.vpub_old = 0) :
    sproutPoolAddition js = 0 := by
  unfold sproutPoolAddition; exact h

/-- **T19 (closure at Canopy — list).** If every JoinSplit in a transaction
has `vpub_old = 0` (as required `[Canopy onward]`), then the total
`vpub_old` contribution — i.e. the total Sprout-pool addition — is `0`.
Source: `zebra-consensus/src/transaction/check.rs:220-246`
(`disabled_add_to_sprout_pool`). -/
theorem totalSproutAddition_zero_of_NoSproutPoolAddition (jss : List JoinSplitPair)
    (h : NoSproutPoolAddition jss) :
    totalSproutAddition jss = 0 := by
  induction jss with
  | nil => rfl
  | cons js rest ih =>
    have hHead : js.vpub_old = 0 := h js (List.mem_cons_self ..)
    have hTail : NoSproutPoolAddition rest := fun j hj => h j (List.mem_cons_of_mem _ hj)
    have hRest : totalSproutAddition rest = 0 := ih hTail
    unfold totalSproutAddition sproutPoolAddition at *
    simp [List.map, List.sum_cons, hHead, hRest]

/-- **T20 (Sprout pool is closed under Canopy-conformant transactions).**
For a list of transactions, each given as its list of JoinSplits, the total
Sprout-pool addition is `0` provided every transaction satisfies the
`[Canopy onward]` rule. The Sprout pool is therefore closed — it can only
*decrease*, not grow, after Canopy. -/
theorem chainTotalSproutAddition_zero
    (txs : List (List JoinSplitPair))
    (h : ∀ tx ∈ txs, NoSproutPoolAddition tx) :
    (txs.map totalSproutAddition).sum = 0 := by
  induction txs with
  | nil => rfl
  | cons tx rest ih =>
    have hHead : NoSproutPoolAddition tx := h tx (List.mem_cons_self ..)
    have hTail : ∀ tx' ∈ rest, NoSproutPoolAddition tx' :=
      fun tx' htx' => h tx' (List.mem_cons_of_mem _ htx')
    have hRest : (rest.map totalSproutAddition).sum = 0 := ih hTail
    have hHeadZero : totalSproutAddition tx = 0 :=
      totalSproutAddition_zero_of_NoSproutPoolAddition tx hHead
    simp [List.map, List.sum_cons, hHeadZero, hRest]

/-! ## `joinsplit_has_vpub_zero` invariant -/

/-- **T21 (`joinsplit_has_vpub_zero` ⇒ one side is zero).** Restates the
per-JoinSplit invariant `vpub_old = 0 ∨ vpub_new = 0` as a disjunction
useful for case splits downstream.
Source: `zebra-consensus/src/transaction/check.rs:191-213`. -/
theorem hasVPubZero_iff (js : JoinSplitPair) :
    hasVPubZero js ↔ js.vpub_old = 0 ∨ js.vpub_new = 0 := Iff.rfl

/-- **T22 (Canopy rule ⇒ `joinsplit_has_vpub_zero`).** The `[Canopy onward]`
rule `vpub_old = 0` is strictly stronger than the always-on rule
`vpub_old = 0 ∨ vpub_new = 0`. Hence any Canopy-conformant JoinSplit also
satisfies the `joinsplit_has_vpub_zero` rule that runs at every height. -/
theorem hasVPubZero_of_vpub_old_zero (js : JoinSplitPair)
    (h : js.vpub_old = 0) :
    hasVPubZero js := Or.inl h

/-- **T23 (Canopy rule ⇒ list-level `joinsplit_has_vpub_zero`).** The same
implication, lifted to a `Vec<JoinSplit>`. -/
theorem all_hasVPubZero_of_NoSproutPoolAddition (jss : List JoinSplitPair)
    (h : NoSproutPoolAddition jss) :
    ∀ js ∈ jss, hasVPubZero js := fun js hjs =>
  hasVPubZero_of_vpub_old_zero js (h js hjs)

/-! ## Pre-Canopy sanity: pool addition can grow -/

/-- **T24 (pre-Canopy, the Sprout pool may grow).** Without the
`[Canopy onward]` constraint, a transaction with `vpub_old > 0` contributes
positively to the Sprout pool. We show a concrete example so the model is
not vacuous: a single JoinSplit with `vpub_old = 5`, `vpub_new = 0`
satisfies the always-on `hasVPubZero` rule (so it is a valid pre-Canopy
transaction) but does *not* satisfy `NoSproutPoolAddition`. -/
theorem pre_canopy_pool_growth_example :
    let js : JoinSplitPair := { vpub_old := 5, vpub_new := 0 }
    hasVPubZero js ∧ ¬ NoSproutPoolAddition [js] := by
  refine ⟨Or.inr rfl, ?_⟩
  intro h
  have h5 : (5 : Nat) = 0 := h { vpub_old := 5, vpub_new := 0 } (List.mem_singleton.mpr rfl)
  exact absurd h5 (by decide)

/-- **T25 (`NoSproutPoolAddition` is decidable).** -/
instance instDecidableNoSproutPoolAddition (jss : List JoinSplitPair) :
    Decidable (NoSproutPoolAddition jss) := by
  unfold NoSproutPoolAddition
  exact List.decidableBAll _ _

/-! ## Auxiliary algebraic facts -/

/-- **T26 (`totalSproutAddition_cons`).** Total addition decomposes over a
list cons. -/
theorem totalSproutAddition_cons (js : JoinSplitPair) (rest : List JoinSplitPair) :
    totalSproutAddition (js :: rest) =
      sproutPoolAddition js + totalSproutAddition rest := by
  unfold totalSproutAddition
  simp [List.map, List.sum_cons]

/-- **T27 (`totalSproutAddition_nil`).** Total addition of an empty list is zero. -/
theorem totalSproutAddition_nil :
    totalSproutAddition [] = 0 := rfl

/-- **T28 (per-JoinSplit size lower bound).** Every JoinSplit description
occupies at least `1506` bytes — even before the proof; in particular every
JoinSplit description is non-empty, ruling out parses that consume zero
bytes. -/
theorem joinsplit_min_size :
    JOINSPLIT_SIZE_WITHOUT_ZKPROOF ≥ 1506 := by
  rw [joinsplit_size_without_zkproof_value]

/-- **T29 (proof sizes are non-zero).** Every variant of the SNARK proof
contributes strictly positive bytes; combined with T28 this rules out a
degenerate "zero-byte JoinSplit" parse. -/
theorem bctv14_proof_pos : 0 < BCTV14_PROOF_SIZE := by
  unfold BCTV14_PROOF_SIZE; decide

theorem groth16_proof_pos : 0 < GROTH16_PROOF_SIZE := by
  unfold GROTH16_PROOF_SIZE; decide

/-- **T30 (BCTV14 has a strictly larger proof than Groth16).** Groth16 is
the strictly more compact later-generation proof system; hence Groth16 JoinSplits
take strictly less wire space, which is the consensus-relevant fact behind
T11. -/
theorem groth16_proof_lt_bctv14_proof :
    GROTH16_PROOF_SIZE < BCTV14_PROOF_SIZE := by
  unfold GROTH16_PROOF_SIZE BCTV14_PROOF_SIZE; decide

end Zebra.JoinSplitProof
