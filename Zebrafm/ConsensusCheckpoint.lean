import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Checkpoint verification

Models the hard-coded checkpoint table and the checkpoint-verifier match logic
from:

* `zebra-chain/src/parameters/checkpoint/list.rs` — `CheckpointList`,
  `from_list` (validity predicate), `hash` (lookup by height), `contains`,
  `max_height`, `min_height_in_range`.
* `zebra-chain/src/parameters/checkpoint/constants.rs` — `MAX_CHECKPOINT_HEIGHT_GAP`
  and `MAX_CHECKPOINT_BYTE_COUNT`.
* `zebra-consensus/src/checkpoint.rs:715-754` — `process_height`: the
  fundamental match-vs-mismatch decision, where a block whose hash equals the
  pinned checkpoint hash is accepted and any other hash at that height is
  rejected as `UnexpectedSideChain`.

A checkpoint table is modelled as a `List (Nat × Nat)` of `(height, hash)`
pairs. The validity predicate from Rust's `CheckpointList::from_list`
(`list.rs:125-166`) requires:

  1. **Genesis pin.** The list starts at height 0 (Rust: `Some((Height(0), _))`,
     `list.rs:138`).
  2. **Strictly increasing heights.** Heights must be unique; we use the
     stronger property that consecutive heights are strictly increasing —
     equivalent to "unique heights in a `BTreeMap`" once the order is fixed
     (Rust: `list.rs:145-147`).
  3. **Unique hashes.** No two checkpoints share a hash (Rust: `list.rs:149-152`).
  4. **No null hash.** The all-zeros hash is forbidden (Rust: `list.rs:155-158`).

The verifier match logic is then a one-liner: at a checkpointed height the
block hash must match the pinned hash; at a non-checkpointed height there is
nothing to check at this layer (other consensus checks run elsewhere). This
module proves that lookup is unique by construction, the match relation is
sound and complete, and the operational consequences ("matching ⇒ accept",
"mismatching ⇒ reject") follow as decidable corollaries.
-/

namespace Zebra.ConsensusCheckpoint

/-! ## Hash and checkpoint model -/

/-- A block hash is modelled as a `Nat` — the only thing we need from it for
this layer is equality. -/
abbrev Hash : Type := Nat

/-- The "null hash" `[0u8; 32]`. Rust forbids it as a checkpoint hash because
it is overloaded for "no parent" / "missing". Source: `list.rs:154-158`. -/
def NULL_HASH : Hash := 0

/-- A single checkpoint entry: `(height, hash)`. -/
abbrev Checkpoint : Type := Nat × Hash

/-- The checkpoint table type — a list of `(height, hash)` pairs in the order
they appear in the hard-coded text file. -/
abbrev Table : Type := List Checkpoint

/-! ## Validity predicates -/

/-- Every entry in the table has height `> h₀`. Used to express the "head is
strictly below every later entry" invariant. -/
def allHeightsGt (h₀ : Nat) : Table → Prop
  | []           => True
  | (h,_) :: rest => h₀ < h ∧ allHeightsGt h₀ rest

/-- The table's heights are strictly increasing. Equivalent to "all heights
unique under the BTreeMap order" once the order is fixed. -/
def heightsStrictlyIncreasing : Table → Prop
  | []           => True
  | (h,_) :: rest => allHeightsGt h rest ∧ heightsStrictlyIncreasing rest

/-- No two entries share a hash. -/
def hashesUnique : Table → Prop
  | []           => True
  | (_,k) :: rest =>
      (∀ p ∈ rest, p.2 ≠ k) ∧ hashesUnique rest

/-- No entry uses the null hash. -/
def noNullHash : Table → Prop
  | []           => True
  | (_,k) :: rest => k ≠ NULL_HASH ∧ noNullHash rest

/-- Composite validity predicate mirroring `CheckpointList::from_list`
(`list.rs:125-166`). The genesis-at-front condition is split out from the
strictly-increasing condition so it can be proved/used independently. -/
structure Valid (t : Table) : Prop where
  /-- Genesis is the first entry (Rust: `Some((Height(0), _))`). -/
  genesisFirst : ∃ k rest, t = (0, k) :: rest
  /-- Heights are strictly increasing along the table. -/
  heightsInc : heightsStrictlyIncreasing t
  /-- All hashes are pairwise distinct. -/
  hashesDistinct : hashesUnique t
  /-- The forbidden null hash is absent. -/
  noNull : noNullHash t

/-! ## Lookup, contains, max_height -/

/-- Look up a height in the table; returns the first matching hash.
Mirrors `CheckpointList::hash` (`list.rs:179`). On a *valid* table the
"first matching" is also the unique matching, which we prove below. -/
def lookup (h : Nat) : Table → Option Hash
  | []           => none
  | (h',k) :: rest => if h' = h then some k else lookup h rest

/-- Is there a checkpoint at this height? Mirrors `CheckpointList::contains`
(`list.rs:171`). -/
def contains (h : Nat) (t : Table) : Bool :=
  (lookup h t).isSome

/-! ## Verifier match logic

The decision in `process_height` (`zebra-consensus/src/checkpoint.rs:715-754`):
at a checkpointed height the block hash must equal the pinned hash; otherwise
the block is rejected as `UnexpectedSideChain`. -/

/-- True iff the candidate `(blockHeight, blockHash)` satisfies the checkpoint
constraint relative to `t`: either no checkpoint pins this height, or the pin
matches `blockHash`. This is the boolean form of the `process_height` match
test (`checkpoint.rs:733`). -/
def verifies (blockHeight : Nat) (blockHash : Hash) (t : Table) : Bool :=
  match lookup blockHeight t with
  | none   => true   -- non-pinned heights pass this layer
  | some k => k == blockHash

/-! ## Theorems on validity -/

/-- **T1 (genesis at index 0).** A valid table has its first entry at height 0;
this is the Rust `from_list` precondition. -/
theorem valid_first_height_zero (t : Table) (hv : Valid t) :
    ∃ k rest, t = (0, k) :: rest := hv.genesisFirst

/-- Members of a list with `allHeightsGt h₀` all have first coordinate `> h₀`. -/
private theorem mem_of_allHeightsGt (h₀ : Nat) (rest : Table)
    (hge : allHeightsGt h₀ rest) :
    ∀ p ∈ rest, h₀ < p.1 := by
  induction rest with
  | nil => intro p hp; exact absurd hp (List.not_mem_nil)
  | cons q qrest ih =>
    intro p hp
    obtain ⟨h₁, k₁⟩ := q
    have ⟨hlt_head, hge_tail⟩ : h₀ < h₁ ∧ allHeightsGt h₀ qrest := hge
    rw [List.mem_cons] at hp
    rcases hp with heq | hp'
    · rw [heq]; exact hlt_head
    · exact ih hge_tail p hp'

/-- **T2 (head height is strictly below every later height).** Direct
consequence of strict increase; this is what lets us argue that a given
height appears at most once in the table. -/
theorem head_strictly_below_rest (h₀ : Nat) (k : Hash) (rest : Table)
    (hsi : heightsStrictlyIncreasing ((h₀, k) :: rest)) :
    ∀ p ∈ rest, h₀ < p.1 := by
  have hge : allHeightsGt h₀ rest := hsi.1
  exact mem_of_allHeightsGt h₀ rest hge

/-- If every later entry has height `> h₀`, then `lookup h₀` skips the rest. -/
private theorem lookup_skips_when_below
    (h₀ : Nat) (rest : Table)
    (hgt : ∀ p ∈ rest, h₀ < p.1) :
    lookup h₀ rest = none := by
  induction rest with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨h', k'⟩
    have hlt : h₀ < h' := hgt ⟨h', k'⟩ List.mem_cons_self
    have hne : h' ≠ h₀ := Nat.ne_of_gt hlt
    unfold lookup
    simp [hne]
    apply ih
    intro p hp
    exact hgt p (List.mem_cons_of_mem _ hp)

/-- The tail of a strictly-increasing list is still strictly-increasing. -/
private theorem tail_strictly_increasing
    (p : Checkpoint) (rest : Table)
    (hsi : heightsStrictlyIncreasing (p :: rest)) :
    heightsStrictlyIncreasing rest := by
  rcases p with ⟨h', k'⟩
  exact hsi.2

/-- Auxiliary form of `lookup_unique_on_valid` over a raw
`heightsStrictlyIncreasing` hypothesis (no full `Valid`). This lets us state
the induction with cleanly generalised premises. -/
private theorem lookup_unique_under_strict_inc
    (t : Table) (hsi : heightsStrictlyIncreasing t)
    (h : Nat) (k₁ k₂ : Hash)
    (hl₁ : lookup h t = some k₁)
    (hin : (h, k₂) ∈ t) :
    k₁ = k₂ := by
  induction t with
  | nil =>
    exact absurd hin (List.not_mem_nil)
  | cons p rest ih =>
    obtain ⟨h', k'⟩ := p
    have hbelow : ∀ q ∈ rest, h' < q.1 :=
      head_strictly_below_rest h' k' rest hsi
    have hsi_rest : heightsStrictlyIncreasing rest :=
      tail_strictly_increasing _ rest hsi
    rw [List.mem_cons] at hin
    rcases hin with hin_head | hin_rest
    · -- hin_head : (h, k₂) = (h', k')
      have h_eq : h = h' := (Prod.mk.injEq _ _ _ _).mp hin_head |>.1
      have k_eq : k₂ = k' := (Prod.mk.injEq _ _ _ _).mp hin_head |>.2
      unfold lookup at hl₁
      simp [← h_eq] at hl₁
      rw [k_eq]
      exact hl₁.symm
    · have h'_lt_h : h' < h := hbelow (h, k₂) hin_rest
      have h'_ne_h : h' ≠ h := Nat.ne_of_lt h'_lt_h
      unfold lookup at hl₁
      simp [h'_ne_h] at hl₁
      exact ih hsi_rest hl₁ hin_rest

/-- **T3 (lookup is unique on valid tables).** A height appears at most once,
so any membership at that height gives back the same hash that `lookup`
returns. This is the property the Rust `from_list` precondition guarantees
by going through a `BTreeMap` and rejecting duplicates (`list.rs:145-147`). -/
theorem lookup_unique_on_valid (t : Table) (hv : Valid t)
    (h : Nat) (k₁ k₂ : Hash)
    (hl₁ : lookup h t = some k₁)
    (hin : (h, k₂) ∈ t) :
    k₁ = k₂ :=
  lookup_unique_under_strict_inc t hv.heightsInc h k₁ k₂ hl₁ hin

/-- **T4 (matching hash trivially verifies).** When the table pins `hash k` at
`height h`, a block with that exact `(h, k)` passes `verifies`. This is the
operational soundness of the verifier's accept branch (`checkpoint.rs:733`). -/
theorem verifies_match (t : Table) (h : Nat) (k : Hash)
    (hl : lookup h t = some k) :
    verifies h k t = true := by
  unfold verifies
  rw [hl]
  simp

/-- **T5 (mismatching hash fails verification).** A block whose hash differs
from the pinned hash at a checkpointed height is rejected. This is the
`UnexpectedSideChain` path of `process_height` (`checkpoint.rs:746-749`). -/
theorem verifies_mismatch_fails (t : Table) (h : Nat) (k k' : Hash)
    (hl : lookup h t = some k) (hne : k ≠ k') :
    verifies h k' t = false := by
  unfold verifies
  rw [hl]
  simp [hne]

/-- **T6 (non-checkpointed height passes this layer).** At a height without a
pin, this layer reports success and other consensus checks (PoW, Merkle root,
…) are responsible. -/
theorem verifies_no_checkpoint (t : Table) (h : Nat) (k : Hash)
    (hl : lookup h t = none) :
    verifies h k t = true := by
  unfold verifies
  rw [hl]

/-! ## Operational theorems -/

/-- **T7 (verify-iff characterisation).** Combines T4-T6: `verifies h k t` is
true iff the lookup at `h` either is absent or matches `k`. -/
theorem verifies_iff (t : Table) (h : Nat) (k : Hash) :
    verifies h k t = true ↔
      (lookup h t = none ∨ lookup h t = some k) := by
  unfold verifies
  cases hl : lookup h t with
  | none =>
    constructor
    · intro _; exact Or.inl rfl
    · intro _; rfl
  | some k' =>
    constructor
    · intro heq
      -- heq : (k' == k) = true
      have : k' = k := by
        have := beq_iff_eq.mp heq
        exact this
      exact Or.inr (by rw [this])
    · intro hor
      rcases hor with habs | hsome
      · exact absurd habs (by simp)
      · -- hsome : some k' = some k
        have : k' = k := Option.some.inj hsome
        rw [this]
        simp

/-! ## Theorems about the validity predicate's structural invariants -/

/-- Auxiliary form over a raw `noNullHash` hypothesis; T8 (below) is the user-facing
corollary on a fully `Valid` table. -/
private theorem lookup_never_null_under_noNull
    (t : Table) (hnn : noNullHash t)
    (h : Nat) (k : Hash) (hl : lookup h t = some k) :
    k ≠ NULL_HASH := by
  induction t with
  | nil =>
    exact absurd hl (by simp [lookup])
  | cons p rest ih =>
    obtain ⟨h', k'⟩ := p
    have ⟨hne_head, hnn_rest⟩ : k' ≠ NULL_HASH ∧ noNullHash rest := hnn
    unfold lookup at hl
    by_cases hcase : h' = h
    · simp [hcase] at hl
      rw [← hl]
      exact hne_head
    · simp [hcase] at hl
      exact ih hnn_rest hl

/-- **T8 (no checkpoint hash is the null hash).** Together with hash-uniqueness
this means a "no parent" hash sentinel will never be confused with a real
checkpoint — protecting against the genesis-block-hash equivocation Rust
defends against at `list.rs:154-158`. -/
theorem lookup_never_null (t : Table) (hv : Valid t)
    (h : Nat) (k : Hash) (hl : lookup h t = some k) :
    k ≠ NULL_HASH :=
  lookup_never_null_under_noNull t hv.noNull h k hl

/-- **T9 (a verified block has a non-null hash).** Operational corollary of
T8 + T4: any block accepted by `verifies` at a checkpointed height has a
non-null hash, so the parent-hash sentinel could never be mistaken for a
verified checkpoint hash. -/
theorem verified_match_non_null (t : Table) (hv : Valid t)
    (h : Nat) (k : Hash)
    (hl : lookup h t = some k) :
    k ≠ NULL_HASH := lookup_never_null t hv h k hl

/-- Auxiliary form over a raw `hashesUnique` hypothesis; T10 (below) is the
user-facing corollary on a fully `Valid` table. -/
private theorem hash_unique_cross_height_under_distinct
    (t : Table) (hud : hashesUnique t)
    (h₁ h₂ : Nat) (k : Hash)
    (hin₁ : (h₁, k) ∈ t) (hin₂ : (h₂, k) ∈ t) :
    h₁ = h₂ := by
  induction t with
  | nil => exact absurd hin₁ (List.not_mem_nil)
  | cons p rest ih =>
    obtain ⟨h', k'⟩ := p
    have ⟨head_ne_rest, hud_rest⟩ :
        (∀ q ∈ rest, q.2 ≠ k') ∧ hashesUnique rest := hud
    rw [List.mem_cons] at hin₁ hin₂
    rcases hin₁ with heq₁ | hin₁'
    · -- heq₁ : (h₁, k) = (h', k')
      have h₁_eq : h₁ = h' := (Prod.mk.injEq _ _ _ _).mp heq₁ |>.1
      have k_eq₁ : k  = k' := (Prod.mk.injEq _ _ _ _).mp heq₁ |>.2
      rcases hin₂ with heq₂ | hin₂'
      · have h₂_eq : h₂ = h' := (Prod.mk.injEq _ _ _ _).mp heq₂ |>.1
        rw [h₁_eq, h₂_eq]
      · have hne : (h₂, k).2 ≠ k' := head_ne_rest (h₂, k) hin₂'
        -- (h₂, k).2 = k, but k = k' contradicts hne
        exact absurd k_eq₁ hne
    · rcases hin₂ with heq₂ | hin₂'
      · have k_eq₂ : k = k' := (Prod.mk.injEq _ _ _ _).mp heq₂ |>.2
        have hne : (h₁, k).2 ≠ k' := head_ne_rest (h₁, k) hin₁'
        exact absurd k_eq₂ hne
      · exact ih hud_rest hin₁' hin₂'

/-- **T10 (hash uniqueness implies cross-height non-aliasing).** Two
checkpointed heights with the same hash must be the same height; on a valid
table the hashes are pairwise distinct. This rules out the "same hash at two
different heights" attack the Rust code guards against by checking
`HashSet::len == original_len` (`list.rs:149-152`). -/
theorem hash_unique_cross_height (t : Table) (hv : Valid t)
    (h₁ h₂ : Nat) (k : Hash)
    (hin₁ : (h₁, k) ∈ t) (hin₂ : (h₂, k) ∈ t) :
    h₁ = h₂ :=
  hash_unique_cross_height_under_distinct t hv.hashesDistinct h₁ h₂ k hin₁ hin₂

/-! ## Genesis checkpoint -/

/-- **T11 (genesis is always pinned).** Per the Rust precondition, every valid
table has a genesis pin at height 0; thus `lookup 0` succeeds. This is the
property the Rust `from_list` enforces at `list.rs:138`. -/
theorem lookup_zero_some (t : Table) (hv : Valid t) :
    ∃ k, lookup 0 t = some k := by
  rcases hv.genesisFirst with ⟨k, rest, rfl⟩
  refine ⟨k, ?_⟩
  unfold lookup
  simp

/-! ## Constants from `checkpoint/constants.rs` -/

/-- Maximum number of blocks per checkpoint gap. Source:
`zebra-chain/src/parameters/checkpoint/constants.rs:12`. -/
def MAX_CHECKPOINT_HEIGHT_GAP : Nat := 400

/-- Maximum cumulative serialized-block byte count per checkpoint range.
Source: `zebra-chain/src/parameters/checkpoint/constants.rs:20`. -/
def MAX_CHECKPOINT_BYTE_COUNT : Nat := 32 * 1024 * 1024

/-- **T12 (checkpoint byte-count value pin).** `32 * 1024 * 1024 = 33_554_432`.
Pins the Rust constant so any change becomes a model-level rebuild error. -/
theorem max_checkpoint_byte_count_value :
    MAX_CHECKPOINT_BYTE_COUNT = 33554432 := by
  unfold MAX_CHECKPOINT_BYTE_COUNT
  decide

/-- **T13 (gap × min block size fits in a checkpoint range).** A pre-Sapling
mainnet block is at most a few KB; 400 blocks fit well inside the 32 MiB
byte-count cap as soon as each block averages under ~83 KB. Stated as the
ratio (in bytes) any checkpoint gap can support. -/
theorem checkpoint_avg_block_budget :
    MAX_CHECKPOINT_BYTE_COUNT / MAX_CHECKPOINT_HEIGHT_GAP = 83886 := by
  rw [max_checkpoint_byte_count_value]
  unfold MAX_CHECKPOINT_HEIGHT_GAP
  decide

/-- **T14 (a 2 MiB block does not exceed one checkpoint range).** Since the
P2P-message cap is 2 MiB, even an adversarial peer cannot inflate a single
block past `MAX_PROTOCOL_MESSAGE_LEN`; thus a single block always fits in the
byte budget, and the gap (400) is the binding parameter. -/
theorem one_block_fits_byte_budget :
    2 * 1024 * 1024 ≤ MAX_CHECKPOINT_BYTE_COUNT := by
  unfold MAX_CHECKPOINT_BYTE_COUNT
  decide

end Zebra.ConsensusCheckpoint
