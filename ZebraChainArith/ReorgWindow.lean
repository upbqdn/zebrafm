import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Reorg-window policy from `zebra-chain/src/parameters/constants.rs`

The Zcash protocol does not define a reorg limit; Zebra applies a local policy:
once the best non-finalized chain grows past `MAX_BLOCK_REORG_HEIGHT = 1000`
blocks above a candidate, that candidate is finalized and cannot be rolled
back. Equivalently, a block at `block_height` is **finalized** at tip
`tip_height` iff `tip_height - block_height ≥ MAX_BLOCK_REORG_HEIGHT`, and is
otherwise still inside the rollback window.

We model heights as `Nat` (the Rust type is `u32`) and prove:
  * the iff characterisation of finality,
  * closure of finality under tip advancement (once finalized, always
    finalized),
  * the dual "in window" predicate and its monotonicity in `block_height`,
  * concrete boundary values at exactly `1000` blocks of depth.
-/

namespace Zebra.ReorgWindow

/-- The maximum chain reorganisation height: Zebra's local rollback window.
Source: `zebra-chain/src/parameters/constants.rs:30`
(`pub const MAX_BLOCK_REORG_HEIGHT: u32 = 1000;`) -/
def MAX_BLOCK_REORG_HEIGHT : Nat := 1000

/-- A block at `blockHeight` is **finalized** relative to a chain tip at
`tipHeight` iff the depth `tipHeight - blockHeight` reaches the reorg window.

Modelled with `Nat` subtraction, which truncates at zero — this matches the
Rust check `tip_height - block_height >= MAX_BLOCK_REORG_HEIGHT` since when
`block_height > tip_height` the depth is `0 < 1000` and the block is not
finalized.
Source: `zebra-chain/src/parameters/constants.rs:30` (policy described in
the constant's doc-comment) -/
def isFinalized (tipHeight blockHeight : Nat) : Bool :=
  decide (tipHeight - blockHeight ≥ MAX_BLOCK_REORG_HEIGHT)

/-- A block is **in the reorg window** iff it is not yet finalized. -/
def inReorgWindow (tipHeight blockHeight : Nat) : Bool :=
  ! isFinalized tipHeight blockHeight

/-! ## Theorems -/

/-- **T1.** Finality iff the depth reaches the reorg window. This is the
defining iff for the `isFinalized` predicate. -/
theorem isFinalized_iff (tipHeight blockHeight : Nat) :
    isFinalized tipHeight blockHeight = true
      ↔ tipHeight - blockHeight ≥ MAX_BLOCK_REORG_HEIGHT := by
  unfold isFinalized
  simp

/-- **T2.** "In the reorg window" iff the depth is strictly below
`MAX_BLOCK_REORG_HEIGHT`. -/
theorem inReorgWindow_iff (tipHeight blockHeight : Nat) :
    inReorgWindow tipHeight blockHeight = true
      ↔ tipHeight - blockHeight < MAX_BLOCK_REORG_HEIGHT := by
  unfold inReorgWindow isFinalized
  simp

/-- **T3.** Finalisation is closed under tip advancement: once a block is
finalized, it stays finalized as the tip grows. -/
theorem isFinalized_mono_tip
    (tipHeight tipHeight' blockHeight : Nat)
    (hAdvance : tipHeight ≤ tipHeight')
    (hFin : isFinalized tipHeight blockHeight = true) :
    isFinalized tipHeight' blockHeight = true := by
  rw [isFinalized_iff] at hFin ⊢
  omega

/-- **T4.** Finalisation is anti-monotone in `blockHeight`: a deeper block
(smaller height) at the same tip is at least as finalized. -/
theorem isFinalized_antimono_block
    (tipHeight blockHeight blockHeight' : Nat)
    (hDeeper : blockHeight' ≤ blockHeight)
    (hFin : isFinalized tipHeight blockHeight = true) :
    isFinalized tipHeight blockHeight' = true := by
  rw [isFinalized_iff] at hFin ⊢
  omega

/-- **T5.** Boundary value at exactly `MAX_BLOCK_REORG_HEIGHT` of depth:
a block whose depth equals `1000` is finalized. -/
theorem isFinalized_at_boundary (blockHeight : Nat) :
    isFinalized (blockHeight + MAX_BLOCK_REORG_HEIGHT) blockHeight = true := by
  rw [isFinalized_iff]
  omega

/-- **T6.** Strictly less than `MAX_BLOCK_REORG_HEIGHT` blocks of depth means
the block is still in the reorg window. -/
theorem inReorgWindow_below_threshold
    (tipHeight blockHeight : Nat)
    (hBelow : tipHeight - blockHeight < MAX_BLOCK_REORG_HEIGHT) :
    inReorgWindow tipHeight blockHeight = true := by
  rw [inReorgWindow_iff]; exact hBelow

/-- **T7.** Excluded middle: every block is either finalized or in the reorg
window — the two predicates partition the space. -/
theorem finalized_or_in_window (tipHeight blockHeight : Nat) :
    isFinalized tipHeight blockHeight = true
      ∨ inReorgWindow tipHeight blockHeight = true := by
  by_cases h : tipHeight - blockHeight ≥ MAX_BLOCK_REORG_HEIGHT
  · left; rw [isFinalized_iff]; exact h
  · right; rw [inReorgWindow_iff]; omega

/-- **T8.** Mutual exclusion: a block cannot be both finalized and in the
reorg window. -/
theorem not_both_finalized_and_in_window (tipHeight blockHeight : Nat) :
    ¬ (isFinalized tipHeight blockHeight = true
        ∧ inReorgWindow tipHeight blockHeight = true) := by
  rintro ⟨hFin, hWin⟩
  rw [isFinalized_iff] at hFin
  rw [inReorgWindow_iff] at hWin
  omega

/-- **T9.** A block at the tip (depth `0`) is always in the reorg window —
it can never be finalized while it is the tip. -/
theorem tip_in_window (tipHeight : Nat) :
    inReorgWindow tipHeight tipHeight = true := by
  rw [inReorgWindow_iff]
  simp [MAX_BLOCK_REORG_HEIGHT]

/-- **T10.** A block strictly above the tip (i.e. not yet on chain) is also
modelled as in the reorg window, since `Nat` subtraction truncates to `0`. -/
theorem above_tip_in_window
    (tipHeight blockHeight : Nat) (hAbove : tipHeight < blockHeight) :
    inReorgWindow tipHeight blockHeight = true := by
  rw [inReorgWindow_iff]
  have hzero : tipHeight - blockHeight = 0 := by omega
  rw [hzero]
  decide

/-- **T11.** Genesis (`blockHeight = 0`) finalises exactly when the tip
reaches `MAX_BLOCK_REORG_HEIGHT`. -/
theorem genesis_finalized_iff (tipHeight : Nat) :
    isFinalized tipHeight 0 = true ↔ tipHeight ≥ MAX_BLOCK_REORG_HEIGHT := by
  rw [isFinalized_iff]
  omega

end Zebra.ReorgWindow
