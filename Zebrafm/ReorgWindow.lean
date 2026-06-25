import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Reorg-window policy from `zebra-chain/src/parameters/constants.rs`

The Zcash protocol does not define a reorg limit; Zebra applies a local policy:
the non-finalized portion of the best chain is kept at most
`MAX_BLOCK_REORG_HEIGHT = 1000` blocks long. After every successful
block-commit, the write task drains the front of the non-finalized chain:

```rust
while non_finalized_state
    .best_chain_len()
    .expect("just successfully inserted a non-finalized block above")
    > MAX_BLOCK_REORG_HEIGHT
{
    tracing::trace!("finalizing block past the reorg limit");
    let contextually_verified_with_trees = non_finalized_state.finalize();
    …
}
```
(`zebra-state/src/service/write.rs:451-463`, with the constant declared at
`zebra-chain/src/parameters/constants.rs:30`.)

`best_chain_len()` returns the number of blocks currently in the
non-finalized chain (`zebra-state/src/service/non_finalized_state.rs:677`).
The check is therefore on **chain length**, not on the depth of an arbitrary
block; it only ever runs against the chain's root.

This module exposes two layers:
  * **Length layer** (`chainLenFinalizationRequired`, `trimToWindow`) —
    a faithful mirror of the Rust `while` loop, operating on chain length.
  * **Depth layer** (`rootDepth`, `isRootFinalized`) — the corresponding
    statement on the root block's depth from the tip. We prove the two
    layers agree exactly when the chain spans `[root .. tip]`.

We model lengths and heights as `Nat` (the Rust types are `u32` and
`i64 = HeightDiff`). The `Nat`-truncation of subtraction is benign here:
the loop body only fires when length strictly exceeds `1000`, so the
`Nat`-subtraction depth `tip - root` is well-defined under the chain
invariant `root ≤ tip`.
-/

namespace Zebra.ReorgWindow

/-- The maximum chain reorganisation height: Zebra's local rollback window.
Source: `zebra-chain/src/parameters/constants.rs:30`
(`pub const MAX_BLOCK_REORG_HEIGHT: u32 = 1000;`). -/
def MAX_BLOCK_REORG_HEIGHT : Nat := 1000

/-! ## Length layer — faithful mirror of the Rust loop -/

/-- The Rust predicate `best_chain_len() > MAX_BLOCK_REORG_HEIGHT` that
guards the finalization `while` loop in
`zebra-state/src/service/write.rs:451-454`. While this holds, the root of
the non-finalized chain is popped and persisted to the finalized state. -/
def chainLenFinalizationRequired (chainLen : Nat) : Bool :=
  decide (chainLen > MAX_BLOCK_REORG_HEIGHT)

/-- One iteration of the Rust `while` loop: when finalisation is required,
shrink the non-finalized chain by one (the root is moved to the finalized
state). When not required, the chain is left untouched. -/
def stepFinalize (chainLen : Nat) : Nat :=
  if chainLenFinalizationRequired chainLen then chainLen - 1 else chainLen

/-- Drain the non-finalized chain down to the reorg window. Mirrors the
post-condition of the Rust `while` loop after `n` iterations; calling with
`n = chainLen` always suffices because each iteration strictly decreases
the length while the guard holds. -/
def trimToWindow : Nat → Nat → Nat
  | 0, chainLen => chainLen
  | n + 1, chainLen =>
      if chainLenFinalizationRequired chainLen then
        trimToWindow n (chainLen - 1)
      else
        chainLen

/-! ## Depth layer — re-expressing the rule on the root block

For a non-finalized chain spanning heights `[rootHeight .. tipHeight]`,
the chain length is `tipHeight - rootHeight + 1`. The Rust check
`chain_len > 1000` then reads `tipHeight - rootHeight ≥ 1000`. We expose
this as a per-block predicate evaluated **at the root**; applying it to
non-root blocks is meaningful only as a hypothetical ("if this block were
the root, would the chain be over-long?"). -/

/-- Depth of a block at `blockHeight` below the chain tip at `tipHeight`.
Modelled as `Nat`-subtraction, which truncates at `0` — meaningful only
when `blockHeight ≤ tipHeight`, the chain-invariant condition. -/
def depth (tipHeight blockHeight : Nat) : Nat := tipHeight - blockHeight

/-- The chain length implied by a `[rootHeight .. tipHeight]` span. -/
def spanLen (tipHeight rootHeight : Nat) : Nat := tipHeight - rootHeight + 1

/-- "Root depth has reached the reorg window." Under the invariant
`rootHeight ≤ tipHeight`, this is equivalent to the Rust length check
`chainLen > MAX_BLOCK_REORG_HEIGHT` — see `length_check_iff_root_depth`. -/
def isRootFinalized (tipHeight rootHeight : Nat) : Bool :=
  decide (depth tipHeight rootHeight ≥ MAX_BLOCK_REORG_HEIGHT)

/-- "The root is still inside the reorg window." The dual of
`isRootFinalized`, with the same chain-invariant caveat. -/
def isRootInWindow (tipHeight rootHeight : Nat) : Bool :=
  ! isRootFinalized tipHeight rootHeight

/-! ## Theorems

The theorems below are split between the length layer (T1–T6, which
prove the loop's termination and invariant) and the depth layer (T7–T16,
which prove the equivalence with the length check at the root and a few
boundary values). -/

/-! ### Length layer -/

/-- **T1.** Length check unfolds to `chainLen > 1000`. This is the
defining iff for the Rust loop guard. -/
theorem chainLenFinalizationRequired_iff (chainLen : Nat) :
    chainLenFinalizationRequired chainLen = true
      ↔ chainLen > MAX_BLOCK_REORG_HEIGHT := by
  unfold chainLenFinalizationRequired
  simp

/-- **T2.** When the loop guard fires, `stepFinalize` strictly decreases
chain length. This is the termination measure for the Rust `while` loop. -/
theorem stepFinalize_strict_decrease (chainLen : Nat)
    (hFire : chainLenFinalizationRequired chainLen = true) :
    stepFinalize chainLen < chainLen := by
  unfold stepFinalize
  have hGt : chainLen > MAX_BLOCK_REORG_HEIGHT :=
    (chainLenFinalizationRequired_iff chainLen).mp hFire
  simp [hFire]
  omega

/-- **T3.** When the loop guard does not fire, `stepFinalize` is the
identity. -/
theorem stepFinalize_noop (chainLen : Nat)
    (hNoFire : chainLenFinalizationRequired chainLen = false) :
    stepFinalize chainLen = chainLen := by
  unfold stepFinalize
  simp [hNoFire]

/-- **T4.** `trimToWindow` is stable once the loop guard no longer fires:
no matter how much extra fuel is provided, the result equals the input. -/
theorem trimToWindow_fuel_stable (n : Nat) (chainLen : Nat)
    (hStable : chainLenFinalizationRequired chainLen = false) :
    trimToWindow n chainLen = chainLen := by
  cases n with
  | zero => rfl
  | succ k =>
      unfold trimToWindow
      simp [hStable]

/-- **T5.** Post-loop invariant: with enough fuel, `trimToWindow` returns
a length that is no longer over-long. Concretely, fueling the loop with
the input length always suffices. -/
theorem trimToWindow_postcondition (chainLen : Nat) :
    chainLenFinalizationRequired (trimToWindow chainLen chainLen) = false := by
  induction chainLen with
  | zero => decide
  | succ k ih =>
      unfold trimToWindow
      by_cases h : chainLenFinalizationRequired (k + 1) = true
      · -- Loop fires once: chain shrinks to `k`, recurse with `k` fuel.
        simp [h]
        exact ih
      · -- Loop does not fire: result is `k + 1`, and the guard is false.
        have hf : chainLenFinalizationRequired (k + 1) = false := by
          cases hk : chainLenFinalizationRequired (k + 1) with
          | false => rfl
          | true => exact absurd hk h
        simp [hf]

/-- **T6.** Bound after trimming: the final length is at most
`MAX_BLOCK_REORG_HEIGHT`. This is the user-visible invariant Zebra
maintains on the non-finalized chain. -/
theorem trimToWindow_le_max (chainLen : Nat) :
    trimToWindow chainLen chainLen ≤ MAX_BLOCK_REORG_HEIGHT := by
  have h := trimToWindow_postcondition chainLen
  unfold chainLenFinalizationRequired at h
  simp only [decide_eq_false_iff_not, not_lt] at h
  exact h

/-! ### Depth layer — equivalence with the length check at the root -/

/-- **T7.** Under the chain-span invariant `rootHeight ≤ tipHeight`, the
chain length and the root depth differ by exactly 1: `spanLen = depth + 1`.
This is the bridge between the length layer and the depth layer. -/
theorem spanLen_eq_depth_succ
    (tipHeight rootHeight : Nat) (_hSpan : rootHeight ≤ tipHeight) :
    spanLen tipHeight rootHeight = depth tipHeight rootHeight + 1 := by
  unfold spanLen depth
  omega

/-- **T8.** Equivalence of the two layers at the root, under the chain-span
invariant. The Rust check on chain length matches the depth check on the
root block. -/
theorem length_check_iff_root_depth
    (tipHeight rootHeight : Nat) (_hSpan : rootHeight ≤ tipHeight) :
    chainLenFinalizationRequired (spanLen tipHeight rootHeight) = true
      ↔ isRootFinalized tipHeight rootHeight = true := by
  rw [chainLenFinalizationRequired_iff]
  unfold isRootFinalized depth spanLen
  simp
  omega

/-- **T9.** Defining iff for `isRootFinalized`. -/
theorem isRootFinalized_iff (tipHeight rootHeight : Nat) :
    isRootFinalized tipHeight rootHeight = true
      ↔ tipHeight - rootHeight ≥ MAX_BLOCK_REORG_HEIGHT := by
  unfold isRootFinalized depth
  simp

/-- **T10.** Defining iff for `isRootInWindow`. -/
theorem isRootInWindow_iff (tipHeight rootHeight : Nat) :
    isRootInWindow tipHeight rootHeight = true
      ↔ tipHeight - rootHeight < MAX_BLOCK_REORG_HEIGHT := by
  unfold isRootInWindow isRootFinalized depth
  simp

/-- **T11.** Root finalization is monotone in the tip: once the root is
past the reorg window, subsequent tip growth keeps it past. This mirrors
the fact that Rust only ever shrinks the non-finalized chain from the
front. -/
theorem isRootFinalized_mono_tip
    (tipHeight tipHeight' rootHeight : Nat)
    (hAdvance : tipHeight ≤ tipHeight')
    (hFin : isRootFinalized tipHeight rootHeight = true) :
    isRootFinalized tipHeight' rootHeight = true := by
  rw [isRootFinalized_iff] at hFin ⊢
  omega

/-- **T12.** Mutual exclusion at the root: the root cannot simultaneously
be finalized and inside the reorg window. -/
theorem not_root_finalized_and_in_window
    (tipHeight rootHeight : Nat) :
    ¬ (isRootFinalized tipHeight rootHeight = true
        ∧ isRootInWindow tipHeight rootHeight = true) := by
  rintro ⟨hFin, hWin⟩
  rw [isRootFinalized_iff] at hFin
  rw [isRootInWindow_iff] at hWin
  omega

/-- **T13.** Boundary value: a root whose depth equals exactly
`MAX_BLOCK_REORG_HEIGHT` is finalized. Equivalently, the corresponding
chain length is `MAX_BLOCK_REORG_HEIGHT + 1`, which exceeds the window. -/
theorem isRootFinalized_at_boundary (rootHeight : Nat) :
    isRootFinalized (rootHeight + MAX_BLOCK_REORG_HEIGHT) rootHeight = true := by
  rw [isRootFinalized_iff]
  omega

/-- **T14.** Just below the boundary: depth `MAX_BLOCK_REORG_HEIGHT - 1`
keeps the root in the reorg window (corresponds to a chain of length
exactly `MAX_BLOCK_REORG_HEIGHT`, the largest allowed value). -/
theorem isRootInWindow_just_below_boundary (rootHeight : Nat) :
    isRootInWindow (rootHeight + (MAX_BLOCK_REORG_HEIGHT - 1)) rootHeight
      = true := by
  rw [isRootInWindow_iff]
  simp [MAX_BLOCK_REORG_HEIGHT]

/-- **T15.** A single-block non-finalized chain (root = tip) is always
inside the reorg window: chain length 1 never triggers finalization. -/
theorem single_block_chain_in_window (height : Nat) :
    isRootInWindow height height = true := by
  rw [isRootInWindow_iff]
  simp [MAX_BLOCK_REORG_HEIGHT]

/-- **T16.** Genesis (`rootHeight = 0`) finalises exactly when the tip
reaches `MAX_BLOCK_REORG_HEIGHT` — equivalently, when the non-finalized
chain accumulates `MAX_BLOCK_REORG_HEIGHT + 1 = 1001` blocks. -/
theorem genesis_root_finalized_iff (tipHeight : Nat) :
    isRootFinalized tipHeight 0 = true ↔ tipHeight ≥ MAX_BLOCK_REORG_HEIGHT := by
  rw [isRootFinalized_iff]
  omega

/-! ## Legacy aliases

The earlier version of this module exposed a per-block "is finalized"
predicate without making the root-vs-non-root distinction explicit.
The definitions below preserve the old names so consumers (`Check.lean`)
keep building, but they are merely aliases for the root-layer
definitions: applying them to non-root blocks is meaningful only as a
hypothetical "if this block were the root" check. -/

/-- Legacy alias for `isRootFinalized`. The Rust check fires only when
the **root** of the non-finalized chain is at this depth from the tip;
for non-root blocks the predicate represents a hypothetical. -/
@[inline] def isFinalized (tipHeight blockHeight : Nat) : Bool :=
  isRootFinalized tipHeight blockHeight

/-- Legacy alias for `isRootInWindow`. Same root-block caveat as
`isFinalized`. -/
@[inline] def inReorgWindow (tipHeight blockHeight : Nat) : Bool :=
  isRootInWindow tipHeight blockHeight

/-- Legacy alias: defining iff for `isFinalized` (= `isRootFinalized`). -/
theorem isFinalized_iff (tipHeight blockHeight : Nat) :
    isFinalized tipHeight blockHeight = true
      ↔ tipHeight - blockHeight ≥ MAX_BLOCK_REORG_HEIGHT :=
  isRootFinalized_iff tipHeight blockHeight

/-- Legacy alias: defining iff for `inReorgWindow` (= `isRootInWindow`). -/
theorem inReorgWindow_iff (tipHeight blockHeight : Nat) :
    inReorgWindow tipHeight blockHeight = true
      ↔ tipHeight - blockHeight < MAX_BLOCK_REORG_HEIGHT :=
  isRootInWindow_iff tipHeight blockHeight

/-- Legacy alias: monotonicity in the tip. -/
theorem isFinalized_mono_tip
    (tipHeight tipHeight' blockHeight : Nat)
    (hAdvance : tipHeight ≤ tipHeight')
    (hFin : isFinalized tipHeight blockHeight = true) :
    isFinalized tipHeight' blockHeight = true :=
  isRootFinalized_mono_tip tipHeight tipHeight' blockHeight hAdvance hFin

/-- Legacy theorem: anti-monotonicity in block height. A deeper
hypothetical-root (smaller height) at the same tip is at least as
finalized. Note that in real chains the actual root is fixed; this
captures the order on the hypothetical predicate. -/
theorem isFinalized_antimono_block
    (tipHeight blockHeight blockHeight' : Nat)
    (hDeeper : blockHeight' ≤ blockHeight)
    (hFin : isFinalized tipHeight blockHeight = true) :
    isFinalized tipHeight blockHeight' = true := by
  rw [show isFinalized = isRootFinalized from rfl] at hFin ⊢
  rw [isRootFinalized_iff] at hFin ⊢
  omega

/-- Legacy alias for the boundary value at exactly `MAX_BLOCK_REORG_HEIGHT`
of depth. -/
theorem isFinalized_at_boundary (blockHeight : Nat) :
    isFinalized (blockHeight + MAX_BLOCK_REORG_HEIGHT) blockHeight = true :=
  isRootFinalized_at_boundary blockHeight

/-- Legacy theorem: strictly less than `MAX_BLOCK_REORG_HEIGHT` blocks of
hypothetical-root depth means the block is still in the reorg window. -/
theorem inReorgWindow_below_threshold
    (tipHeight blockHeight : Nat)
    (hBelow : tipHeight - blockHeight < MAX_BLOCK_REORG_HEIGHT) :
    inReorgWindow tipHeight blockHeight = true := by
  rw [show inReorgWindow = isRootInWindow from rfl]
  rw [isRootInWindow_iff]
  exact hBelow

/-- Legacy excluded-middle theorem for the hypothetical predicate. -/
theorem finalized_or_in_window (tipHeight blockHeight : Nat) :
    isFinalized tipHeight blockHeight = true
      ∨ inReorgWindow tipHeight blockHeight = true := by
  by_cases h : tipHeight - blockHeight ≥ MAX_BLOCK_REORG_HEIGHT
  · left; rw [show isFinalized = isRootFinalized from rfl, isRootFinalized_iff]; exact h
  · right; rw [show inReorgWindow = isRootInWindow from rfl, isRootInWindow_iff]; omega

/-- Legacy mutual-exclusion theorem for the hypothetical predicate. -/
theorem not_both_finalized_and_in_window (tipHeight blockHeight : Nat) :
    ¬ (isFinalized tipHeight blockHeight = true
        ∧ inReorgWindow tipHeight blockHeight = true) := by
  rw [show isFinalized = isRootFinalized from rfl,
      show inReorgWindow = isRootInWindow from rfl]
  exact not_root_finalized_and_in_window tipHeight blockHeight

/-- Legacy theorem: a hypothetical root at the tip (depth `0`) is always
in the reorg window. -/
theorem tip_in_window (tipHeight : Nat) :
    inReorgWindow tipHeight tipHeight = true :=
  single_block_chain_in_window tipHeight

/-- Legacy theorem: a block strictly above the tip (not yet on chain) is
modelled as in the reorg window — `Nat`-subtraction truncates to `0`. -/
theorem above_tip_in_window
    (tipHeight blockHeight : Nat) (hAbove : tipHeight < blockHeight) :
    inReorgWindow tipHeight blockHeight = true := by
  rw [show inReorgWindow = isRootInWindow from rfl, isRootInWindow_iff]
  have hzero : tipHeight - blockHeight = 0 := by omega
  rw [hzero]
  decide

/-- Legacy alias for `genesis_root_finalized_iff`. -/
theorem genesis_finalized_iff (tipHeight : Nat) :
    isFinalized tipHeight 0 = true ↔ tipHeight ≥ MAX_BLOCK_REORG_HEIGHT :=
  genesis_root_finalized_iff tipHeight

end Zebra.ReorgWindow
