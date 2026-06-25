import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# PoW averaging window from `zebra-chain/src/parameters/network_upgrade.rs`

The Zcash difficulty adjustment uses an averaging window of `PoWAveragingWindow`
blocks (= 17) and a median-of-`PoWMedianBlockSpan` (= 11) timestamp filter.

Rust source:

* `POW_AVERAGING_WINDOW: usize = 17` —
  `zebra-chain/src/parameters/network_upgrade.rs:251`
* `PRE_BLOSSOM_POW_TARGET_SPACING: i64 = 150` —
  `zebra-chain/src/parameters/network_upgrade.rs:243`
* `POST_BLOSSOM_POW_TARGET_SPACING: u32 = 75` —
  `zebra-chain/src/parameters/network_upgrade.rs:246`
* `averaging_window_timespan(&self) -> Duration = target_spacing * POW_AVERAGING_WINDOW`
  — `zebra-chain/src/parameters/network_upgrade.rs:498`

`POW_MEDIAN_BLOCK_SPAN = 11` is the Zcash protocol constant `PoWMedianBlockSpan`
(see `zebra-chain/src/work/difficulty.rs:52` and the Zcash protocol spec
§ Difficulty Adjustment). It is not re-exported as a Rust constant in
`network_upgrade.rs`, but it pairs with `POW_AVERAGING_WINDOW` throughout the
difficulty arithmetic.
-/

namespace Zebra.PowAveragingWindow

/-! ## Constants -/

/-- The averaging window for difficulty threshold arithmetic mean calculations.
Source: `zebra-chain/src/parameters/network_upgrade.rs:251`
(`pub const POW_AVERAGING_WINDOW: usize = 17`). -/
def POW_AVERAGING_WINDOW : Nat := 17

/-- The median block span used for the timestamp median filter.
`PoWMedianBlockSpan` in the Zcash protocol specification (§ Difficulty
Adjustment). Not re-exported as a Rust constant in `network_upgrade.rs`,
but pinned to 11 by the protocol. -/
def POW_MEDIAN_BLOCK_SPAN : Nat := 11

/-- The pre-Blossom target block spacing, in seconds.
Source: `zebra-chain/src/parameters/network_upgrade.rs:243`
(`const PRE_BLOSSOM_POW_TARGET_SPACING: i64 = 150`). -/
def PRE_BLOSSOM_POW_TARGET_SPACING : Nat := 150

/-- The post-Blossom target block spacing, in seconds.
Source: `zebra-chain/src/parameters/network_upgrade.rs:246`
(`pub const POST_BLOSSOM_POW_TARGET_SPACING: u32 = 75`). -/
def POST_BLOSSOM_POW_TARGET_SPACING : Nat := 75

/-! ## Derived functions -/

/-- The ideal averaging-window timespan for a network upgrade with the given
`target_spacing` in seconds. Source:
`zebra-chain/src/parameters/network_upgrade.rs:498`
(`averaging_window_timespan(&self) -> Duration`):
`target_spacing * POW_AVERAGING_WINDOW`. -/
def averagingWindowTimespan (targetSpacing : Nat) : Nat :=
  targetSpacing * POW_AVERAGING_WINDOW

/-- Pre-Blossom averaging-window timespan, in seconds. -/
def preBlossomAveragingWindowTimespan : Nat :=
  averagingWindowTimespan PRE_BLOSSOM_POW_TARGET_SPACING

/-- Post-Blossom averaging-window timespan, in seconds. -/
def postBlossomAveragingWindowTimespan : Nat :=
  averagingWindowTimespan POST_BLOSSOM_POW_TARGET_SPACING

/-! ## Theorems -/

/-- **T1.** The averaging window is strictly greater than the median block span.
This is the invariant the difficulty-adjustment algorithm relies on: enough
blocks in the window to compute a meaningful median timestamp gap. -/
theorem averaging_window_gt_median_span :
    POW_MEDIAN_BLOCK_SPAN < POW_AVERAGING_WINDOW := by
  unfold POW_MEDIAN_BLOCK_SPAN POW_AVERAGING_WINDOW
  decide

/-- **T2.** The averaging window has exactly the value the Rust source pins. -/
theorem pow_averaging_window_value : POW_AVERAGING_WINDOW = 17 := rfl

/-- **T3.** The median block span has exactly the value the Zcash protocol pins. -/
theorem pow_median_block_span_value : POW_MEDIAN_BLOCK_SPAN = 11 := rfl

/-- **T4.** Ideal mining: the averaging window timespan equals
`target_spacing * 17`. This is the direct image of the Rust expression
`self.target_spacing() * POW_AVERAGING_WINDOW`. -/
theorem averaging_window_timespan_eq (targetSpacing : Nat) :
    averagingWindowTimespan targetSpacing = targetSpacing * 17 := by
  unfold averagingWindowTimespan POW_AVERAGING_WINDOW
  rfl

/-- **T5.** Pre-Blossom: the averaging window covers `150 * 17 = 2550` seconds
(= 42 minutes 30 seconds) of ideal mining. -/
theorem pre_blossom_averaging_window_timespan_value :
    preBlossomAveragingWindowTimespan = 2550 := by
  unfold preBlossomAveragingWindowTimespan averagingWindowTimespan
    PRE_BLOSSOM_POW_TARGET_SPACING POW_AVERAGING_WINDOW
  decide

/-- **T6.** Post-Blossom: the averaging window covers `75 * 17 = 1275` seconds
(= 21 minutes 15 seconds) of ideal mining. After Blossom halved the target
spacing, the averaging window halved with it. -/
theorem post_blossom_averaging_window_timespan_value :
    postBlossomAveragingWindowTimespan = 1275 := by
  unfold postBlossomAveragingWindowTimespan averagingWindowTimespan
    POST_BLOSSOM_POW_TARGET_SPACING POW_AVERAGING_WINDOW
  decide

/-- **T7.** Blossom halves the target spacing: pre-Blossom spacing is exactly
twice post-Blossom spacing. -/
theorem blossom_halves_target_spacing :
    PRE_BLOSSOM_POW_TARGET_SPACING = 2 * POST_BLOSSOM_POW_TARGET_SPACING := by
  unfold PRE_BLOSSOM_POW_TARGET_SPACING POST_BLOSSOM_POW_TARGET_SPACING
  decide

/-- **T8.** Blossom halves the averaging-window timespan in lockstep:
pre-Blossom window is exactly twice the post-Blossom window. -/
theorem blossom_halves_averaging_window :
    preBlossomAveragingWindowTimespan
      = 2 * postBlossomAveragingWindowTimespan := by
  unfold preBlossomAveragingWindowTimespan postBlossomAveragingWindowTimespan
    averagingWindowTimespan PRE_BLOSSOM_POW_TARGET_SPACING
    POST_BLOSSOM_POW_TARGET_SPACING POW_AVERAGING_WINDOW
  decide

/-- **T9.** Monotonicity: the averaging-window timespan is monotone in
`target_spacing`. A slower target spacing yields a longer window. -/
theorem averaging_window_timespan_monotone
    (s₁ s₂ : Nat) (h : s₁ ≤ s₂) :
    averagingWindowTimespan s₁ ≤ averagingWindowTimespan s₂ := by
  unfold averagingWindowTimespan
  exact Nat.mul_le_mul_right POW_AVERAGING_WINDOW h

/-- **T10.** The averaging-window timespan is zero exactly when the target
spacing is zero. (`POW_AVERAGING_WINDOW > 0`, so the multiplication can't
vanish from the right.) -/
theorem averaging_window_timespan_zero_iff (s : Nat) :
    averagingWindowTimespan s = 0 ↔ s = 0 := by
  unfold averagingWindowTimespan POW_AVERAGING_WINDOW
  constructor
  · intro h
    rcases Nat.mul_eq_zero.mp h with hs | h17
    · exact hs
    · omega
  · intro h; simp [h]

/-- **T11.** Both the averaging window and the median block span are positive.
This is what makes the difficulty-adjustment quotient well-defined. -/
theorem pow_constants_positive :
    0 < POW_AVERAGING_WINDOW ∧ 0 < POW_MEDIAN_BLOCK_SPAN := by
  unfold POW_AVERAGING_WINDOW POW_MEDIAN_BLOCK_SPAN
  decide

end Zebra.PowAveragingWindow
