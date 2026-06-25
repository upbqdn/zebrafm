import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.List.Sort

/-!
# DAA averaging and median window from `zebra-chain` / `zebra-state`

The Zcash difficulty adjustment algorithm (DAA) operates on a window of the
last `PoWAveragingWindow = 17` blocks. The bounding timestamp filter uses the
median of `PoWMedianBlockSpan = 11` blocks. Per ZIP-208, the *median timespan*
between the older and newer 11-block medians is damped by a factor of 4
(`PoWDampingFactor`) and then asymmetrically clamped: at most 16 % below and
at most 32 % above the `AveragingWindowTimespan`.

This module pins down those pieces in `Nat` arithmetic. `ExpandedDifficulty`
target thresholds are 256-bit unsigned values; here we model them as `Nat`
since Lean's `Nat` is unbounded — this is a faithful abstraction over the
U256 ring used in Rust for sums and averages of target thresholds (no
overflow can occur in the abstraction).

Rust source pointers:

* `POW_AVERAGING_WINDOW: usize = 17` —
  `zebra-chain/src/parameters/network_upgrade.rs:251`.
* `PRE_BLOSSOM_POW_TARGET_SPACING: i64 = 150` —
  `zebra-chain/src/parameters/network_upgrade.rs:243`.
* `POST_BLOSSOM_POW_TARGET_SPACING: u32 = 75` —
  `zebra-chain/src/parameters/network_upgrade.rs:246`.
* averaging-window timespan = `target_spacing * POW_AVERAGING_WINDOW` —
  `zebra-chain/src/parameters/network_upgrade.rs:498`.
* `POW_MEDIAN_BLOCK_SPAN = 11`, `POW_DAMPING_FACTOR = 4`,
  `POW_MAX_ADJUST_UP_PERCENT = 16`, `POW_MAX_ADJUST_DOWN_PERCENT = 32` —
  `zebra-state/src/service/check/difficulty.rs:22-43`.
* `median_time`, `mean_target_difficulty`, `median_timespan`,
  `median_timespan_bounded`, `threshold_bits` —
  `zebra-state/src/service/check/difficulty.rs:213-364`.

We model:

* `medianOf` of a length-`n` non-empty list (`1 ≤ n ≤ 11`) as
  `sorted[n / 2]`, matching Rust's `median_time` for any sub-length up to 11.
* `meanTarget` of a length-17 list of expanded target thresholds (`Nat`) as
  `sum / 17` — this is `MeanTarget` from the spec, mirroring Rust's
  `mean_target_difficulty`.
* `actualTimespan` as the difference `newerMedian − olderMedian` (clamped to
  zero in `Nat`, mirroring Rust's `chrono::Duration::num_seconds`-with-
  truncation behaviour).
* `dampedVariance` as `(actualTimespan − averagingWindowTimespan) /
  POW_DAMPING_FACTOR` (separated into positive and negative branches so we
  do not lose the sign information in `Nat`).
* the ZIP-208 bounded timespan via `medianTimespanBounded`, computed as
  `max minTimespan (min maxTimespan (averagingWindowTimespan +
  dampedVariance))`, with `minTimespan = avg * 84 / 100` (down to 16 %
  *below*) and `maxTimespan = avg * 132 / 100` (up to 32 % *above*).
* the PoWLimit cap as the final `min powLimit threshold` step in
  `threshold_bits`.

The legacy symmetric `clampActualTimespan` (50 % / 200 %) is preserved under
a more explicit name `clampActualTimespan_symHalfDouble` so any downstream
notes still type-check; theorems on it are renamed to reflect that they
prove the *symmetric* `[ideal/2, ideal*2]` containment property — *not* the
ZIP-208 bound, which is tighter and asymmetric.
-/

namespace Zebra.DAAMedianWindow

/-! ## Constants -/

/-- `PoWAveragingWindow` (= 17). Number of recent blocks averaged when
adjusting difficulty.
Source: `zebra-chain/src/parameters/network_upgrade.rs:251`. -/
def POW_AVERAGING_WINDOW : Nat := 17

/-- `PoWMedianBlockSpan` (= 11). Number of recent blocks the timestamp
median filter is computed over.
Source: `zebra-state/src/service/check/difficulty.rs:22`. -/
def POW_MEDIAN_BLOCK_SPAN : Nat := 11

/-- `POW_ADJUSTMENT_BLOCK_SPAN` (= 28). Total block span used for adjusting
Zcash block difficulty: `PoWAveragingWindow + PoWMedianBlockSpan`.
Source: `zebra-state/src/service/check/difficulty.rs:28`. -/
def POW_ADJUSTMENT_BLOCK_SPAN : Nat := POW_AVERAGING_WINDOW + POW_MEDIAN_BLOCK_SPAN

/-- The pre-Blossom target block spacing, in seconds.
Source: `zebra-chain/src/parameters/network_upgrade.rs:243`. -/
def PRE_BLOSSOM_POW_TARGET_SPACING : Nat := 150

/-- The post-Blossom target block spacing, in seconds.
Source: `zebra-chain/src/parameters/network_upgrade.rs:246`. -/
def POST_BLOSSOM_POW_TARGET_SPACING : Nat := 75

/-- `PoWDampingFactor` (= 4). Damping factor applied to the median
timespan variance.
Source: `zebra-state/src/service/check/difficulty.rs:33`. -/
def POW_DAMPING_FACTOR : Nat := 4

/-- `PoWMaxAdjustUp * 100` (= 16). Maximum *upward* difficulty adjustment as
a percentage — i.e. the median timespan may be at most 16 % shorter than
the averaging-window timespan.
Source: `zebra-state/src/service/check/difficulty.rs:38`. -/
def POW_MAX_ADJUST_UP_PERCENT : Nat := 16

/-- `PoWMaxAdjustDown * 100` (= 32). Maximum *downward* difficulty
adjustment as a percentage — i.e. the median timespan may be at most 32 %
longer than the averaging-window timespan.
Source: `zebra-state/src/service/check/difficulty.rs:43`. -/
def POW_MAX_ADJUST_DOWN_PERCENT : Nat := 32

/-- The averaging-window timespan in seconds for a given target spacing.
`AveragingWindowTimespan = TargetSpacing * PoWAveragingWindow`.
Source: `zebra-chain/src/parameters/network_upgrade.rs:498-500`. -/
def averagingWindowTimespan (targetSpacing : Nat) : Nat :=
  targetSpacing * POW_AVERAGING_WINDOW

/-! ## Median of a 1..=11 element list

Rust's `AdjustedDifficulty::median_time` accepts any non-empty
`Vec<DateTime<Utc>>` of length up to `PoWMedianBlockSpan = 11`. It sorts the
vector and returns `sorted[len/2]`. We mirror that exact shape. -/

/-- `medianOf ts` is the median of a list of `Nat` timestamps. For a
non-empty list the result is `sorted[ts.length / 2]`. For an empty list we
fall back to `0`; Rust would panic, but we keep this total to keep the
model well-defined.

This matches Rust's `AdjustedDifficulty::median_time`
(`zebra-state/src/service/check/difficulty.rs:357-364`): sort, then return
the element at index `len / 2`. The Zcash spec definition is
`median(S) := sorted(S)[ceiling((|S| + 1) / 2)]`, which for 1-indexed
positions and an odd length `n = 2k + 1` is index `k + 1`, i.e. 0-indexed
`k = n / 2` — agreeing with `len / 2` for the canonical case `len = 11`. -/
def medianOf (ts : List Nat) : Nat :=
  ((List.insertionSort (· ≤ ·) ts)[ts.length / 2]?).getD 0

/-- `medianOf11 ts` is the median of an 11-element list. Specialised
back-compat alias for the `PoWMedianBlockSpan` window. Returns `0` if the
length is not exactly 11 to stay total. -/
def medianOf11 (ts : List Nat) : Nat :=
  if ts.length = POW_MEDIAN_BLOCK_SPAN then medianOf ts else 0

/-! ## Averaging window of 17 target thresholds and (timestamp) means -/

/-- `meanTarget ts` is the arithmetic mean of a 17-element list of
*expanded difficulty target thresholds* (modelled as `Nat`). This is
`MeanTarget` from the Zcash specification and mirrors Rust's
`AdjustedDifficulty::mean_target_difficulty`
(`zebra-state/src/service/check/difficulty.rs:230-259`): sum the 17 expanded
thresholds and divide by `PoWAveragingWindow = 17`. The Rust sum is taken
in `U256`; here `Nat` is unbounded so no overflow can occur.

For other lengths we fall back to `0` to stay total. -/
def meanTarget (ts : List Nat) : Nat :=
  if ts.length = POW_AVERAGING_WINDOW then
    ts.sum / POW_AVERAGING_WINDOW
  else 0

/-- `meanTimestamp ts` is the arithmetic mean of a 17-element list of
`Nat` *timestamps*. This is **not** `MeanTarget`. It is a helper for
timestamp-domain reasoning and concrete sanity tests; it does *not*
correspond to any Rust DAA function. The DAA averages target thresholds
(`meanTarget`), not timestamps. We retain it under an explicit name so the
previous timestamp test vectors still compile, but it must not be confused
with the consensus-critical mean over targets. -/
def meanTimestamp (ts : List Nat) : Nat :=
  if ts.length = POW_AVERAGING_WINDOW then
    ts.sum / POW_AVERAGING_WINDOW
  else 0

/-! ## ZIP-208 actual timespan, damping, and bounded timespan

Rust's `median_timespan_bounded` (`difficulty.rs:276-301`) computes:

```text
damped_variance       := (median_timespan − averagingWindowTimespan)
                          / POW_DAMPING_FACTOR
median_timespan_damped := averagingWindowTimespan + damped_variance
min_median_timespan   := avg * (100 − POW_MAX_ADJUST_UP_PERCENT) / 100   -- = avg * 84/100
max_median_timespan   := avg * (100 + POW_MAX_ADJUST_DOWN_PERCENT) / 100 -- = avg * 132/100
ActualTimespanBounded := max(min_median_timespan,
                             min(max_median_timespan, median_timespan_damped))
```

We model the same in `Nat`. The damped variance has a sign in Rust
(`chrono::Duration` is signed); we split the model into two functions
`dampedVariancePos` and `dampedVarianceNeg` so we never lose the sign. -/

/-- `actualTimespan newerMedian olderMedian` is the difference of the two
medians (newer minus older). In `Nat` we use saturating subtraction:
because the underlying Rust value is a signed `Duration`, negative actual
timespans are possible, but for our purposes we only need the positive
case. See `dampedVarianceNeg` for the symmetric negative branch.

Rust: `AdjustedDifficulty::median_timespan` —
`zebra-state/src/service/check/difficulty.rs:310-330`. -/
def actualTimespan (newerMedian olderMedian : Nat) : Nat :=
  newerMedian - olderMedian

/-- Positive branch of the damped variance: when the actual timespan is
*above* the averaging-window timespan (blocks were slow), the upward
variance is divided by `PoWDampingFactor`. -/
def dampedVariancePos (actual avg : Nat) : Nat :=
  (actual - avg) / POW_DAMPING_FACTOR

/-- Negative branch of the damped variance: when the actual timespan is
*below* the averaging-window timespan (blocks were fast), the downward
variance is divided by `PoWDampingFactor`. -/
def dampedVarianceNeg (actual avg : Nat) : Nat :=
  (avg - actual) / POW_DAMPING_FACTOR

/-- `medianTimespanDamped actual avg` is the averaging-window timespan
plus the damped variance: `avg + (actual − avg) / 4` when `actual ≥ avg`,
or `avg − (avg − actual) / 4` when `actual < avg` (saturated to `0` if
the subtraction would underflow in `Nat`).

This matches `median_timespan_damped` in Rust. -/
def medianTimespanDamped (actual avg : Nat) : Nat :=
  if avg ≤ actual then avg + dampedVariancePos actual avg
  else avg - dampedVarianceNeg actual avg

/-- The lower bound on the median timespan: `avg * 84 / 100`. Mirrors
`min_median_timespan` in Rust. -/
def minMedianTimespan (avg : Nat) : Nat :=
  avg * (100 - POW_MAX_ADJUST_UP_PERCENT) / 100

/-- The upper bound on the median timespan: `avg * 132 / 100`. Mirrors
`max_median_timespan` in Rust. -/
def maxMedianTimespan (avg : Nat) : Nat :=
  avg * (100 + POW_MAX_ADJUST_DOWN_PERCENT) / 100

/-- `medianTimespanBounded actual avg` is `ActualTimespanBounded` from
the Zcash spec, i.e. Rust's `median_timespan_bounded`
(`difficulty.rs:276-301`):
`max minTimespan (min maxTimespan medianTimespanDamped)`. -/
def medianTimespanBounded (actual avg : Nat) : Nat :=
  max (minMedianTimespan avg)
      (min (maxMedianTimespan avg) (medianTimespanDamped actual avg))

/-- `thresholdBitsRaw mean bounded avg powLimit` mirrors the multiplicative
combination in `AdjustedDifficulty::threshold_bits`
(`difficulty.rs:213-224`):

```text
threshold := (MeanTarget / averagingWindowTimespan) * boundedTimespan
threshold := min(PoWLimit, threshold)
```

In `Nat`, dividing first then multiplying preserves Rust's left-to-right
evaluation order on `U256`. The final `min` is the `PoWLimit` cap. -/
def thresholdBitsRaw (mean bounded avg powLimit : Nat) : Nat :=
  min powLimit ((mean / avg) * bounded)

/-! ## Legacy symmetric `[ideal/2, ideal*2]` clamp

The earlier version of this module proved a symmetric `[ideal/2, ideal*2]`
containment, which is *not* the ZIP-208 bound: the spec bound is the
tighter, asymmetric `[avg * 84/100, avg * 132/100]`. We keep the symmetric
clamp under an explicit name so its theorems read honestly: they describe
a *looser* envelope around the spec bound, useful as a sanity check but not
as the ZIP-208 statement. The ZIP-208 statement is `medianTimespanBounded`
above. -/

/-- Symmetric `[ideal/2, ideal*2]` clamp. *Not* the ZIP-208 bound — the
ZIP-208 bound is the tighter, asymmetric `medianTimespanBounded`. -/
def clampActualTimespan_symHalfDouble (actual ideal : Nat) : Nat :=
  max (ideal / 2) (min actual (ideal * 2))

/-! ## Theorems on `medianOf` / `medianOf11` -/

/-- For an 11-element list, `medianOf` equals the 6th sorted element
(0-indexed index 5), matching the canonical `PoWMedianBlockSpan` case. -/
theorem medianOf_eq_sixth_sorted_at_11 (ts : List Nat)
    (hlen : ts.length = POW_MEDIAN_BLOCK_SPAN) :
    medianOf ts = ((List.insertionSort (· ≤ ·) ts)[5]?).getD 0 := by
  have hlen' : ts.length / 2 = 5 := by
    unfold POW_MEDIAN_BLOCK_SPAN at hlen
    omega
  unfold medianOf
  rw [hlen']

/-- For an 11-element list, `medianOf11 = medianOf`. -/
theorem medianOf11_eq_medianOf (ts : List Nat)
    (hlen : ts.length = POW_MEDIAN_BLOCK_SPAN) :
    medianOf11 ts = medianOf ts := by
  unfold medianOf11
  simp [hlen]

/-- For an 11-element list, `medianOf11` returns the 6th sorted element. -/
theorem medianOf11_eq_sixth_sorted (ts : List Nat)
    (hlen : ts.length = POW_MEDIAN_BLOCK_SPAN) :
    medianOf11 ts = ((List.insertionSort (· ≤ ·) ts)[5]?).getD 0 := by
  rw [medianOf11_eq_medianOf ts hlen]
  exact medianOf_eq_sixth_sorted_at_11 ts hlen

/-- The 6th element is well-defined: for a length-11 list, the sorted list
has length 11, so `[5]?` returns `some`. -/
theorem medianOf11_get_some (ts : List Nat)
    (hlen : ts.length = POW_MEDIAN_BLOCK_SPAN) :
    ((List.insertionSort (· ≤ ·) ts)[5]?).isSome := by
  have hsort_len : (List.insertionSort (· ≤ ·) ts).length = ts.length :=
    List.length_insertionSort _ ts
  have h5 : 5 < (List.insertionSort (· ≤ ·) ts).length := by
    rw [hsort_len, hlen]
    unfold POW_MEDIAN_BLOCK_SPAN
    decide
  exact Option.isSome_iff_exists.mpr
    ⟨(List.insertionSort (· ≤ ·) ts)[5], List.getElem?_eq_getElem h5⟩

/-- **(Coverage: Finding 7).** `medianOf` for a list always returns
`sorted[len/2]?`, even for the boundary cases length 0 (empty fallback)
and lengths 1..=10 (sub-`PoWMedianBlockSpan` boot-up window). Rust's
`median_time` accepts any non-empty `Vec`; the only adjustment in our
model is the `0` fallback for the empty case, which Rust would panic on. -/
theorem medianOf_def (ts : List Nat) :
    medianOf ts =
      ((List.insertionSort (· ≤ ·) ts)[ts.length / 2]?).getD 0 := rfl

/-- For a non-empty list `medianOf` does *not* return the sentinel `0`
unless the median element itself is `0`. Specifically the sorted list's
`[len/2]?` lookup is `some`. -/
theorem medianOf_get_some_of_nonempty (ts : List Nat) (hne : ts ≠ []) :
    ((List.insertionSort (· ≤ ·) ts)[ts.length / 2]?).isSome := by
  have hpos : 0 < ts.length := List.length_pos_of_ne_nil hne
  have hsort_len : (List.insertionSort (· ≤ ·) ts).length = ts.length :=
    List.length_insertionSort _ ts
  have hidx : ts.length / 2 < ts.length := Nat.div_lt_self hpos (by decide)
  have hidx' : ts.length / 2 < (List.insertionSort (· ≤ ·) ts).length := by
    rw [hsort_len]; exact hidx
  exact Option.isSome_iff_exists.mpr
    ⟨(List.insertionSort (· ≤ ·) ts)[ts.length / 2],
     List.getElem?_eq_getElem hidx'⟩

/-! ## Theorems on `meanTarget` (`MeanTarget`) -/

/-- **`MeanTarget` matches the spec.** For a 17-block window of target
thresholds, `meanTarget` equals the sum divided by `PoWAveragingWindow = 17`,
matching `AdjustedDifficulty::mean_target_difficulty`. -/
theorem meanTarget_eq_sum_div_17 (ts : List Nat)
    (hlen : ts.length = POW_AVERAGING_WINDOW) :
    meanTarget ts = ts.sum / 17 := by
  unfold meanTarget POW_AVERAGING_WINDOW at *
  simp [hlen]

/-- **`MeanTarget` of a constant window.** Averaging 17 copies of the same
target threshold yields that threshold. -/
theorem meanTarget_constant (target : Nat) :
    meanTarget (List.replicate 17 target) = target := by
  unfold meanTarget POW_AVERAGING_WINDOW
  have hlen : (List.replicate 17 target).length = 17 := List.length_replicate
  rw [if_pos hlen]
  -- `(List.replicate 17 target).sum = 17 * target`, then divide by 17
  have hsum : (List.replicate 17 target).sum = 17 * target := by
    simp [List.sum, List.replicate]
    ring
  rw [hsum]
  exact Nat.mul_div_cancel_left target (by decide : (0 : Nat) < 17)

/-! ## Theorems on `meanTimestamp` (timestamp helper, *not* `MeanTarget`)

These are explicitly labelled as timestamp-domain helpers. They do not
mirror any consensus quantity. -/

/-- The timestamp mean equals `sum / 17` over a 17-element window. -/
theorem meanTimestamp_eq_sum_div_17 (ts : List Nat)
    (hlen : ts.length = POW_AVERAGING_WINDOW) :
    meanTimestamp ts = ts.sum / 17 := by
  unfold meanTimestamp POW_AVERAGING_WINDOW at *
  simp [hlen]

/-- Sanity: 17 copies of 150 average to 150. -/
theorem meanTimestamp_constant_pre_blossom :
    meanTimestamp (List.replicate 17 150) = 150 := by
  unfold meanTimestamp POW_AVERAGING_WINDOW
  have hlen : (List.replicate 17 150).length = 17 := List.length_replicate
  rw [if_pos hlen]
  decide

/-- Sanity: 17 copies of 75 average to 75. -/
theorem meanTimestamp_constant_post_blossom :
    meanTimestamp (List.replicate 17 75) = 75 := by
  unfold meanTimestamp POW_AVERAGING_WINDOW
  have hlen : (List.replicate 17 75).length = 17 := List.length_replicate
  rw [if_pos hlen]
  decide

/-! ## Theorems on `averagingWindowTimespan` -/

/-- The pre-Blossom averaging-window timespan is `150 * 17 = 2550 s`. -/
theorem averagingWindowTimespan_pre_blossom :
    averagingWindowTimespan PRE_BLOSSOM_POW_TARGET_SPACING = 2550 := by
  unfold averagingWindowTimespan POW_AVERAGING_WINDOW PRE_BLOSSOM_POW_TARGET_SPACING
  decide

/-- The post-Blossom averaging-window timespan is `75 * 17 = 1275 s`. -/
theorem averagingWindowTimespan_post_blossom :
    averagingWindowTimespan POST_BLOSSOM_POW_TARGET_SPACING = 1275 := by
  unfold averagingWindowTimespan POW_AVERAGING_WINDOW POST_BLOSSOM_POW_TARGET_SPACING
  decide

/-! ## Theorems on the ZIP-208 bounded median timespan -/

/-- **ZIP-208 lower bound.** The bounded median timespan is never below
`avg * 84 / 100`. -/
theorem medianTimespanBounded_lower (actual avg : Nat) :
    minMedianTimespan avg ≤ medianTimespanBounded actual avg := by
  unfold medianTimespanBounded
  exact Nat.le_max_left _ _

/-- **ZIP-208 upper bound.** The bounded median timespan is never above
`avg * 132 / 100`, **provided** the lower bound does not exceed the upper
bound — which holds whenever `avg ≥ 0` since `84 / 100 ≤ 132 / 100`. -/
theorem medianTimespanBounded_upper (actual avg : Nat) :
    medianTimespanBounded actual avg ≤ maxMedianTimespan avg := by
  unfold medianTimespanBounded
  apply max_le
  · -- minMedianTimespan avg ≤ maxMedianTimespan avg
    unfold minMedianTimespan maxMedianTimespan POW_MAX_ADJUST_UP_PERCENT
      POW_MAX_ADJUST_DOWN_PERCENT
    -- avg * 84 / 100 ≤ avg * 132 / 100
    apply Nat.div_le_div_right
    exact Nat.mul_le_mul_left avg (by decide)
  · exact min_le_left _ _

/-- The bounded timespan always lies in `[avg * 84/100, avg * 132/100]`. -/
theorem medianTimespanBounded_in_band (actual avg : Nat) :
    minMedianTimespan avg ≤ medianTimespanBounded actual avg ∧
      medianTimespanBounded actual avg ≤ maxMedianTimespan avg :=
  ⟨medianTimespanBounded_lower actual avg,
   medianTimespanBounded_upper actual avg⟩

/-- **Order check on the spec constants.** `100 − POW_MAX_ADJUST_UP_PERCENT
< 100 + POW_MAX_ADJUST_DOWN_PERCENT`, so `minMedianTimespan avg ≤
maxMedianTimespan avg`. -/
theorem min_le_max_median_timespan (avg : Nat) :
    minMedianTimespan avg ≤ maxMedianTimespan avg := by
  unfold minMedianTimespan maxMedianTimespan POW_MAX_ADJUST_UP_PERCENT
    POW_MAX_ADJUST_DOWN_PERCENT
  apply Nat.div_le_div_right
  exact Nat.mul_le_mul_left avg (by decide)

/-- The asymmetric ZIP-208 bound is strictly tighter than the symmetric
`[avg/2, avg*2]` envelope on the upper side (for non-trivial `avg`), and on
the lower side as well. We prove the upper side: `maxMedianTimespan avg ≤
avg * 2`. -/
theorem maxMedianTimespan_le_double (avg : Nat) :
    maxMedianTimespan avg ≤ avg * 2 := by
  unfold maxMedianTimespan POW_MAX_ADJUST_DOWN_PERCENT
  -- avg * 132 / 100 ≤ avg * 2
  -- avg * 132 ≤ 100 * (avg * 2) = avg * 200, so dividing by 100 gives
  -- avg * 132 / 100 ≤ avg * 2.
  apply Nat.div_le_of_le_mul
  -- Goal: avg * (100 + 32) ≤ 100 * (avg * 2)
  have : avg * (100 + 32) = avg * 132 := by ring
  rw [this]
  -- avg * 132 ≤ 100 * (avg * 2) = avg * 200
  have h : (100 : Nat) * (avg * 2) = avg * 200 := by ring
  rw [h]
  exact Nat.mul_le_mul_left avg (by decide)

/-- Likewise on the lower side: `avg / 2 ≤ minMedianTimespan avg`, so the
ZIP-208 lower bound is *higher* than the symmetric half-bound. -/
theorem half_le_minMedianTimespan (avg : Nat) :
    avg / 2 ≤ minMedianTimespan avg := by
  unfold minMedianTimespan POW_MAX_ADJUST_UP_PERCENT
  -- avg / 2 ≤ avg * 84 / 100
  -- avg * 50 ≤ avg * 84, so avg * 50 / 100 ≤ avg * 84 / 100, and
  -- avg / 2 = avg * 50 / 100.
  have h84 : avg * 50 ≤ avg * 84 :=
    Nat.mul_le_mul_left avg (by decide)
  have heq : avg / 2 = avg * 50 / 100 := by
    rcases Nat.even_or_odd avg with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · -- avg = 2k case
      have : (2 * k) * 50 = 100 * k := by ring
      omega
    · -- avg = 2k + 1
      -- avg / 2 = k, avg * 50 / 100 = (100*k + 50) / 100 = k
      have h₁ : (2 * k + 1) / 2 = k := by omega
      have h₂ : (2 * k + 1) * 50 / 100 = k := by
        have : (2 * k + 1) * 50 = 100 * k + 50 := by ring
        omega
      omega
  rw [heq]
  exact Nat.div_le_div_right h84

/-! ## Theorems on the damped variance -/

/-- When `actual = avg`, the damped variance is `0` and the damped timespan
equals the averaging-window timespan: no adjustment occurs. -/
theorem medianTimespanDamped_at_avg (avg : Nat) :
    medianTimespanDamped avg avg = avg := by
  unfold medianTimespanDamped
  simp [dampedVariancePos]

/-- When `actual ≥ avg`, the damped timespan is at least `avg`. -/
theorem medianTimespanDamped_lower_bound (actual avg : Nat)
    (hle : avg ≤ actual) :
    avg ≤ medianTimespanDamped actual avg := by
  unfold medianTimespanDamped
  simp [hle]

/-- When `actual ≤ avg`, the damped timespan is at most `avg`. -/
theorem medianTimespanDamped_upper_bound (actual avg : Nat)
    (hle : actual ≤ avg) :
    medianTimespanDamped actual avg ≤ avg := by
  unfold medianTimespanDamped
  by_cases h : avg ≤ actual
  · -- both `avg ≤ actual` and `actual ≤ avg` give `actual = avg`
    have : actual = avg := Nat.le_antisymm hle h
    subst this
    simp [dampedVariancePos]
  · simp [h]

/-- The damped variance dampens by a factor of `POW_DAMPING_FACTOR = 4`:
the upward-damped variance is at most `(actual − avg) / 4`. -/
theorem dampedVariancePos_eq (actual avg : Nat) :
    dampedVariancePos actual avg = (actual - avg) / POW_DAMPING_FACTOR := rfl

/-- The downward-damped variance is at most `(avg − actual) / 4`. -/
theorem dampedVarianceNeg_eq (actual avg : Nat) :
    dampedVarianceNeg actual avg = (avg - actual) / POW_DAMPING_FACTOR := rfl

/-- `POW_DAMPING_FACTOR = 4` literally. -/
theorem POW_DAMPING_FACTOR_eq : POW_DAMPING_FACTOR = 4 := rfl

/-- `POW_MAX_ADJUST_UP_PERCENT = 16` literally. -/
theorem POW_MAX_ADJUST_UP_PERCENT_eq : POW_MAX_ADJUST_UP_PERCENT = 16 := rfl

/-- `POW_MAX_ADJUST_DOWN_PERCENT = 32` literally. -/
theorem POW_MAX_ADJUST_DOWN_PERCENT_eq : POW_MAX_ADJUST_DOWN_PERCENT = 32 := rfl

/-! ## Theorems on the `thresholdBitsRaw` PoWLimit cap -/

/-- **The PoWLimit cap is enforced.** `thresholdBitsRaw` never exceeds the
`powLimit`, mirroring Rust's `threshold = min(network.target_difficulty_limit(),
threshold)` step (`difficulty.rs:221`). -/
theorem thresholdBitsRaw_le_powLimit (mean bounded avg powLimit : Nat) :
    thresholdBitsRaw mean bounded avg powLimit ≤ powLimit := by
  unfold thresholdBitsRaw
  exact min_le_left _ _

/-- When the raw `(mean / avg) * bounded` already fits under the PoWLimit,
the cap is a no-op. -/
theorem thresholdBitsRaw_under_cap (mean bounded avg powLimit : Nat)
    (h : (mean / avg) * bounded ≤ powLimit) :
    thresholdBitsRaw mean bounded avg powLimit = (mean / avg) * bounded := by
  unfold thresholdBitsRaw
  exact min_eq_right h

/-- When the raw value exceeds the PoWLimit, the cap clamps it down. -/
theorem thresholdBitsRaw_over_cap (mean bounded avg powLimit : Nat)
    (h : powLimit < (mean / avg) * bounded) :
    thresholdBitsRaw mean bounded avg powLimit = powLimit := by
  unfold thresholdBitsRaw
  exact min_eq_left (le_of_lt h)

/-! ## Theorems on the legacy symmetric clamp

These are *not* statements about the ZIP-208 bound: that is
`medianTimespanBounded` above. They state the obvious lattice properties of
the symmetric `[ideal/2, ideal*2]` envelope, which is strictly *looser*
than the spec bound. -/

/-- The symmetric clamp puts its output at least at `ideal / 2`. -/
theorem clampSym_lower_bound (actual ideal : Nat) :
    ideal / 2 ≤ clampActualTimespan_symHalfDouble actual ideal := by
  unfold clampActualTimespan_symHalfDouble
  exact Nat.le_max_left _ _

/-- The symmetric clamp puts its output at most at `ideal * 2`. -/
theorem clampSym_upper_bound (actual ideal : Nat) :
    clampActualTimespan_symHalfDouble actual ideal ≤ ideal * 2 := by
  unfold clampActualTimespan_symHalfDouble
  apply max_le
  · have h2 : ideal / 2 ≤ ideal := Nat.div_le_self _ _
    have h3 : ideal ≤ ideal * 2 := Nat.le_mul_of_pos_right _ (by decide)
    exact le_trans h2 h3
  · exact min_le_right _ _

/-- The symmetric clamp is the identity on values already in
`[ideal/2, ideal*2]`. -/
theorem clampSym_in_band_identity (actual ideal : Nat)
    (hlo : ideal / 2 ≤ actual) (hhi : actual ≤ ideal * 2) :
    clampActualTimespan_symHalfDouble actual ideal = actual := by
  unfold clampActualTimespan_symHalfDouble
  have hmin : min actual (ideal * 2) = actual := min_eq_left hhi
  rw [hmin]
  exact max_eq_right hlo

/-- The symmetric clamp saturates from above. -/
theorem clampSym_saturates_high (actual ideal : Nat)
    (hhi : ideal * 2 < actual) :
    clampActualTimespan_symHalfDouble actual ideal = ideal * 2 := by
  unfold clampActualTimespan_symHalfDouble
  have hmin : min actual (ideal * 2) = ideal * 2 :=
    min_eq_right (le_of_lt hhi)
  rw [hmin]
  apply max_eq_right
  have h2 : ideal / 2 ≤ ideal := Nat.div_le_self _ _
  have h3 : ideal ≤ ideal * 2 := Nat.le_mul_of_pos_right _ (by decide)
  exact le_trans h2 h3

/-- The symmetric clamp saturates from below. -/
theorem clampSym_saturates_low (actual ideal : Nat)
    (hlo : actual < ideal / 2) :
    clampActualTimespan_symHalfDouble actual ideal = ideal / 2 := by
  unfold clampActualTimespan_symHalfDouble
  have hmin : min actual (ideal * 2) = actual := by
    apply min_eq_left
    have h2 : ideal / 2 ≤ ideal := Nat.div_le_self _ _
    have h3 : ideal ≤ ideal * 2 := Nat.le_mul_of_pos_right _ (by decide)
    omega
  rw [hmin]
  exact max_eq_left (le_of_lt hlo)

/-- The symmetric clamp is monotone in `actual`. -/
theorem clampSym_monotone (a₁ a₂ ideal : Nat) (hle : a₁ ≤ a₂) :
    clampActualTimespan_symHalfDouble a₁ ideal
      ≤ clampActualTimespan_symHalfDouble a₂ ideal := by
  unfold clampActualTimespan_symHalfDouble
  apply max_le_max (le_refl _)
  exact min_le_min hle (le_refl _)

/-- The symmetric clamp at `ideal` is `ideal` — sanity check that the
identity case holds for the spec-default value. -/
theorem clampSym_at_ideal (ideal : Nat) :
    clampActualTimespan_symHalfDouble ideal ideal = ideal := by
  apply clampSym_in_band_identity
  · exact Nat.div_le_self _ _
  · exact Nat.le_mul_of_pos_right _ (by decide)

/-! ## Concrete vectors -/

/-- `medianOf11` of a sorted vector returns the middle element. -/
theorem medianOf11_sorted_example :
    medianOf11 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] = 6 := by
  unfold medianOf11 POW_MEDIAN_BLOCK_SPAN
  decide

/-- `medianOf11` is order-independent. -/
theorem medianOf11_unsorted_example :
    medianOf11 [11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1] = 6 := by
  unfold medianOf11 POW_MEDIAN_BLOCK_SPAN
  decide

/-- **(Coverage: Finding 7)** `medianOf` of a singleton returns that element. -/
theorem medianOf_singleton (x : Nat) :
    medianOf [x] = x := by
  unfold medianOf
  simp

/-- **(Coverage: Finding 7)** `medianOf` of a 5-element list (sub-`PoWMedianBlockSpan`
context) returns the 3rd sorted element. -/
theorem medianOf_five :
    medianOf [5, 3, 1, 4, 2] = 3 := by
  unfold medianOf
  decide

/-- **(Coverage: Finding 7)** `medianOf` of a 3-element list returns the
median of those three values. -/
theorem medianOf_three_unsorted :
    medianOf [10, 1, 5] = 5 := by
  unfold medianOf
  decide

/-- **(Coverage: Finding 6)** `MeanTarget` over a constant 17-block window
of target threshold `T` returns `T`. -/
theorem meanTarget_constant_example :
    meanTarget (List.replicate 17 1_000_000) = 1_000_000 := by
  exact meanTarget_constant 1_000_000

/-- **(Coverage: Finding 8)** The averaging-window timespan is positive
when the target spacing is positive. -/
theorem averagingWindowTimespan_pos (s : Nat) (hs : 0 < s) :
    0 < averagingWindowTimespan s := by
  unfold averagingWindowTimespan POW_AVERAGING_WINDOW
  exact Nat.mul_pos hs (by decide)

/-! ## Sanity constants -/

/-- The averaging window, median span, and damping factor are all positive,
and the median span is shorter than the averaging window. -/
theorem constants_positive :
    0 < POW_AVERAGING_WINDOW ∧ 0 < POW_MEDIAN_BLOCK_SPAN ∧
      POW_MEDIAN_BLOCK_SPAN < POW_AVERAGING_WINDOW ∧
      0 < POW_DAMPING_FACTOR := by
  unfold POW_AVERAGING_WINDOW POW_MEDIAN_BLOCK_SPAN POW_DAMPING_FACTOR
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The total adjustment block span is exactly the sum of the averaging
window and median span: `28 = 17 + 11`. -/
theorem adjustment_block_span_decomp :
    POW_ADJUSTMENT_BLOCK_SPAN = POW_AVERAGING_WINDOW + POW_MEDIAN_BLOCK_SPAN := rfl

/-- The spec percentages reflect the asymmetric adjustment bounds
declared in ZIP-208: up to 16 % below and up to 32 % above. -/
theorem percent_constants_asymmetric :
    POW_MAX_ADJUST_UP_PERCENT < POW_MAX_ADJUST_DOWN_PERCENT := by
  unfold POW_MAX_ADJUST_UP_PERCENT POW_MAX_ADJUST_DOWN_PERCENT
  decide

end Zebra.DAAMedianWindow
