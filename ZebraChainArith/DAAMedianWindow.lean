import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.List.Sort

/-!
# DAA averaging and median window from `zebra-chain/src/work/difficulty.rs`

The Zcash difficulty adjustment algorithm (DAA) operates on a window of the
last `PoWAveragingWindow = 17` blocks. The bounding timestamp filter uses the
median of `PoWMedianBlockSpan = 11` blocks. The adjustment factor is then
clamped between `0.5` and `2.0` per ZIP-208, so the new target is never less
than half nor more than twice the previous one.

Rust source pointers:

* `POW_AVERAGING_WINDOW: usize = 17` —
  `zebra-chain/src/parameters/network_upgrade.rs:251`
* `PRE_BLOSSOM_POW_TARGET_SPACING: i64 = 150` —
  `zebra-chain/src/parameters/network_upgrade.rs:243`
* `POST_BLOSSOM_POW_TARGET_SPACING: u32 = 75` —
  `zebra-chain/src/parameters/network_upgrade.rs:246`
* averaging-window timespan = `target_spacing * POW_AVERAGING_WINDOW` —
  `zebra-chain/src/parameters/network_upgrade.rs:498`
* `PoWMedianBlockSpan = 11` — Zcash protocol spec § Difficulty Adjustment;
  pairs with `POW_AVERAGING_WINDOW` throughout difficulty arithmetic
  (`zebra-chain/src/work/difficulty.rs:52`).

We model:

* the median window as a `List Nat` of length 11 (timestamps);
* the averaging window as a `List Nat` of length 17;
* `median` of an 11-list as `sorted[5]` (the 6th element when 1-indexed,
  the middle of an odd-length sorted list);
* `mean` over the averaging window as `(sum) / 17` (`Nat` division);
* the ZIP-208 clamp as the bound that the adjusted timespan never falls
  outside `[ideal/2, ideal*2]`. Since we are using `Nat`, "factor of 0.5"
  is "half the value" and "factor of 2.0" is "double the value".

The proofs do not require floating-point types: clamping `x` to
`[ideal/2, ideal*2]` is just `max (ideal/2) (min x (ideal*2))`.
-/

namespace Zebra.DAAMedianWindow

/-! ## Constants -/

/-- `PoWAveragingWindow` (= 17). Number of recent blocks averaged when
adjusting difficulty.
Source: `zebra-chain/src/parameters/network_upgrade.rs:251`. -/
def POW_AVERAGING_WINDOW : Nat := 17

/-- `PoWMedianBlockSpan` (= 11). Number of recent blocks the timestamp
median filter is computed over. Spec constant; not re-exported by Zebra,
but referenced throughout `zebra-chain/src/work/difficulty.rs`. -/
def POW_MEDIAN_BLOCK_SPAN : Nat := 11

/-- The pre-Blossom target block spacing, in seconds.
Source: `zebra-chain/src/parameters/network_upgrade.rs:243`. -/
def PRE_BLOSSOM_POW_TARGET_SPACING : Nat := 150

/-- The post-Blossom target block spacing, in seconds.
Source: `zebra-chain/src/parameters/network_upgrade.rs:246`. -/
def POST_BLOSSOM_POW_TARGET_SPACING : Nat := 75

/-! ## Median of an 11-element list -/

/-- `medianOf11 ts` is the median of an 11-element list of timestamps.
We compute it as the 6th element (1-indexed; i.e. `sorted[5]` 0-indexed)
of the sorted list. If the input is not exactly length 11 we fall back to
`0` so the function stays total. -/
def medianOf11 (ts : List Nat) : Nat :=
  if ts.length = POW_MEDIAN_BLOCK_SPAN then
    ((List.insertionSort (· ≤ ·) ts)[5]?).getD 0
  else 0

/-! ## Averaging window of 17 timestamps -/

/-- `mean17 ts` is the arithmetic mean of a 17-element list of timestamps,
computed by `Nat` floor-division. If the input is not exactly length 17 we
fall back to `0`. Matches the DAA's "sum of block times / `POW_AVERAGING_WINDOW`"
form. -/
def mean17 (ts : List Nat) : Nat :=
  if ts.length = POW_AVERAGING_WINDOW then
    ts.sum / POW_AVERAGING_WINDOW
  else 0

/-! ## ZIP-208 clamp of the adjustment factor -/

/-- `clampActualTimespan actual ideal` enforces the ZIP-208 bound that the
"actual" timespan over the averaging window is clamped between half and
double the "ideal" timespan. With `Nat` arithmetic the clamp is
`max (ideal/2) (min actual (ideal*2))`. This corresponds to the difficulty
*adjustment factor* being bounded between `0.5` and `2.0`. -/
def clampActualTimespan (actual ideal : Nat) : Nat :=
  max (ideal / 2) (min actual (ideal * 2))

/-! ## Theorems -/

/-- **T1 (median is the 6th sorted element).** For an 11-element list, the
sorted list also has length 11, and `medianOf11` returns its 6th element
(0-indexed index 5). -/
theorem medianOf11_eq_sixth_sorted (ts : List Nat)
    (hlen : ts.length = POW_MEDIAN_BLOCK_SPAN) :
    medianOf11 ts =
      ((List.insertionSort (· ≤ ·) ts)[5]?).getD 0 := by
  unfold medianOf11
  simp [hlen]

/-- **T1b (the 6th element is well-defined).** For an 11-element list, the
sorted list has length 11, so `[5]?` returns `some`. -/
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

/-- **T2 (mean is total / 17).** For a 17-element window, the mean equals
the sum of all timestamps divided (floor) by `POW_AVERAGING_WINDOW = 17`. -/
theorem mean17_eq_sum_div_17 (ts : List Nat)
    (hlen : ts.length = POW_AVERAGING_WINDOW) :
    mean17 ts = ts.sum / 17 := by
  unfold mean17 POW_AVERAGING_WINDOW at *
  simp [hlen]

/-- **T3 (clamp lower bound: ≥ ideal/2).** The clamped timespan is never
below half the ideal timespan: the ZIP-208 lower bound. This is the
"factor ≥ 0.5" half of the adjustment-factor bound. -/
theorem clamp_lower_bound (actual ideal : Nat) :
    ideal / 2 ≤ clampActualTimespan actual ideal := by
  unfold clampActualTimespan
  exact Nat.le_max_left _ _

/-- **T4 (clamp upper bound: ≤ ideal*2).** The clamped timespan is never
above twice the ideal timespan: the ZIP-208 upper bound. This is the
"factor ≤ 2.0" half of the adjustment-factor bound. -/
theorem clamp_upper_bound (actual ideal : Nat) :
    clampActualTimespan actual ideal ≤ ideal * 2 := by
  unfold clampActualTimespan
  -- max (ideal/2) (min actual (ideal*2)) ≤ ideal*2
  apply max_le
  · -- ideal/2 ≤ ideal*2
    have h2 : ideal / 2 ≤ ideal := Nat.div_le_self _ _
    have h3 : ideal ≤ ideal * 2 := Nat.le_mul_of_pos_right _ (by decide)
    exact le_trans h2 h3
  · exact min_le_right _ _

/-- **T5 (clamp is identity on the in-band region).** Any `actual` already
in `[ideal/2, ideal*2]` is unchanged by `clampActualTimespan`. -/
theorem clamp_in_band_identity (actual ideal : Nat)
    (hlo : ideal / 2 ≤ actual) (hhi : actual ≤ ideal * 2) :
    clampActualTimespan actual ideal = actual := by
  unfold clampActualTimespan
  have hmin : min actual (ideal * 2) = actual := min_eq_left hhi
  rw [hmin]
  exact max_eq_right hlo

/-- **T6 (clamp saturates from above).** Any `actual > ideal*2` is clamped
down to `ideal*2`. -/
theorem clamp_saturates_high (actual ideal : Nat)
    (hhi : ideal * 2 < actual) :
    clampActualTimespan actual ideal = ideal * 2 := by
  unfold clampActualTimespan
  have hmin : min actual (ideal * 2) = ideal * 2 :=
    min_eq_right (le_of_lt hhi)
  rw [hmin]
  -- max (ideal/2) (ideal*2) = ideal*2
  apply max_eq_right
  have h2 : ideal / 2 ≤ ideal := Nat.div_le_self _ _
  have h3 : ideal ≤ ideal * 2 := Nat.le_mul_of_pos_right _ (by decide)
  exact le_trans h2 h3

/-- **T7 (clamp saturates from below).** Any `actual < ideal/2` is clamped
up to `ideal/2`. -/
theorem clamp_saturates_low (actual ideal : Nat)
    (hlo : actual < ideal / 2) :
    clampActualTimespan actual ideal = ideal / 2 := by
  unfold clampActualTimespan
  have hmin : min actual (ideal * 2) = actual := by
    apply min_eq_left
    have h2 : ideal / 2 ≤ ideal := Nat.div_le_self _ _
    have h3 : ideal ≤ ideal * 2 := Nat.le_mul_of_pos_right _ (by decide)
    omega
  rw [hmin]
  exact max_eq_left (le_of_lt hlo)

/-- **T8 (clamp is monotone in `actual`).** Clamping preserves the order
of the input "actual" timespan. -/
theorem clamp_monotone (a₁ a₂ ideal : Nat) (hle : a₁ ≤ a₂) :
    clampActualTimespan a₁ ideal ≤ clampActualTimespan a₂ ideal := by
  unfold clampActualTimespan
  apply max_le_max (le_refl _)
  exact min_le_min hle (le_refl _)

/-- **T9 (clamped value lies in `[ideal/2, ideal*2]`).** Combination of
T3 and T4: the clamped timespan always lies in the ZIP-208 band. -/
theorem clamp_in_band (actual ideal : Nat) :
    ideal / 2 ≤ clampActualTimespan actual ideal ∧
      clampActualTimespan actual ideal ≤ ideal * 2 :=
  ⟨clamp_lower_bound actual ideal, clamp_upper_bound actual ideal⟩

/-- **T10 (averaging window and median span are distinct, both positive).**
Sanity-check on the constants. -/
theorem constants_positive :
    0 < POW_AVERAGING_WINDOW ∧ 0 < POW_MEDIAN_BLOCK_SPAN
      ∧ POW_MEDIAN_BLOCK_SPAN < POW_AVERAGING_WINDOW := by
  unfold POW_AVERAGING_WINDOW POW_MEDIAN_BLOCK_SPAN
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **T11 (concrete example: median of a sorted list).** For an already
sorted 11-element list, the median is just the element at index 5. -/
theorem medianOf11_sorted_example :
    medianOf11 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] = 6 := by
  unfold medianOf11 POW_MEDIAN_BLOCK_SPAN
  decide

/-- **T12 (concrete example: median of an unsorted list).** The median is
order-independent — it depends only on the multiset of inputs. -/
theorem medianOf11_unsorted_example :
    medianOf11 [11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1] = 6 := by
  unfold medianOf11 POW_MEDIAN_BLOCK_SPAN
  decide

/-- **T13 (concrete example of mean over a 17-list).** A 17-block window of
identical 150-second timestamps has mean exactly 150. -/
theorem mean17_constant_pre_blossom :
    mean17 (List.replicate 17 150) = 150 := by
  unfold mean17 POW_AVERAGING_WINDOW
  have hlen : (List.replicate 17 150).length = 17 := List.length_replicate
  simp [hlen]

/-- **T14 (concrete example of mean over a 17-list of post-Blossom block
times).** A 17-block window of identical 75-second timestamps has mean
exactly 75. -/
theorem mean17_constant_post_blossom :
    mean17 (List.replicate 17 75) = 75 := by
  unfold mean17 POW_AVERAGING_WINDOW
  have hlen : (List.replicate 17 75).length = 17 := List.length_replicate
  simp [hlen]

/-- **T15 (clamp of the ideal value is the ideal value).** When the actual
timespan equals the ideal, no adjustment occurs. (Requires `ideal ≥ 1` so
that `ideal/2 ≤ ideal`.) -/
theorem clamp_at_ideal (ideal : Nat) :
    clampActualTimespan ideal ideal = ideal := by
  apply clamp_in_band_identity
  · exact Nat.div_le_self _ _
  · exact Nat.le_mul_of_pos_right _ (by decide)

end Zebra.DAAMedianWindow
