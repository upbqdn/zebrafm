import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Zebrafm.Subsidy

/-!
# Slow-start block subsidy ramp

Models the pre-`SLOW_START_INTERVAL` portion of `block_subsidy(h)` from
`zebra-chain/src/parameters/network/subsidy.rs`. Before block height
`SLOW_START_INTERVAL` (20_000 on mainnet) the per-block subsidy ramps
linearly from 0 toward `MAX_BLOCK_SUBSIDY`, with a one-block "shift"
at `SLOW_START_SHIFT = SLOW_START_INTERVAL / 2` that adds an extra
`slow_start_rate` of subsidy so that the post-shift portion catches up
to exactly `MAX_BLOCK_SUBSIDY` at the boundary.

The Rust formula (from `block_subsidy` in `subsidy.rs`):

```rust
let slow_start_rate = MAX_BLOCK_SUBSIDY / u64::from(slow_start_interval);
if height < net.slow_start_shift() {
    slow_start_rate * u64::from(height)
} else {
    slow_start_rate * (u64::from(height) + 1)
}
```

Both branches multiply by `slow_start_rate`. The change at the shift
boundary is that `(h+1)` replaces `h`, compensating for the slow start.

Concrete mainnet constants used here:
  * `SLOW_START_INTERVAL = 20_000`
  * `SLOW_START_SHIFT    = 10_000`
  * `MAX_BLOCK_SUBSIDY   = (25 * COIN) / 2 = 1_250_000_000`
  * `slowStartRate       = MAX_BLOCK_SUBSIDY / SLOW_START_INTERVAL = 62_500`

Source: `zebra-chain/src/parameters/network/subsidy.rs:460-467`
       (the `if height < slow_start_interval` branch of `block_subsidy`)
Source: `zebra-chain/src/parameters/constants.rs:11`
       (`SLOW_START_INTERVAL`)
Source: `zebra-chain/src/parameters/constants.rs:18`
       (`SLOW_START_SHIFT = SLOW_START_INTERVAL / 2`)
-/

namespace Zebra.SlowStartSubsidy

/-- Number of zatoshis in 1 ZEC. -/
def COIN : Nat := 100_000_000

/-- The genesis block subsidy: `(25 * COIN) / 2 = 1_250_000_000` zats.
Source: `zebra-chain/src/parameters/network/subsidy/constants.rs` -/
def MAX_BLOCK_SUBSIDY : Nat := (25 * COIN) / 2

/-- The slow-start interval on mainnet: subsidies ramp up from 0 over
this many blocks.
Source: `zebra-chain/src/parameters/constants.rs:11` -/
def SLOW_START_INTERVAL : Nat := 20_000

/-- The slow-start shift: half of `SLOW_START_INTERVAL`.
Source: `zebra-chain/src/parameters/constants.rs:18` -/
def SLOW_START_SHIFT : Nat := SLOW_START_INTERVAL / 2

/-- The per-block rate of subsidy increase during the slow-start window.
Source: `zebra-chain/src/parameters/network/subsidy.rs:461` -/
def slowStartRate : Nat := MAX_BLOCK_SUBSIDY / SLOW_START_INTERVAL

/-- The pre-`SLOW_START_INTERVAL` block subsidy. Outside the window we return 0
here, since this module only models the slow-start ramp; the post-window
calculation is in `Zebra.Subsidy`.
Source: `zebra-chain/src/parameters/network/subsidy.rs:460-467` -/
def slowStartSubsidy (h : Nat) : Nat :=
  if h < SLOW_START_INTERVAL then
    if h < SLOW_START_SHIFT then
      slowStartRate * h
    else
      slowStartRate * (h + 1)
  else
    0

/-! ## Concrete-value lemmas

These tie the symbolic constants above to their concrete values, so the
theorems can be read directly against the spec without unfolding.
-/

/-- The shift is `10_000` on mainnet. -/
theorem slowStartShift_value : SLOW_START_SHIFT = 10_000 := by
  unfold SLOW_START_SHIFT SLOW_START_INTERVAL; rfl

/-- The slow-start rate is `62_500` zats per block on mainnet. -/
theorem slowStartRate_value : slowStartRate = 62_500 := by
  unfold slowStartRate MAX_BLOCK_SUBSIDY COIN SLOW_START_INTERVAL; rfl

/-- The maximum block subsidy is `1_250_000_000` zats. -/
theorem maxBlockSubsidy_value : MAX_BLOCK_SUBSIDY = 1_250_000_000 := by
  unfold MAX_BLOCK_SUBSIDY COIN; rfl

/-- The slow-start rate times the slow-start interval equals
`MAX_BLOCK_SUBSIDY` exactly: the ramp is dimensioned to land on the
maximum at the boundary. -/
theorem slowStartRate_mul_interval :
    slowStartRate * SLOW_START_INTERVAL = MAX_BLOCK_SUBSIDY := by
  unfold slowStartRate MAX_BLOCK_SUBSIDY COIN SLOW_START_INTERVAL; rfl

/-! ## Theorems -/

/-- **T1 (genesis subsidy is zero).** At height 0 the pre-shift formula
gives `slowStartRate * 0 = 0`. This matches the Zcash design: there is no
mining reward at genesis. -/
theorem slowStartSubsidy_zero : slowStartSubsidy 0 = 0 := by
  unfold slowStartSubsidy
  simp [SLOW_START_INTERVAL, SLOW_START_SHIFT]

/-- **T2 (subsidy is monotone non-decreasing within the slow-start window).**
For any two heights `h₁ ≤ h₂` both strictly below `SLOW_START_INTERVAL`,
the slow-start subsidy at `h₂` is at least that at `h₁`.

The shift introduces a discrete `slowStartRate`-sized jump at
`h = SLOW_START_SHIFT`, but that jump is *upward*, so monotonicity is
preserved across it. -/
theorem slowStartSubsidy_monotone (h₁ h₂ : Nat)
    (hle : h₁ ≤ h₂) (hLt : h₂ < SLOW_START_INTERVAL) :
    slowStartSubsidy h₁ ≤ slowStartSubsidy h₂ := by
  have hLt1 : h₁ < SLOW_START_INTERVAL := Nat.lt_of_le_of_lt hle hLt
  unfold slowStartSubsidy
  simp [hLt1, hLt]
  by_cases hs1 : h₁ < SLOW_START_SHIFT
  · by_cases hs2 : h₂ < SLOW_START_SHIFT
    · simp [hs1, hs2]
      exact Nat.mul_le_mul_left _ hle
    · simp [hs1, hs2]
      have : h₁ ≤ h₂ + 1 := by omega
      exact Nat.mul_le_mul_left _ this
  · have hs2 : ¬ h₂ < SLOW_START_SHIFT := by omega
    simp [hs1, hs2]
    exact Nat.mul_le_mul_left _ (by omega)

/-- **T3 (subsidy at the shift boundary).** At `h = SLOW_START_SHIFT`,
the post-shift formula gives `slowStartRate * (SLOW_START_SHIFT + 1)`.
Concretely: `62_500 * 10_001 = 625_062_500`. -/
theorem slowStartSubsidy_at_shift :
    slowStartSubsidy SLOW_START_SHIFT = slowStartRate * (SLOW_START_SHIFT + 1) := by
  unfold slowStartSubsidy
  have h1 : SLOW_START_SHIFT < SLOW_START_INTERVAL := by
    unfold SLOW_START_SHIFT SLOW_START_INTERVAL; decide
  have h2 : ¬ SLOW_START_SHIFT < SLOW_START_SHIFT := lt_irrefl _
  simp [h1, h2]

/-- **T4 (subsidy just below the shift).** At `h = SLOW_START_SHIFT - 1`,
the pre-shift formula gives `slowStartRate * (SLOW_START_SHIFT - 1)`.
Concretely: `62_500 * 9_999 = 624_937_500`. This is exactly
`slowStartRate` less than the value at `SLOW_START_SHIFT` would have been
under continued pre-shift arithmetic — the shift compensates by jumping
ahead by 1. -/
theorem slowStartSubsidy_just_below_shift :
    slowStartSubsidy (SLOW_START_SHIFT - 1) = slowStartRate * (SLOW_START_SHIFT - 1) := by
  unfold slowStartSubsidy
  have h1 : SLOW_START_SHIFT - 1 < SLOW_START_INTERVAL := by
    unfold SLOW_START_SHIFT SLOW_START_INTERVAL; decide
  have h2 : SLOW_START_SHIFT - 1 < SLOW_START_SHIFT := by
    unfold SLOW_START_SHIFT SLOW_START_INTERVAL; decide
  simp [h1, h2]

/-- **T5 (subsidy at the last in-window block matches `MAX_BLOCK_SUBSIDY`).**
At `h = SLOW_START_INTERVAL - 1 = 19_999`, the formula gives
`slowStartRate * (h + 1) = slowStartRate * SLOW_START_INTERVAL =
MAX_BLOCK_SUBSIDY`. This is the key invariant: the ramp lands on the
maximum subsidy exactly at the boundary, so there is no discontinuity
when control transfers to the post-slow-start formula. -/
theorem slowStartSubsidy_at_interval_minus_one :
    slowStartSubsidy (SLOW_START_INTERVAL - 1) = MAX_BLOCK_SUBSIDY := by
  unfold slowStartSubsidy
  have h1 : SLOW_START_INTERVAL - 1 < SLOW_START_INTERVAL := by
    unfold SLOW_START_INTERVAL; decide
  have h2 : ¬ SLOW_START_INTERVAL - 1 < SLOW_START_SHIFT := by
    unfold SLOW_START_INTERVAL SLOW_START_SHIFT; decide
  simp [h1, h2]
  -- Goal: slowStartRate * ((SLOW_START_INTERVAL - 1) + 1) = MAX_BLOCK_SUBSIDY
  have hrw : (SLOW_START_INTERVAL - 1) + 1 = SLOW_START_INTERVAL := by
    unfold SLOW_START_INTERVAL; decide
  rw [hrw, slowStartRate_mul_interval]

/-- **T6 (subsidy is bounded above by `MAX_BLOCK_SUBSIDY` within the window).**
Within the slow-start window, the per-block subsidy never exceeds
`MAX_BLOCK_SUBSIDY`. This is the load-bearing security invariant:
no individual block over-pays the mining reward during the ramp. -/
theorem slowStartSubsidy_le_max (h : Nat) (hLt : h < SLOW_START_INTERVAL) :
    slowStartSubsidy h ≤ MAX_BLOCK_SUBSIDY := by
  unfold slowStartSubsidy
  simp [hLt]
  by_cases hs : h < SLOW_START_SHIFT
  · simp [hs]
    -- slowStartRate * h ≤ slowStartRate * SLOW_START_INTERVAL = MAX_BLOCK_SUBSIDY
    have hbd : h ≤ SLOW_START_INTERVAL := by
      have : SLOW_START_SHIFT ≤ SLOW_START_INTERVAL := by
        unfold SLOW_START_SHIFT SLOW_START_INTERVAL; decide
      omega
    calc slowStartRate * h
        ≤ slowStartRate * SLOW_START_INTERVAL := Nat.mul_le_mul_left _ hbd
      _ = MAX_BLOCK_SUBSIDY := slowStartRate_mul_interval
  · simp [hs]
    -- slowStartRate * (h + 1) ≤ slowStartRate * SLOW_START_INTERVAL = MAX_BLOCK_SUBSIDY
    have hbd : h + 1 ≤ SLOW_START_INTERVAL := by omega
    calc slowStartRate * (h + 1)
        ≤ slowStartRate * SLOW_START_INTERVAL := Nat.mul_le_mul_left _ hbd
      _ = MAX_BLOCK_SUBSIDY := slowStartRate_mul_interval

/-- **T7 (pre-shift subsidy is exactly proportional to height).** For
`h < SLOW_START_SHIFT`, the subsidy is `slowStartRate * h`. This is the
straight-line ramp from 0 — pre-shift, the formula has no `+1`. -/
theorem slowStartSubsidy_pre_shift (h : Nat) (hLt : h < SLOW_START_SHIFT) :
    slowStartSubsidy h = slowStartRate * h := by
  have hInterval : h < SLOW_START_INTERVAL := by
    have : SLOW_START_SHIFT ≤ SLOW_START_INTERVAL := by
      unfold SLOW_START_SHIFT SLOW_START_INTERVAL; decide
    omega
  unfold slowStartSubsidy
  simp [hInterval, hLt]

/-- **T8 (post-shift in-window subsidy uses the `+1` formula).** For
`SLOW_START_SHIFT ≤ h < SLOW_START_INTERVAL`, the subsidy is
`slowStartRate * (h + 1)`. -/
theorem slowStartSubsidy_post_shift (h : Nat)
    (hLo : SLOW_START_SHIFT ≤ h) (hHi : h < SLOW_START_INTERVAL) :
    slowStartSubsidy h = slowStartRate * (h + 1) := by
  unfold slowStartSubsidy
  have hns : ¬ h < SLOW_START_SHIFT := Nat.not_lt.mpr hLo
  simp [hHi, hns]

/-- **T9 (shift contributes exactly `2 * slowStartRate` of subsidy jump).**
Crossing the shift boundary upward by one block (going from `h - 1` to
`h` where `h = SLOW_START_SHIFT`) increases the subsidy by exactly
`2 * slowStartRate`: one factor for the height delta `(h - 1) → h` and
one for the `+1` post-shift adjustment in the Rust formula. The equality
is exact (not just a lower bound). -/
theorem slowStartSubsidy_shift_jump
    (hpos : 0 < SLOW_START_SHIFT) :
    slowStartSubsidy SLOW_START_SHIFT =
      slowStartSubsidy (SLOW_START_SHIFT - 1) + 2 * slowStartRate := by
  rw [slowStartSubsidy_at_shift, slowStartSubsidy_just_below_shift]
  -- Goal: slowStartRate * (SLOW_START_SHIFT + 1) =
  --       slowStartRate * (SLOW_START_SHIFT - 1) + 2 * slowStartRate
  have h1 : SLOW_START_SHIFT + 1 = (SLOW_START_SHIFT - 1) + 2 := by omega
  rw [h1, Nat.mul_add, Nat.mul_comm slowStartRate 2]

/-- **T10 (post-window subsidy is zero in this model).** Outside the
slow-start window, this module returns 0 (the post-window subsidy is
governed by the `Subsidy` module). This is a sanity check that the
domain split is clean. -/
theorem slowStartSubsidy_post_window (h : Nat) (hGe : SLOW_START_INTERVAL ≤ h) :
    slowStartSubsidy h = 0 := by
  unfold slowStartSubsidy
  simp [Nat.not_lt.mpr hGe]

/-! ## Bridge to `Zebra.Subsidy.blockSubsidy`

Rust models block subsidy as a single function `block_subsidy(h)` with a
two-way split at `slow_start_interval` (`subsidy.rs:460-476`). For
modularity the Lean version splits it into `Zebra.SlowStartSubsidy.slowStartSubsidy`
(the ramp, in this module) and `Zebra.Subsidy.blockSubsidy` (the
post-ramp halving cascade). The composition below is the single Lean
function that mirrors Rust's `block_subsidy` end-to-end, plus the
bridge theorems showing it agrees with each side of the split inside
its own domain.

The two namespaces share name `SLOW_START_INTERVAL` etc., so the bridge
also confirms (via `Subsidy.max_block_subsidy_matches_slow_start` and
`Subsidy.slow_start_shift_matches_slow_start`) that the numeric
constants line up between modules. -/

/-- The full Rust `block_subsidy(h)` semantics: ramp inside the
slow-start window, post-window halving cascade above it. Mirrors
`zebra-chain/src/parameters/network/subsidy.rs:460-476` byte-for-byte
on mainnet. -/
def combinedBlockSubsidy (h : Nat) : Nat :=
  if h < SLOW_START_INTERVAL then
    slowStartSubsidy h
  else
    Zebra.Subsidy.blockSubsidy h

/-- The two `SLOW_START_INTERVAL` constants in `Zebra.SlowStartSubsidy`
and `Zebra.Subsidy` are equal (both `20_000`). Sanity check that the
bridge does not silently use mismatched boundaries. -/
theorem slow_start_interval_matches :
    SLOW_START_INTERVAL = Zebra.Subsidy.SLOW_START_INTERVAL := rfl

/-- **B1 (bridge: inside the slow-start window).** For
`h < SLOW_START_INTERVAL` the combined function agrees with the ramp. -/
theorem combinedBlockSubsidy_in_window (h : Nat) (hLt : h < SLOW_START_INTERVAL) :
    combinedBlockSubsidy h = slowStartSubsidy h := by
  unfold combinedBlockSubsidy
  simp [hLt]

/-- **B2 (bridge: outside the slow-start window).** For
`h ≥ SLOW_START_INTERVAL` the combined function agrees with the
post-window cascade in `Zebra.Subsidy`. -/
theorem combinedBlockSubsidy_post_window (h : Nat)
    (hGe : SLOW_START_INTERVAL ≤ h) :
    combinedBlockSubsidy h = Zebra.Subsidy.blockSubsidy h := by
  unfold combinedBlockSubsidy
  simp [Nat.not_lt.mpr hGe]

/-- **B3 (bridge: continuity at the boundary).** Both halves of the
Rust formula return `MAX_BLOCK_SUBSIDY` at the slow-start boundary:
the ramp lands exactly on the maximum at `SLOW_START_INTERVAL - 1`
(T5 above), and the post-ramp formula begins at `MAX_BLOCK_SUBSIDY`
at `SLOW_START_INTERVAL` since the halving index is still 0 and we
are pre-Blossom. This shows the spec function has no discontinuity
at the boundary — the model split does not introduce a phantom jump. -/
theorem combinedBlockSubsidy_continuity_at_boundary :
    combinedBlockSubsidy (SLOW_START_INTERVAL - 1) =
      combinedBlockSubsidy SLOW_START_INTERVAL := by
  -- Left side: ramp at `SLOW_START_INTERVAL - 1` is `MAX_BLOCK_SUBSIDY` (T5).
  have hLt : SLOW_START_INTERVAL - 1 < SLOW_START_INTERVAL := by
    unfold SLOW_START_INTERVAL; decide
  rw [combinedBlockSubsidy_in_window _ hLt,
      slowStartSubsidy_at_interval_minus_one]
  -- Right side: post-ramp at `SLOW_START_INTERVAL` is also `MAX_BLOCK_SUBSIDY`.
  -- At h = 20_000: halving = (20_000 - 10_000)/840_000 = 0, divisor = 1,
  -- baseSubsidy = MAX_BLOCK_SUBSIDY (since 20_000 < BLOSSOM_HEIGHT).
  rw [combinedBlockSubsidy_post_window _ (Nat.le_refl _)]
  change MAX_BLOCK_SUBSIDY = Zebra.Subsidy.blockSubsidy SLOW_START_INTERVAL
  unfold Zebra.Subsidy.blockSubsidy Zebra.Subsidy.halvingDivisor
    Zebra.Subsidy.halving Zebra.Subsidy.baseSubsidy
    Zebra.Subsidy.MAX_BLOCK_SUBSIDY Zebra.Subsidy.COIN
    Zebra.Subsidy.SLOW_START_SHIFT Zebra.Subsidy.SLOW_START_INTERVAL
    Zebra.Subsidy.BLOSSOM_HEIGHT Zebra.Subsidy.PRE_BLOSSOM_HALVING_INTERVAL
    Zebra.Subsidy.BLOSSOM_POW_TARGET_SPACING_RATIO
    Zebra.Subsidy.POST_BLOSSOM_HALVING_INTERVAL
    SLOW_START_INTERVAL MAX_BLOCK_SUBSIDY COIN
  decide

/-- **B4 (bridge: pre-shift agrees with combined at `h = 0`).** Sanity:
the genesis subsidy via the unified function is 0, matching T1. -/
theorem combinedBlockSubsidy_zero : combinedBlockSubsidy 0 = 0 := by
  have hLt : (0 : Nat) < SLOW_START_INTERVAL := by
    unfold SLOW_START_INTERVAL; decide
  rw [combinedBlockSubsidy_in_window 0 hLt, slowStartSubsidy_zero]

/-- **B5 (bridge: pre-Blossom 1st halving sample).** Concrete-vector
check at Blossom activation height: through the combined function, the
mainnet subsidy at `BLOSSOM_HEIGHT = 653_600` is `MAX_BLOCK_SUBSIDY / 2 =
625_000_000` zats — the first halving via the Blossom spacing-ratio
adjustment (not the index-cascade halving). Cross-binds the bridge with
`Subsidy.blockSubsidy_at_blossom`. -/
theorem combinedBlockSubsidy_at_blossom :
    combinedBlockSubsidy Zebra.Subsidy.BLOSSOM_HEIGHT = 625_000_000 := by
  have hGe : SLOW_START_INTERVAL ≤ Zebra.Subsidy.BLOSSOM_HEIGHT := by
    unfold SLOW_START_INTERVAL Zebra.Subsidy.BLOSSOM_HEIGHT; decide
  rw [combinedBlockSubsidy_post_window _ hGe,
      Zebra.Subsidy.blockSubsidy_at_blossom]

end Zebra.SlowStartSubsidy
