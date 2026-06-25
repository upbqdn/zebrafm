import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Halving and block subsidy (post-slow-start)

Models the post-slow-start core of the Zcash block subsidy from
`zebra-chain/src/parameters/network/subsidy.rs` (`halving`, `halving_divisor`,
`block_subsidy`). Pre-slow-start ramp lives in `Zebra.SlowStartSubsidy`.

The Rust `halving` is a 3-branch function (`subsidy.rs:422-446`):

```rust
let halving_index = if height < slow_start_shift {
    0
} else if height < blossom_height {
    let pre_blossom_height = height - slow_start_shift;
    pre_blossom_height / network.pre_blossom_halving_interval()
} else {
    let pre_blossom_height = blossom_height - slow_start_shift;
    let scaled_pre_blossom_height =
        pre_blossom_height * HeightDiff::from(BLOSSOM_POW_TARGET_SPACING_RATIO);
    let post_blossom_height = height - blossom_height;
    (scaled_pre_blossom_height + post_blossom_height) / network.post_blossom_halving_interval()
};
```

The Rust `block_subsidy` post-slow-start branch (`subsidy.rs:469-475`) halves
`MAX_BLOCK_SUBSIDY` once more when the current upgrade is `Blossom` or later:

```rust
let base_subsidy = if NetworkUpgrade::current(net, height) < NetworkUpgrade::Blossom {
    MAX_BLOCK_SUBSIDY
} else {
    MAX_BLOCK_SUBSIDY / u64::from(BLOSSOM_POW_TARGET_SPACING_RATIO)
};
base_subsidy / halving_div
```

The `halving_divisor` itself is `1u64.checked_shl(halving(height, network))`
which is `2 ^ halving(height)` when `halving(height) < 64`, else `None`.

Concrete mainnet constants (`zebra-chain/src/parameters/constants.rs:11,18`
and `zebra-chain/src/parameters/network/subsidy/constants.rs:14,20,25,28-29`):

  * `COIN                          = 100_000_000`
  * `MAX_BLOCK_SUBSIDY             = (25 * COIN) / 2 = 1_250_000_000`
  * `BLOSSOM_POW_TARGET_SPACING_RATIO = 2`
  * `PRE_BLOSSOM_HALVING_INTERVAL  = 840_000`
  * `POST_BLOSSOM_HALVING_INTERVAL = 1_680_000`
  * `SLOW_START_SHIFT              = 10_000`
  * `SLOW_START_INTERVAL           = 20_000`
  * mainnet `BLOSSOM_HEIGHT        = 653_600`
  * mainnet `CANOPY_HEIGHT         = 1_046_400`
-/

namespace Zebra.Subsidy

/-- Number of zatoshis in 1 ZEC. -/
def COIN : Nat := 100_000_000

/-- The largest block subsidy, used before the first halving and before
post-Blossom scaling. `(25 * COIN) / 2 = 1_250_000_000` zats.
Source: `subsidy/constants.rs:14`. -/
def MAX_BLOCK_SUBSIDY : Nat := (25 * COIN) / 2

/-- Pre/post-Blossom block-spacing ratio. After Blossom each spec block takes
half the wall-clock time, so post-Blossom halving intervals are scaled by 2.
Source: `subsidy/constants.rs:20`. -/
def BLOSSOM_POW_TARGET_SPACING_RATIO : Nat := 2

/-- Pre-Blossom halving interval (blocks). On both mainnet and testnet.
Source: `subsidy/constants.rs:25`. -/
def PRE_BLOSSOM_HALVING_INTERVAL : Nat := 840_000

/-- Post-Blossom halving interval (blocks). Defined as
`PRE_BLOSSOM_HALVING_INTERVAL * BLOSSOM_POW_TARGET_SPACING_RATIO`.
Source: `subsidy/constants.rs:28-29`. -/
def POST_BLOSSOM_HALVING_INTERVAL : Nat :=
  PRE_BLOSSOM_HALVING_INTERVAL * BLOSSOM_POW_TARGET_SPACING_RATIO

/-- Mainnet slow-start interval. Blocks before this height ramp up to the
maximum subsidy. Source: `parameters/constants.rs:11`. -/
def SLOW_START_INTERVAL : Nat := 20_000

/-- Slow-start shift; `SLOW_START_INTERVAL / 2` by construction.
Source: `parameters/constants.rs:18`. -/
def SLOW_START_SHIFT : Nat := SLOW_START_INTERVAL / 2

/-- Mainnet Blossom activation height.
Source: `parameters/constants.rs:83`. -/
def BLOSSOM_HEIGHT : Nat := 653_600

/-- Mainnet Canopy activation height. Used only as a witness; not consulted by
`halving`. Source: `parameters/constants.rs:87`. -/
def CANOPY_HEIGHT : Nat := 1_046_400

/-- `u64::MAX`. Subsidy divisors above `2^63` overflow `u64::checked_shl` and
return `None` in Rust. -/
def U64_MAX : Nat := 18_446_744_073_709_551_615

/-! ## Halving index and divisor -/

/-- Mirror of Rust `halving(height, network)` on mainnet, with mainnet
constants substituted.

The function is a 3-way cascade:
  1. `h < SLOW_START_SHIFT` → `0` (pre-shift constant)
  2. `SLOW_START_SHIFT ≤ h < BLOSSOM_HEIGHT` → `(h - SLOW_START_SHIFT) /
     PRE_BLOSSOM_HALVING_INTERVAL` (pre-Blossom quotient)
  3. `h ≥ BLOSSOM_HEIGHT` → `(BPM + (h - BLOSSOM_HEIGHT)) /
     POST_BLOSSOM_HALVING_INTERVAL`, where
     `BPM = (BLOSSOM_HEIGHT - SLOW_START_SHIFT) * BLOSSOM_POW_TARGET_SPACING_RATIO`

Source: `subsidy.rs:422-446`. -/
def halving (h : Nat) : Nat :=
  if h < SLOW_START_SHIFT then
    0
  else if h < BLOSSOM_HEIGHT then
    (h - SLOW_START_SHIFT) / PRE_BLOSSOM_HALVING_INTERVAL
  else
    let scaledPreBlossom :=
      (BLOSSOM_HEIGHT - SLOW_START_SHIFT) * BLOSSOM_POW_TARGET_SPACING_RATIO
    let postBlossom := h - BLOSSOM_HEIGHT
    (scaledPreBlossom + postBlossom) / POST_BLOSSOM_HALVING_INTERVAL

/-- `halving_divisor(h)` = `2^halving(h)` when it fits in `u64`, else `None`.
Source: `subsidy.rs:412-415` (`1u64.checked_shl(halving(...))`). -/
def halvingDivisor (h : Nat) : Option Nat :=
  let k := halving h
  if k < 64 then some (2 ^ k) else none

/-- The post-slow-start "base subsidy" used by `block_subsidy`:
`MAX_BLOCK_SUBSIDY` pre-Blossom, halved once on or after Blossom.
Source: `subsidy.rs:469-473`. -/
def baseSubsidy (h : Nat) : Nat :=
  if h < BLOSSOM_HEIGHT then
    MAX_BLOCK_SUBSIDY
  else
    MAX_BLOCK_SUBSIDY / BLOSSOM_POW_TARGET_SPACING_RATIO

/-- `block_subsidy(h)` for `h ≥ SLOW_START_INTERVAL`. The pre-slow-start ramp
is modelled separately in `Zebra.SlowStartSubsidy.slowStartSubsidy`. Returns 0
when the divisor overflows (eventually-zero-subsidy property).
Source: `subsidy.rs:468-476`. -/
def blockSubsidy (h : Nat) : Nat :=
  match halvingDivisor h with
  | none   => 0
  | some d => baseSubsidy h / d

/-! ## Concrete-value lemmas -/

/-- `POST_BLOSSOM_HALVING_INTERVAL` evaluates to `1_680_000` blocks. -/
theorem post_blossom_halving_interval_value :
    POST_BLOSSOM_HALVING_INTERVAL = 1_680_000 := by
  unfold POST_BLOSSOM_HALVING_INTERVAL PRE_BLOSSOM_HALVING_INTERVAL
    BLOSSOM_POW_TARGET_SPACING_RATIO
  rfl

/-- `MAX_BLOCK_SUBSIDY = 1_250_000_000` zats. -/
theorem max_block_subsidy_value :
    MAX_BLOCK_SUBSIDY = 1_250_000_000 := by
  unfold MAX_BLOCK_SUBSIDY COIN; rfl

/-- `SLOW_START_SHIFT = 10_000` blocks. -/
theorem slow_start_shift_value : SLOW_START_SHIFT = 10_000 := by
  unfold SLOW_START_SHIFT SLOW_START_INTERVAL; rfl

/-- Witness that Canopy activates exactly one post-Blossom interval after
Blossom, modulo the slow-start scaling: the algebraic identity backing
`halving CANOPY_HEIGHT = 1`.

Direct numerical evaluation: `(653_600 - 10_000) * 2 + (1_046_400 - 653_600)`
`= 643_600 * 2 + 392_800 = 1_287_200 + 392_800 = 1_680_000`. -/
theorem canopy_aligns_one_halving :
    (BLOSSOM_HEIGHT - SLOW_START_SHIFT) * BLOSSOM_POW_TARGET_SPACING_RATIO +
      (CANOPY_HEIGHT - BLOSSOM_HEIGHT) = POST_BLOSSOM_HALVING_INTERVAL := by
  rw [show BLOSSOM_HEIGHT = 653_600 from rfl,
      show SLOW_START_SHIFT = 10_000 from rfl,
      show BLOSSOM_POW_TARGET_SPACING_RATIO = 2 from rfl,
      show CANOPY_HEIGHT = 1_046_400 from rfl,
      show POST_BLOSSOM_HALVING_INTERVAL = 1_680_000 from rfl]

/-! ## Halving theorems -/

/-- **T2 (halving is 0 below the slow-start shift).** -/
theorem halving_pre_shift (h : Nat) (hh : h < SLOW_START_SHIFT) :
    halving h = 0 := by
  unfold halving
  simp [hh]

/-- Helper for monotonicity at the pre/post-Blossom boundary: the pre-Blossom
quotient of any height ≤ BLOSSOM_HEIGHT is ≤ the post-Blossom value of any
height ≥ BLOSSOM_HEIGHT. -/
private theorem pre_le_post_halving (h₁ h₂ : Nat)
    (hSS : SLOW_START_SHIFT ≤ h₁) (hBl1 : h₁ < BLOSSOM_HEIGHT)
    (_hBl2 : BLOSSOM_HEIGHT ≤ h₂) :
    (h₁ - SLOW_START_SHIFT) / PRE_BLOSSOM_HALVING_INTERVAL ≤
      ((BLOSSOM_HEIGHT - SLOW_START_SHIFT) * BLOSSOM_POW_TARGET_SPACING_RATIO
        + (h₂ - BLOSSOM_HEIGHT)) / POST_BLOSSOM_HALVING_INTERVAL := by
  have h_num_le : h₁ - SLOW_START_SHIFT ≤ BLOSSOM_HEIGHT - SLOW_START_SHIFT := by
    omega
  have hPosLR :
      POST_BLOSSOM_HALVING_INTERVAL =
        PRE_BLOSSOM_HALVING_INTERVAL * BLOSSOM_POW_TARGET_SPACING_RATIO := by
    unfold POST_BLOSSOM_HALVING_INTERVAL; rfl
  have step1 :
      (h₁ - SLOW_START_SHIFT) / PRE_BLOSSOM_HALVING_INTERVAL
        ≤ (BLOSSOM_HEIGHT - SLOW_START_SHIFT) / PRE_BLOSSOM_HALVING_INTERVAL :=
    Nat.div_le_div_right h_num_le
  have step2 :
      (BLOSSOM_HEIGHT - SLOW_START_SHIFT) / PRE_BLOSSOM_HALVING_INTERVAL
        = ((BLOSSOM_HEIGHT - SLOW_START_SHIFT) * BLOSSOM_POW_TARGET_SPACING_RATIO)
            / POST_BLOSSOM_HALVING_INTERVAL := by
    rw [hPosLR]
    have hr_pos : 0 < BLOSSOM_POW_TARGET_SPACING_RATIO := by
      unfold BLOSSOM_POW_TARGET_SPACING_RATIO; decide
    exact (Nat.mul_div_mul_right (BLOSSOM_HEIGHT - SLOW_START_SHIFT)
      PRE_BLOSSOM_HALVING_INTERVAL hr_pos).symm
  have step3 :
      ((BLOSSOM_HEIGHT - SLOW_START_SHIFT) * BLOSSOM_POW_TARGET_SPACING_RATIO)
          / POST_BLOSSOM_HALVING_INTERVAL
        ≤ ((BLOSSOM_HEIGHT - SLOW_START_SHIFT) * BLOSSOM_POW_TARGET_SPACING_RATIO
            + (h₂ - BLOSSOM_HEIGHT)) / POST_BLOSSOM_HALVING_INTERVAL :=
    Nat.div_le_div_right (Nat.le_add_right _ _)
  -- chain: step1 ; step2 (eq) ; step3
  have step12 :
      (h₁ - SLOW_START_SHIFT) / PRE_BLOSSOM_HALVING_INTERVAL
        ≤ ((BLOSSOM_HEIGHT - SLOW_START_SHIFT) * BLOSSOM_POW_TARGET_SPACING_RATIO)
            / POST_BLOSSOM_HALVING_INTERVAL := by
    rw [← step2]; exact step1
  exact step12.trans step3

/-- **T1 (halving is monotone in height).** -/
theorem halving_monotone (h₁ h₂ : Nat) (hle : h₁ ≤ h₂) :
    halving h₁ ≤ halving h₂ := by
  -- Explicit case analysis on the height of each input, then evaluate `halving`.
  -- Three branches per input, with three impossible combinations (h₁ above h₂'s
  -- range), so six real cases.
  by_cases h1lt : h₁ < SLOW_START_SHIFT
  · -- h₁ pre-shift: halving h₁ = 0, nothing to prove.
    have : halving h₁ = 0 := halving_pre_shift h₁ h1lt
    rw [this]
    exact Nat.zero_le _
  · have h1ge : SLOW_START_SHIFT ≤ h₁ := Nat.not_lt.mp h1lt
    by_cases h1bl : h₁ < BLOSSOM_HEIGHT
    · -- h₁ in pre-Blossom branch.
      have halv1 : halving h₁ = (h₁ - SLOW_START_SHIFT)
          / PRE_BLOSSOM_HALVING_INTERVAL := by
        unfold halving
        simp [h1lt, h1bl]
      rw [halv1]
      by_cases h2bl : h₂ < BLOSSOM_HEIGHT
      · -- h₂ also in pre-Blossom branch.
        have h2lt : ¬ h₂ < SLOW_START_SHIFT := by omega
        have halv2 : halving h₂ = (h₂ - SLOW_START_SHIFT)
            / PRE_BLOSSOM_HALVING_INTERVAL := by
          unfold halving
          simp [h2lt, h2bl]
        rw [halv2]
        exact Nat.div_le_div_right (by omega)
      · -- h₂ in post-Blossom branch.
        have h2ge : BLOSSOM_HEIGHT ≤ h₂ := Nat.not_lt.mp h2bl
        have h2lt : ¬ h₂ < SLOW_START_SHIFT := by
          have : SLOW_START_SHIFT ≤ BLOSSOM_HEIGHT := by
            unfold SLOW_START_SHIFT SLOW_START_INTERVAL BLOSSOM_HEIGHT; decide
          omega
        have halv2 : halving h₂ =
            ((BLOSSOM_HEIGHT - SLOW_START_SHIFT) * BLOSSOM_POW_TARGET_SPACING_RATIO
              + (h₂ - BLOSSOM_HEIGHT)) / POST_BLOSSOM_HALVING_INTERVAL := by
          unfold halving
          simp [h2lt, h2bl]
        rw [halv2]
        exact pre_le_post_halving h₁ h₂ h1ge h1bl h2ge
    · -- h₁ in post-Blossom branch; then h₂ ≥ h₁ ≥ BLOSSOM_HEIGHT.
      have h1ge_bl : BLOSSOM_HEIGHT ≤ h₁ := Nat.not_lt.mp h1bl
      have h2bl : BLOSSOM_HEIGHT ≤ h₂ := le_trans h1ge_bl hle
      have h2lt : ¬ h₂ < SLOW_START_SHIFT := by
        have : SLOW_START_SHIFT ≤ BLOSSOM_HEIGHT := by
          unfold SLOW_START_SHIFT SLOW_START_INTERVAL BLOSSOM_HEIGHT; decide
        omega
      have h2bl' : ¬ h₂ < BLOSSOM_HEIGHT := Nat.not_lt.mpr h2bl
      have halv1 : halving h₁ =
          ((BLOSSOM_HEIGHT - SLOW_START_SHIFT) * BLOSSOM_POW_TARGET_SPACING_RATIO
            + (h₁ - BLOSSOM_HEIGHT)) / POST_BLOSSOM_HALVING_INTERVAL := by
        unfold halving
        simp [h1lt, h1bl]
      have halv2 : halving h₂ =
          ((BLOSSOM_HEIGHT - SLOW_START_SHIFT) * BLOSSOM_POW_TARGET_SPACING_RATIO
            + (h₂ - BLOSSOM_HEIGHT)) / POST_BLOSSOM_HALVING_INTERVAL := by
        unfold halving
        simp [h2lt, h2bl']
      rw [halv1, halv2]
      exact Nat.div_le_div_right (by omega)

/-- **T3 (halving is 0 at Blossom activation on mainnet).**
At Blossom the numerator equals `(BLOSSOM_HEIGHT - SLOW_START_SHIFT) * 2 =
1_287_200 < POST_BLOSSOM_HALVING_INTERVAL = 1_680_000`. -/
theorem halving_at_blossom : halving BLOSSOM_HEIGHT = 0 := by
  unfold halving
  have h1 : ¬ BLOSSOM_HEIGHT < SLOW_START_SHIFT := by
    unfold BLOSSOM_HEIGHT SLOW_START_SHIFT SLOW_START_INTERVAL; decide
  have h2 : ¬ BLOSSOM_HEIGHT < BLOSSOM_HEIGHT := Nat.lt_irrefl _
  simp only [h1, h2, if_false]
  -- Goal: ((BLOSSOM_HEIGHT - SLOW_START_SHIFT) * BLOSSOM_POW_TARGET_SPACING_RATIO
  --        + (BLOSSOM_HEIGHT - BLOSSOM_HEIGHT)) / POST_BLOSSOM_HALVING_INTERVAL = 0
  rw [Nat.sub_self, Nat.add_zero,
      show BLOSSOM_HEIGHT = 653_600 from rfl,
      show SLOW_START_SHIFT = 10_000 from rfl,
      show BLOSSOM_POW_TARGET_SPACING_RATIO = 2 from rfl,
      show POST_BLOSSOM_HALVING_INTERVAL = 1_680_000 from rfl]

/-- **T4 (halving is exactly 1 at Canopy on mainnet).**
This matches Rust: at Canopy the first halving has just kicked in. -/
theorem halving_at_canopy : halving CANOPY_HEIGHT = 1 := by
  unfold halving
  have h1 : ¬ CANOPY_HEIGHT < SLOW_START_SHIFT := by
    unfold CANOPY_HEIGHT SLOW_START_SHIFT SLOW_START_INTERVAL; decide
  have h2 : ¬ CANOPY_HEIGHT < BLOSSOM_HEIGHT := by
    unfold CANOPY_HEIGHT BLOSSOM_HEIGHT; decide
  simp only [h1, h2, if_false]
  rw [show BLOSSOM_HEIGHT = 653_600 from rfl,
      show SLOW_START_SHIFT = 10_000 from rfl,
      show BLOSSOM_POW_TARGET_SPACING_RATIO = 2 from rfl,
      show CANOPY_HEIGHT = 1_046_400 from rfl,
      show POST_BLOSSOM_HALVING_INTERVAL = 1_680_000 from rfl]

/-- **T5 (divisor is `Some(2^k)` when k < 64).** -/
theorem halvingDivisor_in_range (h : Nat) (hk : halving h < 64) :
    halvingDivisor h = some (2 ^ halving h) := by
  unfold halvingDivisor
  simp [hk]

/-- **T6 (divisor is `None` when overflow).** -/
theorem halvingDivisor_overflow (h : Nat) (hk : 64 ≤ halving h) :
    halvingDivisor h = none := by
  unfold halvingDivisor
  simp [Nat.not_lt.mpr hk]

/-- **T7 (eventually-zero subsidy).** Once the halving index reaches 64+, the
divisor overflows u64 and `block_subsidy` returns 0. -/
theorem blockSubsidy_zero_when_overflow (h : Nat) (hk : 64 ≤ halving h) :
    blockSubsidy h = 0 := by
  unfold blockSubsidy
  rw [halvingDivisor_overflow h hk]

/-! ## baseSubsidy and concrete vectors -/

/-- `baseSubsidy h = MAX_BLOCK_SUBSIDY` when `h < BLOSSOM_HEIGHT`. -/
theorem baseSubsidy_pre_blossom (h : Nat) (hh : h < BLOSSOM_HEIGHT) :
    baseSubsidy h = MAX_BLOCK_SUBSIDY := by
  unfold baseSubsidy
  simp [hh]

/-- `baseSubsidy h = MAX_BLOCK_SUBSIDY / 2` when `h ≥ BLOSSOM_HEIGHT`.
This is the post-Blossom 2x correction. -/
theorem baseSubsidy_post_blossom (h : Nat) (hh : BLOSSOM_HEIGHT ≤ h) :
    baseSubsidy h = MAX_BLOCK_SUBSIDY / 2 := by
  unfold baseSubsidy BLOSSOM_POW_TARGET_SPACING_RATIO
  have : ¬ h < BLOSSOM_HEIGHT := Nat.not_lt.mpr hh
  simp [this]

/-- **T8 (post-Blossom subsidy is halved at Blossom activation).** With the
post-Blossom correction applied, the subsidy at the Blossom activation block
is `MAX_BLOCK_SUBSIDY / 2 = 625_000_000` zats — half of what the spec called
the "headline" max. -/
theorem blockSubsidy_at_blossom :
    blockSubsidy BLOSSOM_HEIGHT = 625_000_000 := by
  unfold blockSubsidy
  rw [halvingDivisor_in_range BLOSSOM_HEIGHT
        (by rw [halving_at_blossom]; decide),
      halving_at_blossom, baseSubsidy_post_blossom BLOSSOM_HEIGHT (le_refl _)]
  unfold MAX_BLOCK_SUBSIDY COIN
  decide

/-- **T9 (subsidy at Canopy first halving).** At Canopy the divisor is 2 and
the post-Blossom base is `MAX_BLOCK_SUBSIDY / 2`, giving
`625_000_000 / 2 = 312_500_000` zats. -/
theorem blockSubsidy_at_canopy :
    blockSubsidy CANOPY_HEIGHT = 312_500_000 := by
  unfold blockSubsidy
  rw [halvingDivisor_in_range CANOPY_HEIGHT
        (by rw [halving_at_canopy]; decide),
      halving_at_canopy,
      baseSubsidy_post_blossom CANOPY_HEIGHT
        (by unfold CANOPY_HEIGHT BLOSSOM_HEIGHT; decide)]
  unfold MAX_BLOCK_SUBSIDY COIN
  decide

/-- **T10 (subsidy is monotone non-increasing in height past Blossom).**
Within the post-Blossom range with no divisor overflow, doubling the halving
index or moving deeper into a halving epoch only shrinks the subsidy. The
post-Blossom base is constant `MAX_BLOCK_SUBSIDY / 2`, so the only moving part
is the halving divisor. -/
theorem blockSubsidy_post_blossom_nonincreasing
    (h₁ h₂ : Nat) (hBl : BLOSSOM_HEIGHT ≤ h₁) (hle : h₁ ≤ h₂)
    (hk : halving h₂ < 64) :
    blockSubsidy h₂ ≤ blockSubsidy h₁ := by
  unfold blockSubsidy
  have hBl2 : BLOSSOM_HEIGHT ≤ h₂ := le_trans hBl hle
  have hk1 : halving h₁ < 64 := lt_of_le_of_lt (halving_monotone h₁ h₂ hle) hk
  rw [halvingDivisor_in_range h₁ hk1, halvingDivisor_in_range h₂ hk]
  rw [baseSubsidy_post_blossom h₁ hBl, baseSubsidy_post_blossom h₂ hBl2]
  -- Both reduce to `(MAX/2) / 2^(halving h_i)`, with `halving h₁ ≤ halving h₂`.
  apply Nat.div_le_div_left
  · exact Nat.pow_le_pow_right (by norm_num) (halving_monotone h₁ h₂ hle)
  · exact Nat.two_pow_pos _

/-! ## Cross-module sanity -/

/-- `POST_BLOSSOM_HALVING_INTERVAL` in `Subsidy` matches the explicit
`1_680_000` baked into the dev-fund constants module. -/
theorem post_blossom_halving_interval_matches_devfund :
    POST_BLOSSOM_HALVING_INTERVAL = 1_680_000 :=
  post_blossom_halving_interval_value

/-- `MAX_BLOCK_SUBSIDY` in `Subsidy` matches the value in `SlowStartSubsidy`
(both are `(25 * COIN) / 2 = 1_250_000_000`). The number is fixed at the
spec level. -/
theorem max_block_subsidy_matches_slow_start :
    MAX_BLOCK_SUBSIDY = 1_250_000_000 :=
  max_block_subsidy_value

/-- `SLOW_START_SHIFT` in `Subsidy` matches the value in `SlowStartSubsidy`
(both are `SLOW_START_INTERVAL / 2 = 10_000`). -/
theorem slow_start_shift_matches_slow_start :
    SLOW_START_SHIFT = 10_000 :=
  slow_start_shift_value

end Zebra.Subsidy
