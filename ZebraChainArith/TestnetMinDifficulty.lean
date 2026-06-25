import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Testnet minimum-difficulty rule (ZIP-208)

From `zebra-chain/src/parameters/network_upgrade.rs`.

The testnet minimum-difficulty rule says: at height
`≥ TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT`, a testnet block whose time gap
to the previous block is strictly greater than
`6 * POST_BLOSSOM_POW_TARGET_SPACING` seconds is treated as minimum difficulty.

Modeled constants:
- `POST_BLOSSOM_POW_TARGET_SPACING : Nat := 75` seconds (post-Blossom upgrades).
- `PRE_BLOSSOM_POW_TARGET_SPACING : Int := 150` seconds (pre-Blossom upgrades).
- `TESTNET_MINIMUM_DIFFICULTY_GAP_MULTIPLIER : Int := 6`.
- `TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT : Nat := 299_188`.

The key arithmetic identity to verify is the post-Blossom gap threshold:
`6 * 75 = 450` seconds.
-/

namespace Zebra.TestnetMinDifficulty

/-- Pre-Blossom PoW target block spacing in seconds.
Source: `zebra-chain/src/parameters/network_upgrade.rs:243` -/
def PRE_BLOSSOM_POW_TARGET_SPACING : Int := 150

/-- Post-Blossom PoW target block spacing in seconds.
Source: `zebra-chain/src/parameters/network_upgrade.rs:246` -/
def POST_BLOSSOM_POW_TARGET_SPACING : Nat := 75

/-- Multiplier used to derive the testnet minimum-difficulty time-gap threshold.
Source: `zebra-chain/src/parameters/network_upgrade.rs:257` -/
def TESTNET_MINIMUM_DIFFICULTY_GAP_MULTIPLIER : Int := 6

/-- Start height for the testnet minimum-difficulty consensus rule.
Source: `zebra-chain/src/parameters/network_upgrade.rs:262` -/
def TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT : Nat := 299188

/-- Post-Blossom target-spacing in seconds, lifted to `Int` (matches the Rust
arithmetic `POST_BLOSSOM_POW_TARGET_SPACING.into()` widening `u32` to `i64`).
Source: `zebra-chain/src/parameters/network_upgrade.rs:405` -/
def postBlossomSpacingInt : Int := (POST_BLOSSOM_POW_TARGET_SPACING : Int)

/-- Minimum-difficulty time-gap threshold in seconds for a post-Blossom upgrade:
`target_spacing * 6`.
Source: `zebra-chain/src/parameters/network_upgrade.rs:459` -/
def postBlossomMinDifficultyGap : Int :=
  postBlossomSpacingInt * TESTNET_MINIMUM_DIFFICULTY_GAP_MULTIPLIER

/-- Minimum-difficulty time-gap threshold in seconds for a pre-Blossom upgrade:
`target_spacing * 6 = 150 * 6 = 900` seconds.
Source: `zebra-chain/src/parameters/network_upgrade.rs:459` -/
def preBlossomMinDifficultyGap : Int :=
  PRE_BLOSSOM_POW_TARGET_SPACING * TESTNET_MINIMUM_DIFFICULTY_GAP_MULTIPLIER

/-- `minimum_difficulty_spacing_for_height` restricted to Testnet, using only
post-Blossom spacing (since the testnet min-difficulty start height
`299_188` is past Blossom activation on testnet).

Returns `some gap` iff `network = Testnet` and `height ≥ start`. Mainnet
always returns `none`.
Source: `zebra-chain/src/parameters/network_upgrade.rs:445` -/
def minimumDifficultySpacingForHeight (isTestnet : Bool) (height : Nat) :
    Option Int :=
  if isTestnet ∧ height ≥ TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT then
    some postBlossomMinDifficultyGap
  else
    none

/-- `is_testnet_min_difficulty_block`: the block is treated as min-difficulty
iff the time gap exceeds the threshold. We model `block_time` and
`previous_block_time` as their `Int`-second difference `blockTimeGap`.
Source: `zebra-chain/src/parameters/network_upgrade.rs:479` -/
def isTestnetMinDifficultyBlock
    (isTestnet : Bool) (height : Nat) (blockTimeGap : Int) : Bool :=
  match minimumDifficultySpacingForHeight isTestnet height with
  | some gap => decide (blockTimeGap > gap)
  | none     => false

/-! ## Theorems -/

/-- **T1.** The post-Blossom min-difficulty gap is exactly `450` seconds:
`6 * POST_BLOSSOM_POW_TARGET_SPACING = 450`. -/
theorem postBlossomMinDifficultyGap_eq_450 :
    postBlossomMinDifficultyGap = 450 := by
  unfold postBlossomMinDifficultyGap postBlossomSpacingInt
        POST_BLOSSOM_POW_TARGET_SPACING TESTNET_MINIMUM_DIFFICULTY_GAP_MULTIPLIER
  decide

/-- **T2.** The pre-Blossom min-difficulty gap is exactly `900` seconds:
`6 * 150 = 900`. -/
theorem preBlossomMinDifficultyGap_eq_900 :
    preBlossomMinDifficultyGap = 900 := by
  unfold preBlossomMinDifficultyGap
        PRE_BLOSSOM_POW_TARGET_SPACING TESTNET_MINIMUM_DIFFICULTY_GAP_MULTIPLIER
  decide

/-- **T3.** `minimumDifficultySpacingForHeight` returns `some` exactly on
Testnet at or after the start height. -/
theorem minimumDifficultySpacingForHeight_isSome_iff
    (isTestnet : Bool) (height : Nat) :
    (minimumDifficultySpacingForHeight isTestnet height).isSome ↔
      isTestnet = true ∧ height ≥ TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT := by
  unfold minimumDifficultySpacingForHeight
  by_cases htest : isTestnet = true
  · by_cases hh : height ≥ TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT
    · simp [htest, hh]
    · simp [htest, hh]
  · simp [htest]

/-- **T4.** On Mainnet, the min-difficulty spacing is always `none`. -/
theorem minimumDifficultySpacingForHeight_mainnet (height : Nat) :
    minimumDifficultySpacingForHeight false height = none := by
  unfold minimumDifficultySpacingForHeight
  simp

/-- **T5.** Below the start height on Testnet, the min-difficulty spacing is
`none`. -/
theorem minimumDifficultySpacingForHeight_below_start (height : Nat)
    (h : height < TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT) :
    minimumDifficultySpacingForHeight true height = none := by
  unfold minimumDifficultySpacingForHeight
  have hnot : ¬ height ≥ TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT := by omega
  simp [hnot]

/-- **T6.** At or above the start height on Testnet, the gap is always `450`. -/
theorem minimumDifficultySpacingForHeight_testnet_active (height : Nat)
    (h : height ≥ TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT) :
    minimumDifficultySpacingForHeight true height = some 450 := by
  unfold minimumDifficultySpacingForHeight
  simp [h, postBlossomMinDifficultyGap_eq_450]

/-- **T7.** On Mainnet, no block is ever considered a testnet min-difficulty
block, regardless of height or time gap. -/
theorem isTestnetMinDifficultyBlock_mainnet
    (height : Nat) (gap : Int) :
    isTestnetMinDifficultyBlock false height gap = false := by
  unfold isTestnetMinDifficultyBlock
  rw [minimumDifficultySpacingForHeight_mainnet]

/-- **T8.** On Testnet below the start height, no block is a min-difficulty
block. -/
theorem isTestnetMinDifficultyBlock_below_start
    (height : Nat) (gap : Int)
    (h : height < TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT) :
    isTestnetMinDifficultyBlock true height gap = false := by
  unfold isTestnetMinDifficultyBlock
  rw [minimumDifficultySpacingForHeight_below_start _ h]

/-- **T9.** On Testnet at/after the start height, a block qualifies iff the
time gap is strictly greater than `450` seconds. -/
theorem isTestnetMinDifficultyBlock_active_iff
    (height : Nat) (gap : Int)
    (h : height ≥ TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT) :
    isTestnetMinDifficultyBlock true height gap = true ↔ gap > 450 := by
  unfold isTestnetMinDifficultyBlock
  rw [minimumDifficultySpacingForHeight_testnet_active _ h]
  simp

/-- **T10.** A time gap of exactly `450` seconds is *not* enough — the rule
uses strict `>`, not `≥`. -/
theorem isTestnetMinDifficultyBlock_boundary_strict
    (height : Nat) (h : height ≥ TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT) :
    isTestnetMinDifficultyBlock true height 450 = false := by
  unfold isTestnetMinDifficultyBlock
  rw [minimumDifficultySpacingForHeight_testnet_active _ h]
  decide

/-- **T11.** A time gap of `451` seconds at the start height triggers
min-difficulty. -/
theorem isTestnetMinDifficultyBlock_above_boundary :
    isTestnetMinDifficultyBlock true TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT 451
      = true := by
  unfold isTestnetMinDifficultyBlock
  rw [minimumDifficultySpacingForHeight_testnet_active _ (Nat.le_refl _)]
  decide

/-- **T12.** Monotonicity in the time gap: if a smaller gap triggers
min-difficulty, then any larger gap does too. -/
theorem isTestnetMinDifficultyBlock_mono_gap
    (height : Nat) (g₁ g₂ : Int) (hle : g₁ ≤ g₂)
    (h₁ : isTestnetMinDifficultyBlock true height g₁ = true) :
    isTestnetMinDifficultyBlock true height g₂ = true := by
  unfold isTestnetMinDifficultyBlock at h₁ ⊢
  cases hspacing :
      minimumDifficultySpacingForHeight true height with
  | none =>
      rw [hspacing] at h₁
      simp at h₁
  | some gap =>
      rw [hspacing] at h₁
      simp at h₁
      simp
      linarith

end Zebra.TestnetMinDifficulty
