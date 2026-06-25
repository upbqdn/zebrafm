import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Testnet minimum-difficulty rule (ZIP-208)

From `zebra-chain/src/parameters/network_upgrade.rs`.

The testnet minimum-difficulty rule says: at height
`≥ TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT`, a testnet block whose time gap
to the previous block is strictly greater than
`6 * target_spacing(current_upgrade(height))` seconds is treated as minimum
difficulty.

The threshold therefore depends on which network upgrade is active at the
given height, **not** on a single hard-coded constant. The rule activates at
height `299_188`, but Blossom does not activate on testnet until height
`584_000`. So the threshold is:

* `[299_188, 584_000)` — Sapling is the current upgrade, pre-Blossom spacing
  `150` s applies, threshold `150 * 6 = 900` s.
* `[584_000, ∞)` — Blossom or later, post-Blossom spacing `75` s applies,
  threshold `75 * 6 = 450` s.

Modeled constants:
* `POST_BLOSSOM_POW_TARGET_SPACING : Nat := 75` seconds (post-Blossom upgrades).
* `PRE_BLOSSOM_POW_TARGET_SPACING : Int := 150` seconds (pre-Blossom upgrades).
* `TESTNET_MINIMUM_DIFFICULTY_GAP_MULTIPLIER : Int := 6`.
* `TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT : Nat := 299_188`.
* `TESTNET_BLOSSOM_ACTIVATION_HEIGHT : Nat := 584_000`.
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

/-- Activation height of `Blossom` on Testnet — used to split the testnet
min-difficulty rule into a pre-Blossom (Sapling) region with threshold `900 s`
and a post-Blossom region with threshold `450 s`.
Source: `zebra-chain/src/parameters/constants.rs:57` -/
def TESTNET_BLOSSOM_ACTIVATION_HEIGHT : Nat := 584000

/-- Post-Blossom target-spacing in seconds, lifted to `Int` (matches the Rust
arithmetic `POST_BLOSSOM_POW_TARGET_SPACING.into()` widening `u32` to `i64`).
Source: `zebra-chain/src/parameters/network_upgrade.rs:405` -/
def postBlossomSpacingInt : Int := (POST_BLOSSOM_POW_TARGET_SPACING : Int)

/-- Minimum-difficulty time-gap threshold in seconds for a post-Blossom upgrade:
`target_spacing * 6 = 75 * 6 = 450` seconds.
Source: `zebra-chain/src/parameters/network_upgrade.rs:459` -/
def postBlossomMinDifficultyGap : Int :=
  postBlossomSpacingInt * TESTNET_MINIMUM_DIFFICULTY_GAP_MULTIPLIER

/-- Minimum-difficulty time-gap threshold in seconds for a pre-Blossom upgrade:
`target_spacing * 6 = 150 * 6 = 900` seconds.
Source: `zebra-chain/src/parameters/network_upgrade.rs:459` -/
def preBlossomMinDifficultyGap : Int :=
  PRE_BLOSSOM_POW_TARGET_SPACING * TESTNET_MINIMUM_DIFFICULTY_GAP_MULTIPLIER

/-- The min-difficulty threshold that applies at testnet `height`, assuming the
rule is active (`height ≥ TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT`):

* heights in `[start, BLOSSOM)` are Sapling, so the threshold is `900 s`;
* heights in `[BLOSSOM, ∞)` are post-Blossom, so the threshold is `450 s`.

Mirrors Rust `NetworkUpgrade::current(testnet, height).target_spacing() * 6`
once min-difficulty is active. -/
def thresholdForTestnetHeight (height : Nat) : Int :=
  if height < TESTNET_BLOSSOM_ACTIVATION_HEIGHT then
    preBlossomMinDifficultyGap
  else
    postBlossomMinDifficultyGap

/-- `minimum_difficulty_spacing_for_height` restricted to the (network, height)
pair. Returns `some gap` iff `network = Testnet` and `height ≥ start`. The
returned gap depends on which network upgrade is current at `height`
(pre- vs. post-Blossom). Mainnet always returns `none`.
Source: `zebra-chain/src/parameters/network_upgrade.rs:445` -/
def minimumDifficultySpacingForHeight (isTestnet : Bool) (height : Nat) :
    Option Int :=
  if isTestnet ∧ height ≥ TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT then
    some (thresholdForTestnetHeight height)
  else
    none

/-- `is_testnet_min_difficulty_block`: the block is treated as min-difficulty
iff the time gap exceeds the upgrade-specific threshold. We model
`block_time` and `previous_block_time` as their `Int`-second difference
`blockTimeGap`.
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

/-- **T6.** At or above the start height on Testnet, the spacing is
`some (thresholdForTestnetHeight height)`. This is the height-aware version
that correctly returns `900 s` for Sapling-era heights and `450 s` for
post-Blossom heights — **not** a single hard-coded `450`. -/
theorem minimumDifficultySpacingForHeight_testnet_active (height : Nat)
    (h : height ≥ TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT) :
    minimumDifficultySpacingForHeight true height
      = some (thresholdForTestnetHeight height) := by
  unfold minimumDifficultySpacingForHeight
  simp [h]

/-- **T6a.** Sapling-region case of T6: for heights in `[start, BLOSSOM)` on
Testnet, the spacing is `some 900`. This is the band the previous version of
this module silently mis-handled (it returned `450` for ~285k blocks). -/
theorem minimumDifficultySpacingForHeight_testnet_sapling (height : Nat)
    (h_lo : height ≥ TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT)
    (h_hi : height < TESTNET_BLOSSOM_ACTIVATION_HEIGHT) :
    minimumDifficultySpacingForHeight true height = some 900 := by
  rw [minimumDifficultySpacingForHeight_testnet_active _ h_lo]
  unfold thresholdForTestnetHeight
  simp [h_hi, preBlossomMinDifficultyGap_eq_900]

/-- **T6b.** Post-Blossom case of T6: for heights in `[BLOSSOM, ∞)` on Testnet,
the spacing is `some 450`. -/
theorem minimumDifficultySpacingForHeight_testnet_blossom (height : Nat)
    (h : height ≥ TESTNET_BLOSSOM_ACTIVATION_HEIGHT) :
    minimumDifficultySpacingForHeight true height = some 450 := by
  have h_lo : height ≥ TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT := by
    unfold TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT
          TESTNET_BLOSSOM_ACTIVATION_HEIGHT at *
    omega
  rw [minimumDifficultySpacingForHeight_testnet_active _ h_lo]
  unfold thresholdForTestnetHeight
  have h_not_lt : ¬ height < TESTNET_BLOSSOM_ACTIVATION_HEIGHT := by omega
  simp [h_not_lt, postBlossomMinDifficultyGap_eq_450]

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
time gap is strictly greater than the height-dependent threshold
(`900 s` pre-Blossom, `450 s` post-Blossom). -/
theorem isTestnetMinDifficultyBlock_active_iff
    (height : Nat) (gap : Int)
    (h : height ≥ TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT) :
    isTestnetMinDifficultyBlock true height gap = true ↔
      gap > thresholdForTestnetHeight height := by
  unfold isTestnetMinDifficultyBlock
  rw [minimumDifficultySpacingForHeight_testnet_active _ h]
  simp

/-- **T9a.** Sapling-region specialisation of T9: pre-Blossom, the rule fires
iff `gap > 900`. -/
theorem isTestnetMinDifficultyBlock_active_sapling_iff
    (height : Nat) (gap : Int)
    (h_lo : height ≥ TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT)
    (h_hi : height < TESTNET_BLOSSOM_ACTIVATION_HEIGHT) :
    isTestnetMinDifficultyBlock true height gap = true ↔ gap > 900 := by
  unfold isTestnetMinDifficultyBlock
  rw [minimumDifficultySpacingForHeight_testnet_sapling _ h_lo h_hi]
  simp

/-- **T9b.** Post-Blossom specialisation of T9: the rule fires iff `gap > 450`. -/
theorem isTestnetMinDifficultyBlock_active_blossom_iff
    (height : Nat) (gap : Int)
    (h : height ≥ TESTNET_BLOSSOM_ACTIVATION_HEIGHT) :
    isTestnetMinDifficultyBlock true height gap = true ↔ gap > 450 := by
  unfold isTestnetMinDifficultyBlock
  rw [minimumDifficultySpacingForHeight_testnet_blossom _ h]
  simp

/-- **T10.** The boundary is **strict** (`>`, not `≥`) — a gap equal to the
threshold is *not* enough. We state the post-Blossom version explicitly here:
at heights `≥ BLOSSOM`, a gap of exactly `450 s` does not trigger the rule.
The pre-Blossom analogue lives in `_boundary_strict_sapling`. -/
theorem isTestnetMinDifficultyBlock_boundary_strict
    (height : Nat) (h : height ≥ TESTNET_BLOSSOM_ACTIVATION_HEIGHT) :
    isTestnetMinDifficultyBlock true height 450 = false := by
  unfold isTestnetMinDifficultyBlock
  rw [minimumDifficultySpacingForHeight_testnet_blossom _ h]
  decide

/-- **T10a.** Sapling-region version of T10: at heights in `[start, BLOSSOM)`,
a gap of exactly `900 s` does not trigger the rule. -/
theorem isTestnetMinDifficultyBlock_boundary_strict_sapling
    (height : Nat)
    (h_lo : height ≥ TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT)
    (h_hi : height < TESTNET_BLOSSOM_ACTIVATION_HEIGHT) :
    isTestnetMinDifficultyBlock true height 900 = false := by
  unfold isTestnetMinDifficultyBlock
  rw [minimumDifficultySpacingForHeight_testnet_sapling _ h_lo h_hi]
  decide

/-- **T11.** Concrete vector exhibiting that the rule fires when the gap
crosses the upgrade-specific threshold. At the start height (`299_188`)
the current upgrade is Sapling — so the threshold is `900 s`, and the
minimum triggering gap is `901 s`. (The previous version of this theorem
incorrectly claimed `451 s` was enough at the start height, which is wrong:
`451 ≤ 900`, the Sapling threshold.) -/
theorem isTestnetMinDifficultyBlock_above_boundary :
    isTestnetMinDifficultyBlock true TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT 901
      = true := by
  unfold isTestnetMinDifficultyBlock
  rw [minimumDifficultySpacingForHeight_testnet_sapling _ (Nat.le_refl _)
        (by unfold TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT
                  TESTNET_BLOSSOM_ACTIVATION_HEIGHT; decide)]
  decide

/-- **T11a.** Post-Blossom companion of T11: at the Blossom activation height
on Testnet, a gap of `451 s` is enough to trigger the rule (post-Blossom
threshold `450 s`). -/
theorem isTestnetMinDifficultyBlock_above_boundary_blossom :
    isTestnetMinDifficultyBlock true TESTNET_BLOSSOM_ACTIVATION_HEIGHT 451
      = true := by
  unfold isTestnetMinDifficultyBlock
  rw [minimumDifficultySpacingForHeight_testnet_blossom _ (Nat.le_refl _)]
  decide

/-- **T11b.** At a Sapling-era testnet height (`start_height ≤ h < BLOSSOM`),
a gap of `451 s` is **not** enough — this concretely witnesses the bug fixed
in this module (the previous Lean model would have answered `true` here). -/
theorem isTestnetMinDifficultyBlock_sapling_gap_451_false :
    isTestnetMinDifficultyBlock true TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT 451
      = false := by
  unfold isTestnetMinDifficultyBlock
  rw [minimumDifficultySpacingForHeight_testnet_sapling _ (Nat.le_refl _)
        (by unfold TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT
                  TESTNET_BLOSSOM_ACTIVATION_HEIGHT; decide)]
  decide

/-- **T12.** Monotonicity in the time gap: if a smaller gap triggers
min-difficulty, then any larger gap does too. This holds regardless of which
threshold is in force at `height`. -/
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

/-! ## Consistency / cross-region invariants -/

/-- **T13.** The pre-Blossom threshold is strictly larger than the post-Blossom
threshold (`900 > 450`): blocks need a longer dead time during Sapling to
qualify as min-difficulty, because Sapling has 2x the block spacing. -/
theorem pre_gt_post : preBlossomMinDifficultyGap > postBlossomMinDifficultyGap := by
  rw [preBlossomMinDifficultyGap_eq_900, postBlossomMinDifficultyGap_eq_450]
  decide

/-- **T14.** The pre-Blossom threshold is exactly twice the post-Blossom
threshold, matching the `BLOSSOM_POW_TARGET_SPACING_RATIO = 2` invariant. -/
theorem pre_eq_two_mul_post :
    preBlossomMinDifficultyGap = 2 * postBlossomMinDifficultyGap := by
  rw [preBlossomMinDifficultyGap_eq_900, postBlossomMinDifficultyGap_eq_450]
  decide

/-- **T15.** The Sapling region of the testnet min-difficulty rule is
non-empty: `[299_188, 584_000)` contains roughly 285k heights. This pins
down that ignoring the Sapling threshold (as the previous Lean model did) is
a real correctness gap, not a vacuous edge case. -/
theorem sapling_region_size :
    TESTNET_BLOSSOM_ACTIVATION_HEIGHT - TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT
      = 284812 := by
  unfold TESTNET_BLOSSOM_ACTIVATION_HEIGHT TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT
  decide

/-- **T16.** Start height precedes Blossom activation on Testnet, justifying
the two-region split in `thresholdForTestnetHeight`. -/
theorem start_lt_blossom :
    TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT < TESTNET_BLOSSOM_ACTIVATION_HEIGHT := by
  unfold TESTNET_MINIMUM_DIFFICULTY_START_HEIGHT TESTNET_BLOSSOM_ACTIVATION_HEIGHT
  decide

end Zebra.TestnetMinDifficulty
