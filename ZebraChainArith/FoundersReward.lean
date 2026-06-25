import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Founders reward

Models the founders-reward split of the Zcash block subsidy, as it existed
from genesis through (but not including) Canopy activation. Source:
`zebra-chain/src/parameters/network/subsidy.rs` (function `founders_reward`),
which implements `FoundersReward(height)` from protocol spec §7.8.

The rule is: for heights below Canopy *and* before the first halving, the
founders receive `FOUNDERS_REWARD_NUMERATOR / FOUNDERS_REWARD_DENOMINATOR =
20 / 100 = 1/5` of the block subsidy, and the rest goes to the miner. After
Canopy (or after the first halving on weird testnets), the founders reward
is zero and the full subsidy goes to the miner.

In Rust the implementation uses `subsidy.div_exact(5)`, taking advantage of
the fact that the pre-Canopy subsidy values are all divisible by 5. We model
both the `floor(subsidy / 5)` form (faithful to integer arithmetic) and the
exact (`5 ∣ subsidy`) form, and prove sum-conservation:

  `minerReward(subsidy, height) + foundersReward(subsidy, height) = subsidy`

whenever the subsidy is divisible by 5 (the case that the protocol guarantees).
-/

namespace Zebra.FoundersReward

/-- `FOUNDERS_REWARD_NUMERATOR`: numerator of the founders-reward fraction. -/
def FOUNDERS_REWARD_NUMERATOR : Nat := 20

/-- `FOUNDERS_REWARD_DENOMINATOR`: denominator of the founders-reward fraction. -/
def FOUNDERS_REWARD_DENOMINATOR : Nat := 100

/-- The simplified ratio `FOUNDERS_REWARD_DENOMINATOR / FOUNDERS_REWARD_NUMERATOR = 5`.
This is the divisor used by `subsidy.div_exact(5)` in the Rust code. -/
def FOUNDERS_DIVISOR : Nat := FOUNDERS_REWARD_DENOMINATOR / FOUNDERS_REWARD_NUMERATOR

/-- Whether the founders reward is active at this height. In Rust this is the
condition `halving(height, net) < 1 && current(net, height) < Canopy`. We
abstract both bits into a single Boolean. -/
def foundersActive (preCanopy : Bool) : Bool := preCanopy

/-- `FoundersReward(height)` = `block_subsidy(height) / 5` when active, else `0`.
Source: `zebra-chain/src/parameters/network/subsidy.rs:539` (`founders_reward`). -/
def foundersReward (subsidy : Nat) (preCanopy : Bool) : Nat :=
  if foundersActive preCanopy then subsidy / FOUNDERS_DIVISOR else 0

/-- `MinerSubsidy(height)` = `block_subsidy − founders_reward − funding_streams`.
We model the (pre-Canopy, no-funding-streams) form: miner gets whatever the
founders don't.
Source: `zebra-chain/src/parameters/network/subsidy.rs:484` (`miner_subsidy`). -/
def minerReward (subsidy : Nat) (preCanopy : Bool) : Nat :=
  subsidy - foundersReward subsidy preCanopy

/-! ## Theorems -/

/-- **T1 (the simplified divisor is 5).** `100 / 20 = 5`. -/
theorem founders_divisor_eq_five : FOUNDERS_DIVISOR = 5 := by
  decide

/-- **T2 (founders-reward fraction is 20%).** The numerator over the
denominator is `1 / 5`: i.e. `5 * NUMERATOR = DENOMINATOR`. -/
theorem founders_ratio_one_fifth :
    5 * FOUNDERS_REWARD_NUMERATOR = FOUNDERS_REWARD_DENOMINATOR := by
  decide

/-- **T3 (founders reward is zero post-Canopy).** Once Canopy is active the
founders reward is identically zero, for any subsidy. -/
theorem foundersReward_post_canopy (subsidy : Nat) :
    foundersReward subsidy false = 0 := by
  unfold foundersReward foundersActive
  simp

/-- **T4 (miner gets full subsidy post-Canopy).** -/
theorem minerReward_post_canopy (subsidy : Nat) :
    minerReward subsidy false = subsidy := by
  unfold minerReward
  rw [foundersReward_post_canopy]
  exact Nat.sub_zero subsidy

/-- **T5 (founders reward formula pre-Canopy).** -/
theorem foundersReward_pre_canopy (subsidy : Nat) :
    foundersReward subsidy true = subsidy / 5 := by
  unfold foundersReward foundersActive FOUNDERS_DIVISOR
    FOUNDERS_REWARD_DENOMINATOR FOUNDERS_REWARD_NUMERATOR
  simp

/-- **T6 (founders reward is bounded by 1/5 of subsidy).** Floor division
never exceeds the true quotient. -/
theorem foundersReward_le_fifth (subsidy : Nat) (preCanopy : Bool) :
    5 * foundersReward subsidy preCanopy ≤ subsidy := by
  unfold foundersReward foundersActive FOUNDERS_DIVISOR
    FOUNDERS_REWARD_DENOMINATOR FOUNDERS_REWARD_NUMERATOR
  split_ifs with h
  · -- Goal: 5 * (subsidy / (100/20)) ≤ subsidy; reduce 100/20 to 5 first.
    change 5 * (subsidy / 5) ≤ subsidy
    have := Nat.div_mul_le_self subsidy 5
    linarith
  · simp

/-- **T7 (founders reward is at most the subsidy).** -/
theorem foundersReward_le_subsidy (subsidy : Nat) (preCanopy : Bool) :
    foundersReward subsidy preCanopy ≤ subsidy := by
  have h := foundersReward_le_fifth subsidy preCanopy
  have : foundersReward subsidy preCanopy ≤ 5 * foundersReward subsidy preCanopy := by
    have : 1 * foundersReward subsidy preCanopy ≤ 5 * foundersReward subsidy preCanopy := by
      exact Nat.mul_le_mul_right _ (by decide)
    simpa using this
  omega

/-- **T8 (sum conservation when subsidy is divisible by 5, pre-Canopy).** The
miner reward plus the founders reward equals the block subsidy, exactly, when
the subsidy is divisible by 5 — which the protocol guarantees pre-Canopy
(`div_exact(5)` in Rust). -/
theorem sum_conservation_pre_canopy (subsidy : Nat) (hdvd : 5 ∣ subsidy) :
    minerReward subsidy true + foundersReward subsidy true = subsidy := by
  unfold minerReward
  rw [foundersReward_pre_canopy]
  -- Goal: (subsidy - subsidy / 5) + subsidy / 5 = subsidy
  have h : subsidy / 5 ≤ subsidy := Nat.div_le_self subsidy 5
  omega

/-- **T9 (sum conservation post-Canopy, no divisibility needed).** -/
theorem sum_conservation_post_canopy (subsidy : Nat) :
    minerReward subsidy false + foundersReward subsidy false = subsidy := by
  rw [minerReward_post_canopy, foundersReward_post_canopy]
  exact Nat.add_zero subsidy

/-- **T10 (founders reward is monotone in subsidy).** A larger subsidy never
gives a smaller founders reward, holding the activation flag fixed. -/
theorem foundersReward_monotone_subsidy
    (s₁ s₂ : Nat) (hle : s₁ ≤ s₂) (preCanopy : Bool) :
    foundersReward s₁ preCanopy ≤ foundersReward s₂ preCanopy := by
  unfold foundersReward
  split_ifs
  · exact Nat.div_le_div_right hle
  · exact Nat.le_refl 0

/-- **T11 (miner reward is monotone in subsidy, pre-Canopy with divisibility)**.
When both subsidies are multiples of 5, raising the subsidy raises the miner's
take. (Without divisibility, floor effects in the founders reward can make this
fail by 1 in pathological cases; protocol always gives multiples of 5.) -/
theorem minerReward_monotone_pre_canopy
    (s₁ s₂ : Nat) (hle : s₁ ≤ s₂) (h1 : 5 ∣ s₁) (h2 : 5 ∣ s₂) :
    minerReward s₁ true ≤ minerReward s₂ true := by
  unfold minerReward
  rw [foundersReward_pre_canopy, foundersReward_pre_canopy]
  -- Need: s₁ - s₁/5 ≤ s₂ - s₂/5
  -- Since 5 ∣ s₁ and 5 ∣ s₂, write sᵢ = 5 * kᵢ; then sᵢ - sᵢ/5 = 4 * kᵢ.
  obtain ⟨k₁, rfl⟩ := h1
  obtain ⟨k₂, rfl⟩ := h2
  -- After rfl-rewrites sᵢ becomes `5 * kᵢ`; simplify the divisions via omega.
  have e1 : 5 * k₁ / 5 = k₁ := by omega
  have e2 : 5 * k₂ / 5 = k₂ := by omega
  rw [e1, e2]
  have hk : k₁ ≤ k₂ := by omega
  omega

/-- **T12 (miner reward is 4/5 of subsidy, pre-Canopy, when divisible by 5).**
Concrete characterization of the split. -/
theorem minerReward_pre_canopy_div5 (subsidy : Nat) (h : 5 ∣ subsidy) :
    5 * minerReward subsidy true = 4 * subsidy := by
  unfold minerReward
  rw [foundersReward_pre_canopy]
  obtain ⟨k, rfl⟩ := h
  have e : 5 * k / 5 = k := by omega
  rw [e]
  -- Goal: 5 * (5 * k - k) = 4 * (5 * k); linear identity over Nat.
  omega

/-- **T13 (concrete example: founders share of `MAX_BLOCK_SUBSIDY`).** The
genesis subsidy is `1_250_000_000` zatoshis; the founders' share is
`250_000_000` (= 2.5 ZEC). -/
theorem foundersReward_at_genesis_subsidy :
    foundersReward 1_250_000_000 true = 250_000_000 := by
  rw [foundersReward_pre_canopy]

/-- **T14 (concrete example: miner share of `MAX_BLOCK_SUBSIDY`).** Miner gets
`1_000_000_000` zatoshis (= 10 ZEC) out of the 12.5 ZEC genesis subsidy. -/
theorem minerReward_at_genesis_subsidy :
    minerReward 1_250_000_000 true = 1_000_000_000 := by
  unfold minerReward
  rw [foundersReward_at_genesis_subsidy]

end Zebra.FoundersReward
