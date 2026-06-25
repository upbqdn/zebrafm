import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Founders reward

Models the founders-reward split of the Zcash block subsidy, as it existed
from genesis through (but not including) Canopy activation. Source:
`zebra-chain/src/parameters/network/subsidy.rs` (function `founders_reward`,
lines 539-552), which implements `FoundersReward(height)` from protocol
spec §7.8.

The Rust rule (`subsidy.rs:545-551`) is:

```rust
if halving(height, net) < 1 && NetworkUpgrade::current(net, height) < NetworkUpgrade::Canopy {
    block_subsidy(height, net)
        .map(|subsidy| subsidy.div_exact(5))
        .expect("block subsidy must be valid for founders rewards")
} else {
    Amount::zero()
}
```

Two guards are combined with `&&`: `halving < 1` *and* the current upgrade is
before Canopy. On mainnet these are equivalent (Canopy activates at the first
halving), but on custom testnets the first halving can land later than Canopy
and the spec guards against that inconsistency by checking both.

`div_exact(5)` is *not* silent floor division: it panics if `subsidy % 5 ≠ 0`
(`amount.rs:79-86`). The protocol guarantees `block_subsidy(h) ≡ 0 (mod 5)`
in the founders window, so this never fires on real chains, but a Lean model
that pretends `subsidy / 5` is the same is hiding a real precondition. We
model `div_exact` as `Option`-valued, returning `none` on non-divisibility.

This module establishes:
  * an honest, `Option`-valued `divExact5` mirroring Rust's panicking
    `div_exact`;
  * a single Boolean activation guard `foundersActive` parameterised by both
    `halvingLt1` and `preCanopy` (so the model preserves the `&&` structure);
  * `foundersReward (subsidy, halvingLt1, preCanopy) : Option Nat`, which is
    `none` when active and the subsidy is not divisible by 5 (i.e. the Rust
    code would panic), `some 0` when inactive, and `some (subsidy / 5)` when
    active and divisible;
  * `minerReward`, which uses ordinary subtraction once the founders share is
    known and `subsidy ≥ founders` (which is automatic from divisibility);
  * sum-conservation modulo the activation guard and divisibility hypothesis;
  * concrete vectors against `MAX_BLOCK_SUBSIDY = 1_250_000_000` and the
    post-Blossom-halved `MAX_BLOCK_SUBSIDY / 2 = 625_000_000` (the post-Blossom
    base subsidy used for the founders window from Blossom up to Canopy on
    mainnet).
-/

namespace Zebra.FoundersReward

/-- `FOUNDERS_REWARD_NUMERATOR`: numerator of the founders-reward fraction.
Source: `subsidy.rs:540` (comment "20% of the block subsidy"). -/
def FOUNDERS_REWARD_NUMERATOR : Nat := 20

/-- `FOUNDERS_REWARD_DENOMINATOR`: denominator of the founders-reward
fraction. -/
def FOUNDERS_REWARD_DENOMINATOR : Nat := 100

/-- The simplified ratio `FOUNDERS_REWARD_DENOMINATOR / FOUNDERS_REWARD_NUMERATOR = 5`.
This is the literal divisor used by `subsidy.div_exact(5)` in
`subsidy.rs:547`. -/
def FOUNDERS_DIVISOR : Nat := FOUNDERS_REWARD_DENOMINATOR / FOUNDERS_REWARD_NUMERATOR

/-! ## Mirror of `Amount::div_exact`

Rust's `div_exact(self, rhs)` (`amount.rs:79-86`) divides only when the
dividend is a multiple of `rhs`, and panics otherwise. We use
`Option`-valued division to capture the same partiality. -/

/-- `divExact5 n` = `some (n / 5)` when `5 ∣ n`, else `none`. Mirrors the
panicking semantics of `Amount::div_exact(self, 5)` in Rust
(`amount.rs:79-86`): the Rust call panics on the `none` branch, so any code
path that gets there is buggy. -/
def divExact5 (n : Nat) : Option Nat :=
  if n % 5 = 0 then some (n / 5) else none

/-! ## Activation guard

The Rust condition (`subsidy.rs:545`) is:

```rust
halving(height, net) < 1 && NetworkUpgrade::current(net, height) < NetworkUpgrade::Canopy
```

The two conjuncts agree on mainnet but can disagree on custom testnets where
Canopy activates before the first halving; the conjunction enforces the
stricter "both must hold" semantics. We expose both as parameters and AND
them, so callers can't accidentally collapse the guard.

Sources: the comment in `subsidy.rs:540-544` explains the conjunction. -/

/-- The founders reward is active iff `halving(height, net) < 1` *and* the
current network upgrade is strictly before Canopy. Both are required: this
preserves the `&&` structure of the Rust condition. -/
def foundersActive (halvingLt1 preCanopy : Bool) : Bool := halvingLt1 && preCanopy

/-! ## Founders / miner reward

We model rewards as `Option Nat`: `none` represents the Rust panic on a
non-divisible subsidy, `some k` represents a successful pay-out of `k`
zatoshis. -/

/-- `FoundersReward(height)` modelled as `Option Nat`. When inactive,
the founders share is `some 0`. When active, it is `divExact5 subsidy`, so
`none` whenever `5 ∤ subsidy` (capturing the Rust `expect` panic).
Source: `subsidy.rs:539-552`. -/
def foundersReward (subsidy : Nat) (halvingLt1 preCanopy : Bool) : Option Nat :=
  if foundersActive halvingLt1 preCanopy then divExact5 subsidy else some 0

/-- `MinerSubsidy(height)` modelled as `Option Nat`. When the founders share
is `none` (Rust would have panicked), the miner share is also `none`.
Otherwise the miner gets `subsidy - founders_share`.
Source: `subsidy.rs:484-496` (`miner_subsidy`), restricted to the no-funding-
streams pre-Canopy window. -/
def minerReward (subsidy : Nat) (halvingLt1 preCanopy : Bool) : Option Nat :=
  (foundersReward subsidy halvingLt1 preCanopy).map (fun f => subsidy - f)

/-! ## Concrete-value lemmas -/

/-- **T1 (the simplified divisor is 5).** `100 / 20 = 5`. -/
theorem founders_divisor_eq_five : FOUNDERS_DIVISOR = 5 := by
  decide

/-- **T2 (founders-reward fraction is 20%).** The numerator over the
denominator is `1 / 5`: i.e. `5 * NUMERATOR = DENOMINATOR`. -/
theorem founders_ratio_one_fifth :
    5 * FOUNDERS_REWARD_NUMERATOR = FOUNDERS_REWARD_DENOMINATOR := by
  decide

/-! ## `divExact5` lemmas -/

/-- **T3 (`divExact5` agrees with floor division on multiples of 5).** -/
theorem divExact5_dvd (n : Nat) (h : 5 ∣ n) :
    divExact5 n = some (n / 5) := by
  unfold divExact5
  rw [Nat.dvd_iff_mod_eq_zero] at h
  simp [h]

/-- **T4 (`divExact5` is `none` on non-multiples of 5).** Captures the Rust
panic site of `Amount::div_exact`. -/
theorem divExact5_not_dvd (n : Nat) (h : ¬ 5 ∣ n) :
    divExact5 n = none := by
  unfold divExact5
  rw [Nat.dvd_iff_mod_eq_zero] at h
  simp [h]

/-- **T5 (`divExact5` round-trip).** When `5 ∣ n`, the unwrapped value
multiplied by 5 recovers `n`. -/
theorem divExact5_round_trip (n : Nat) (h : 5 ∣ n) :
    ∀ q, divExact5 n = some q → 5 * q = n := by
  intro q hq
  rw [divExact5_dvd n h] at hq
  injection hq with hq
  rw [← hq, Nat.mul_comm]
  exact Nat.div_mul_cancel h

/-! ## Founders-reward shape theorems -/

/-- **T6 (founders reward is `some 0` post-Canopy).** Once Canopy is active
(`preCanopy = false`) the founders reward is `some 0`, for any subsidy and
any value of `halvingLt1`. Mirrors `subsidy.rs:549-551` returning
`Amount::zero()`. -/
theorem foundersReward_post_canopy
    (subsidy : Nat) (halvingLt1 : Bool) :
    foundersReward subsidy halvingLt1 false = some 0 := by
  unfold foundersReward foundersActive
  simp

/-- **T7 (founders reward is `some 0` once halving ≥ 1).** When
`halvingLt1 = false` the founders reward is `some 0`, for any subsidy and
any value of `preCanopy`. This is the other half of the double-guard. -/
theorem foundersReward_post_halving
    (subsidy : Nat) (preCanopy : Bool) :
    foundersReward subsidy false preCanopy = some 0 := by
  unfold foundersReward foundersActive
  simp

/-- **T8 (miner gets full subsidy post-Canopy).** -/
theorem minerReward_post_canopy
    (subsidy : Nat) (halvingLt1 : Bool) :
    minerReward subsidy halvingLt1 false = some subsidy := by
  unfold minerReward
  rw [foundersReward_post_canopy]
  simp

/-- **T9 (miner gets full subsidy post-halving).** -/
theorem minerReward_post_halving
    (subsidy : Nat) (preCanopy : Bool) :
    minerReward subsidy false preCanopy = some subsidy := by
  unfold minerReward
  rw [foundersReward_post_halving]
  simp

/-- **T10 (founders reward formula when active and divisible).** -/
theorem foundersReward_active_dvd
    (subsidy : Nat) (h : 5 ∣ subsidy) :
    foundersReward subsidy true true = some (subsidy / 5) := by
  unfold foundersReward foundersActive
  simp only [Bool.and_self, if_true]
  exact divExact5_dvd subsidy h

/-- **T11 (founders reward is `none` when active and `5 ∤ subsidy`).**
This is the Lean witness of the Rust panic at `subsidy.rs:548`: any code
path that reaches the active branch with a non-divisible subsidy is calling
`Amount::div_exact(5)` on a non-multiple of 5, which panics. -/
theorem foundersReward_active_panic
    (subsidy : Nat) (h : ¬ 5 ∣ subsidy) :
    foundersReward subsidy true true = none := by
  unfold foundersReward foundersActive
  simp only [Bool.and_self, if_true]
  exact divExact5_not_dvd subsidy h

/-! ## Conservation -/

/-- **T12 (sum conservation when active and divisible).** Modelling
`Amount::div_exact` honestly: when active, the protocol guarantees `5 ∣
subsidy`, and then `minerReward + foundersReward = subsidy` exactly. -/
theorem sum_conservation_active
    (subsidy : Nat) (h : 5 ∣ subsidy) :
    ∃ m f, minerReward subsidy true true = some m ∧
           foundersReward subsidy true true = some f ∧
           m + f = subsidy := by
  refine ⟨subsidy - subsidy / 5, subsidy / 5, ?_, ?_, ?_⟩
  · unfold minerReward
    rw [foundersReward_active_dvd subsidy h]
    simp
  · exact foundersReward_active_dvd subsidy h
  · have hle : subsidy / 5 ≤ subsidy := Nat.div_le_self subsidy 5
    omega

/-- **T13 (sum conservation post-Canopy).** No divisibility needed. -/
theorem sum_conservation_post_canopy
    (subsidy : Nat) (halvingLt1 : Bool) :
    ∃ m f, minerReward subsidy halvingLt1 false = some m ∧
           foundersReward subsidy halvingLt1 false = some f ∧
           m + f = subsidy := by
  refine ⟨subsidy, 0, ?_, ?_, ?_⟩
  · exact minerReward_post_canopy subsidy halvingLt1
  · exact foundersReward_post_canopy subsidy halvingLt1
  · exact Nat.add_zero subsidy

/-- **T14 (sum conservation post-halving).** Symmetric to T13 but using the
`halvingLt1 = false` half of the guard. -/
theorem sum_conservation_post_halving
    (subsidy : Nat) (preCanopy : Bool) :
    ∃ m f, minerReward subsidy false preCanopy = some m ∧
           foundersReward subsidy false preCanopy = some f ∧
           m + f = subsidy := by
  refine ⟨subsidy, 0, ?_, ?_, ?_⟩
  · exact minerReward_post_halving subsidy preCanopy
  · exact foundersReward_post_halving subsidy preCanopy
  · exact Nat.add_zero subsidy

/-! ## Bounds and monotonicity -/

/-- **T15 (founders reward is bounded by 1/5 of subsidy).** Floor division
never exceeds the true quotient: whenever the founders reward is defined as
`some f`, we have `5 * f ≤ subsidy`. -/
theorem foundersReward_le_fifth
    (subsidy : Nat) (halvingLt1 preCanopy : Bool) (f : Nat)
    (hf : foundersReward subsidy halvingLt1 preCanopy = some f) :
    5 * f ≤ subsidy := by
  unfold foundersReward foundersActive at hf
  split_ifs at hf with hact
  · -- Active branch: `hf : divExact5 subsidy = some f`.
    unfold divExact5 at hf
    split_ifs at hf with hmod
    -- Only the divisible sub-branch survives (the `none = some f` is
    -- already absurd and discharged by `split_ifs`).
    injection hf with hf
    rw [← hf]
    have := Nat.div_mul_le_self subsidy 5
    omega
  · -- Inactive branch: `hf : some 0 = some f`, so `f = 0`.
    injection hf with hf
    rw [← hf]
    simp

/-- **T16 (founders reward is at most the subsidy).** -/
theorem foundersReward_le_subsidy
    (subsidy : Nat) (halvingLt1 preCanopy : Bool) (f : Nat)
    (hf : foundersReward subsidy halvingLt1 preCanopy = some f) :
    f ≤ subsidy := by
  have h := foundersReward_le_fifth subsidy halvingLt1 preCanopy f hf
  omega

/-- **T17 (founders reward is monotone in subsidy, holding the activation
flags fixed).** A larger subsidy never gives a smaller founders reward,
when both are divisible by 5 (the case the protocol guarantees). -/
theorem foundersReward_monotone_subsidy
    (s₁ s₂ : Nat) (hle : s₁ ≤ s₂)
    (h1 : 5 ∣ s₁) (h2 : 5 ∣ s₂)
    (halvingLt1 preCanopy : Bool)
    (f₁ f₂ : Nat)
    (hf1 : foundersReward s₁ halvingLt1 preCanopy = some f₁)
    (hf2 : foundersReward s₂ halvingLt1 preCanopy = some f₂) :
    f₁ ≤ f₂ := by
  unfold foundersReward foundersActive at hf1 hf2
  split_ifs at hf1 hf2 with hact
  · -- Both active and divisible: f_i = s_i / 5.
    rw [divExact5_dvd s₁ h1] at hf1
    rw [divExact5_dvd s₂ h2] at hf2
    injection hf1 with hf1
    injection hf2 with hf2
    rw [← hf1, ← hf2]
    exact Nat.div_le_div_right hle
  · -- Both inactive: f_i = 0.
    injection hf1 with hf1
    injection hf2 with hf2
    rw [← hf1, ← hf2]

/-- **T18 (miner reward is monotone in subsidy when active and both
divisible).** When both subsidies are multiples of 5, raising the subsidy
raises the miner's take. -/
theorem minerReward_monotone_active
    (s₁ s₂ : Nat) (hle : s₁ ≤ s₂)
    (h1 : 5 ∣ s₁) (h2 : 5 ∣ s₂)
    (m₁ m₂ : Nat)
    (hm1 : minerReward s₁ true true = some m₁)
    (hm2 : minerReward s₂ true true = some m₂) :
    m₁ ≤ m₂ := by
  unfold minerReward at hm1 hm2
  rw [foundersReward_active_dvd s₁ h1] at hm1
  rw [foundersReward_active_dvd s₂ h2] at hm2
  rw [Option.map_some] at hm1 hm2
  injection hm1 with hm1
  injection hm2 with hm2
  obtain ⟨k₁, rfl⟩ := h1
  obtain ⟨k₂, rfl⟩ := h2
  have e1 : 5 * k₁ / 5 = k₁ := by omega
  have e2 : 5 * k₂ / 5 = k₂ := by omega
  rw [e1] at hm1
  rw [e2] at hm2
  -- m₁ = 5 * k₁ - k₁ = 4 * k₁; m₂ = 4 * k₂; k₁ ≤ k₂.
  have hk : k₁ ≤ k₂ := by omega
  omega

/-- **T19 (miner reward is `4/5` of subsidy, active and divisible).**
Concrete characterization of the split. -/
theorem minerReward_active_four_fifths
    (subsidy : Nat) (h : 5 ∣ subsidy) (m : Nat)
    (hm : minerReward subsidy true true = some m) :
    5 * m = 4 * subsidy := by
  unfold minerReward at hm
  rw [foundersReward_active_dvd subsidy h] at hm
  rw [Option.map_some] at hm
  injection hm with hm
  obtain ⟨k, rfl⟩ := h
  have e : 5 * k / 5 = k := by omega
  rw [e] at hm
  -- m = 5 * k - k = 4 * k; goal: 5 * (5 * k - k) = 4 * (5 * k).
  omega

/-! ## Concrete examples against the genesis subsidy

Source: `subsidy/constants.rs:14` — `MAX_BLOCK_SUBSIDY = (25 * COIN) / 2 =
1_250_000_000` zatoshis. This is the founders-window subsidy on mainnet
before Blossom, which is the regime the founders reward applies to. -/

/-- **T20 (concrete example: founders share of pre-Blossom max subsidy).**
The pre-Blossom max subsidy is `1_250_000_000` zatoshis; the founders'
share is `250_000_000` (= 2.5 ZEC), one-fifth of the block subsidy. -/
theorem foundersReward_at_pre_blossom_subsidy :
    foundersReward 1_250_000_000 true true = some 250_000_000 := by
  rw [foundersReward_active_dvd 1_250_000_000 (by decide : (5 : Nat) ∣ 1_250_000_000)]

/-- **T21 (concrete example: miner share of pre-Blossom max subsidy).**
Miner gets `1_000_000_000` zatoshis (= 10 ZEC) out of the 12.5 ZEC
pre-Blossom max subsidy. -/
theorem minerReward_at_pre_blossom_subsidy :
    minerReward 1_250_000_000 true true = some 1_000_000_000 := by
  unfold minerReward
  rw [foundersReward_at_pre_blossom_subsidy]
  rfl

/-- **T22 (concrete example: founders share of post-Blossom base subsidy).**
After Blossom on mainnet (and still before Canopy) the base subsidy is
`MAX_BLOCK_SUBSIDY / 2 = 625_000_000` zatoshis; the founders' share is
`125_000_000` (= 1.25 ZEC). -/
theorem foundersReward_at_post_blossom_subsidy :
    foundersReward 625_000_000 true true = some 125_000_000 := by
  rw [foundersReward_active_dvd 625_000_000 (by decide : (5 : Nat) ∣ 625_000_000)]

/-- **T23 (concrete example: miner share of post-Blossom base subsidy).**
Miner gets `500_000_000` zatoshis (= 5 ZEC). -/
theorem minerReward_at_post_blossom_subsidy :
    minerReward 625_000_000 true true = some 500_000_000 := by
  unfold minerReward
  rw [foundersReward_at_post_blossom_subsidy]
  rfl

/-! ## Double-guard interaction

These theorems exhibit that the `&&` between `halvingLt1` and `preCanopy`
is load-bearing: either alone disables the founders reward. -/

/-- **T24 (only one guard active is not enough).** If only `halvingLt1` is
true and `preCanopy` is false, the founders reward is still `some 0`. -/
theorem foundersReward_halving_but_post_canopy
    (subsidy : Nat) :
    foundersReward subsidy true false = some 0 :=
  foundersReward_post_canopy subsidy true

/-- **T25 (other one-guard case).** If only `preCanopy` is true and
`halvingLt1` is false, the founders reward is still `some 0`. -/
theorem foundersReward_canopy_but_post_halving
    (subsidy : Nat) :
    foundersReward subsidy false true = some 0 :=
  foundersReward_post_halving subsidy true

end Zebra.FoundersReward
