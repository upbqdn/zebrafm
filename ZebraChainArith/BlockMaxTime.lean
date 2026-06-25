import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Block max-time tolerance from the Zcash consensus rules

The Zcash consensus rules require that a block's `header.time` be no more than
`MAX_BLOCK_TIME_TOLERANCE = 7200` seconds (two hours) in the future relative
to the validator's local clock:

  `block_time ≤ now + MAX_BLOCK_TIME_TOLERANCE`

This is the standard "future block time" bound shared with Bitcoin
(consensus.h `nMaxFutureBlockTime`). Zebra's parameter machinery for related
time-gap checks lives under `zebra-chain/src/parameters/network_upgrade.rs`
(see `is_max_block_time_enforced` and friends), and the constants for related
limits live in `zebra-chain/src/parameters/constants.rs`.

We model times as `Nat` second counts (Unix epoch seconds) and the predicate
as a simple linear inequality.
-/

namespace Zebra.BlockMaxTime

/-- Maximum allowed gap, in seconds, between the local clock and a block's
declared `header.time`. Spec value: 7200 s = 2 hours.
Source: Zcash consensus rules (Bitcoin-derived `MaxFutureBlockTime`),
referenced from `zebra-chain/src/parameters/network_upgrade.rs:464`
(`is_testnet_min_difficulty_block` / surrounding `block_time` rules) and the
constants in `zebra-chain/src/parameters/constants.rs`. -/
def MAX_BLOCK_TIME_TOLERANCE : Nat := 7200

/-- The predicate: `block_time` is acceptable iff it is no more than
`MAX_BLOCK_TIME_TOLERANCE` seconds beyond `now`. Note that we permit
block-times in the *past* (no lower bound from this rule).
Source: Zcash consensus rules; corresponds to the Bitcoin
`block.GetBlockTime() <= GetAdjustedTime() + MAX_FUTURE_BLOCK_TIME` check
adopted by Zcash. -/
def isAcceptable (blockTime now : Nat) : Bool :=
  decide (blockTime ≤ now + MAX_BLOCK_TIME_TOLERANCE)

/-- The largest acceptable `block_time` given the current `now`. -/
def maxAcceptable (now : Nat) : Nat := now + MAX_BLOCK_TIME_TOLERANCE

/-! ## Theorems -/

/-- **T1.** `MAX_BLOCK_TIME_TOLERANCE` is exactly two hours of seconds. -/
theorem tolerance_value : MAX_BLOCK_TIME_TOLERANCE = 2 * 60 * 60 := by
  unfold MAX_BLOCK_TIME_TOLERANCE; decide

/-- **T2.** Acceptance is exactly the linear inequality
`block_time ≤ now + MAX_BLOCK_TIME_TOLERANCE`. -/
theorem isAcceptable_iff (blockTime now : Nat) :
    isAcceptable blockTime now = true ↔
      blockTime ≤ now + MAX_BLOCK_TIME_TOLERANCE := by
  unfold isAcceptable
  exact decide_eq_true_iff

/-- **T3.** The current local time `now` is always acceptable as a block time
(no future skew). -/
theorem now_is_acceptable (now : Nat) : isAcceptable now now = true := by
  rw [isAcceptable_iff]; omega

/-- **T4.** Any block time in the past is acceptable. -/
theorem past_is_acceptable (blockTime now : Nat) (h : blockTime ≤ now) :
    isAcceptable blockTime now = true := by
  rw [isAcceptable_iff]; omega

/-- **T5.** The boundary value `now + MAX_BLOCK_TIME_TOLERANCE` is acceptable
(the inequality is non-strict). -/
theorem boundary_is_acceptable (now : Nat) :
    isAcceptable (now + MAX_BLOCK_TIME_TOLERANCE) now = true := by
  rw [isAcceptable_iff]

/-- **T6.** One second past the boundary is rejected. -/
theorem just_past_boundary_rejected (now : Nat) :
    isAcceptable (now + MAX_BLOCK_TIME_TOLERANCE + 1) now = false := by
  unfold isAcceptable
  simp

/-- **T7.** Monotonicity in `now`: if a block time is acceptable at `now₁`
and `now₁ ≤ now₂`, it is still acceptable at the later `now₂`. -/
theorem acceptable_mono_now (blockTime now₁ now₂ : Nat)
    (h12 : now₁ ≤ now₂) (h : isAcceptable blockTime now₁ = true) :
    isAcceptable blockTime now₂ = true := by
  rw [isAcceptable_iff] at h ⊢
  omega

/-- **T8.** Anti-monotonicity in `blockTime`: if a later block time is
acceptable, then any earlier block time is also acceptable. -/
theorem acceptable_antimono_blockTime (bt₁ bt₂ now : Nat)
    (h12 : bt₁ ≤ bt₂) (h : isAcceptable bt₂ now = true) :
    isAcceptable bt₁ now = true := by
  rw [isAcceptable_iff] at h ⊢
  omega

/-- **T9.** `maxAcceptable now` is itself acceptable. -/
theorem maxAcceptable_acceptable (now : Nat) :
    isAcceptable (maxAcceptable now) now = true := by
  unfold maxAcceptable
  exact boundary_is_acceptable now

/-- **T10.** `maxAcceptable` is the *least upper bound*: any acceptable
`blockTime` is `≤ maxAcceptable now`. -/
theorem maxAcceptable_is_upper_bound (blockTime now : Nat)
    (h : isAcceptable blockTime now = true) :
    blockTime ≤ maxAcceptable now := by
  rw [isAcceptable_iff] at h
  unfold maxAcceptable
  exact h

/-- **T11.** Tightness of the bound: a strictly larger `blockTime` than
`maxAcceptable now` is rejected. -/
theorem above_maxAcceptable_rejected (blockTime now : Nat)
    (h : blockTime > maxAcceptable now) :
    isAcceptable blockTime now = false := by
  unfold isAcceptable maxAcceptable at *
  simp only [decide_eq_false_iff_not, not_le]
  exact h

/-- **T12.** `maxAcceptable` is monotone in `now`. -/
theorem maxAcceptable_mono (now₁ now₂ : Nat) (h : now₁ ≤ now₂) :
    maxAcceptable now₁ ≤ maxAcceptable now₂ := by
  unfold maxAcceptable; omega

end Zebra.BlockMaxTime
