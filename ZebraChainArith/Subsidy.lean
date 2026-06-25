import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Halving and block subsidy

Models the post-slow-start, post-Blossom-correction core of the Zcash subsidy
schedule from `zebra-chain/src/parameters/network/subsidy.rs`. The mainnet
formula:

  * `halving(h) ≈ (h − Blossom_height) / 840_000 + 1`
    (post-Blossom; pre-Blossom factors are absorbed into the pre-Blossom term)
  * `halving_divisor(h) = 2^halving(h)` if `halving(h) < 64`, else `None`
  * `block_subsidy(h) = MAX_BLOCK_SUBSIDY / halving_divisor(h)`
    (post-slow-start; pre-slow-start has a separate ramp)

We model the halving *index* as a function of height, the divisor as
`Option Nat` (`None` when it overflows u64), and the subsidy as the
floor-division of `MAX_BLOCK_SUBSIDY` by the divisor. Concrete mainnet
constants are baked in.

The grant proposal names this as Phase 5; here we prove the load-bearing
arithmetic facts.
-/

namespace Zebra.Subsidy

/-- Number of zatoshis in 1 ZEC. -/
def COIN : Nat := 100_000_000

/-- The genesis block subsidy: `(25 * COIN) / 2 = 1_250_000_000` zats. -/
def MAX_BLOCK_SUBSIDY : Nat := (25 * COIN) / 2

/-- Mainnet post-Blossom halving interval (blocks). -/
def POST_BLOSSOM_HALVING_INTERVAL : Nat := 840_000

/-- Mainnet Blossom activation height. -/
def BLOSSOM_HEIGHT : Nat := 653_600

/-- u64::MAX: the upper bound on the halving divisor. -/
def U64_MAX : Nat := 18_446_744_073_709_551_615

/-! ## Halving and divisor -/

/-- A simplified post-Blossom halving index: `(h − BLOSSOM_HEIGHT) / interval`,
clamped to 0 below Blossom. The first halving (index 1) happens at the first
`POST_BLOSSOM_HALVING_INTERVAL` after Blossom, and so on. -/
def halving (h : Nat) : Nat :=
  if h < BLOSSOM_HEIGHT then 0
  else (h - BLOSSOM_HEIGHT) / POST_BLOSSOM_HALVING_INTERVAL

/-- `halving_divisor(h)` = `2^halving(h)` if it fits in u64, else `None`. -/
def halvingDivisor (h : Nat) : Option Nat :=
  let k := halving h
  if k < 64 then some (2 ^ k) else none

/-- `block_subsidy(h)` = `MAX_BLOCK_SUBSIDY / halving_divisor(h)`. Returns 0
when the divisor overflows (eventually-zero-subsidy property). -/
def blockSubsidy (h : Nat) : Nat :=
  match halvingDivisor h with
  | none => 0
  | some d => MAX_BLOCK_SUBSIDY / d

/-! ## Theorems -/

/-- **T1 (halving is monotone in height).** -/
theorem halving_monotone (h₁ h₂ : Nat) (hle : h₁ ≤ h₂) :
    halving h₁ ≤ halving h₂ := by
  unfold halving
  split_ifs with h1 h2 h2
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · omega
  · exact Nat.div_le_div_right (by omega)

/-- **T2 (halving is 0 below Blossom).** -/
theorem halving_pre_blossom (h : Nat) (hh : h < BLOSSOM_HEIGHT) : halving h = 0 := by
  unfold halving
  simp [hh]

/-- **T3 (halving is 0 at Blossom activation).** -/
theorem halving_at_blossom : halving BLOSSOM_HEIGHT = 0 := by
  unfold halving
  simp [BLOSSOM_HEIGHT, POST_BLOSSOM_HALVING_INTERVAL]

/-- **T4 (halving is 1 one interval past Blossom).** -/
theorem halving_one_interval_post_blossom :
    halving (BLOSSOM_HEIGHT + POST_BLOSSOM_HALVING_INTERVAL) = 1 := by
  unfold halving
  simp [BLOSSOM_HEIGHT, POST_BLOSSOM_HALVING_INTERVAL]

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
divisor overflows u64 and the subsidy is treated as zero. -/
theorem blockSubsidy_zero_when_overflow (h : Nat) (hk : 64 ≤ halving h) :
    blockSubsidy h = 0 := by
  unfold blockSubsidy
  rw [halvingDivisor_overflow h hk]

/-- **T8 (subsidy at Blossom is `MAX_BLOCK_SUBSIDY`).** Before any halving has
happened. -/
theorem blockSubsidy_at_blossom : blockSubsidy BLOSSOM_HEIGHT = MAX_BLOCK_SUBSIDY := by
  unfold blockSubsidy halvingDivisor halving
  simp [BLOSSOM_HEIGHT, POST_BLOSSOM_HALVING_INTERVAL]

/-- **T9 (subsidy halves at each halving boundary).** One halving interval past
Blossom, the subsidy is `MAX_BLOCK_SUBSIDY / 2`. -/
theorem blockSubsidy_first_halving :
    blockSubsidy (BLOSSOM_HEIGHT + POST_BLOSSOM_HALVING_INTERVAL) =
      MAX_BLOCK_SUBSIDY / 2 := by
  unfold blockSubsidy halvingDivisor
  rw [halving_one_interval_post_blossom]
  simp

/-- **T10 (subsidy is monotone non-increasing in height, no halving overflow).**
Within the range where the divisor fits in u64, the subsidy never increases. -/
theorem blockSubsidy_nonincreasing (h₁ h₂ : Nat) (hle : h₁ ≤ h₂)
    (hk : halving h₂ < 64) :
    blockSubsidy h₂ ≤ blockSubsidy h₁ := by
  unfold blockSubsidy
  have hk1 : halving h₁ < 64 := by
    have := halving_monotone h₁ h₂ hle
    omega
  rw [halvingDivisor_in_range h₁ hk1, halvingDivisor_in_range h₂ hk]
  -- Goal: MAX_BLOCK_SUBSIDY / 2^(halving h₂) ≤ MAX_BLOCK_SUBSIDY / 2^(halving h₁)
  have hpow1 : (0 : Nat) < 2 ^ halving h₁ := Nat.two_pow_pos _
  apply Nat.div_le_div_left
  · exact Nat.pow_le_pow_right (by norm_num) (halving_monotone h₁ h₂ hle)
  · exact hpow1

end Zebra.Subsidy
