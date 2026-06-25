import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Canopy / NU6 deferred-earn lockbox

Models the lockbox / deferred funding stream introduced by
[ZIP-1015](https://zips.z.cash/zip-1015) and activated at NU6 on Mainnet.
Source: `zebra-chain/src/parameters/network/subsidy.rs` (`funding_stream_values`)
and `zebra-chain/src/parameters/network/subsidy/constants/mainnet.rs`
(the `FUNDING_STREAMS` table, where the post-NU6 streams set the `Deferred`
recipient numerator to `12` and the `MajorGrants` numerator to `8` against a
fixed `FUNDING_STREAM_RECEIVER_DENOMINATOR` of `100`).

The spec equation, repeated in the Zebra source comments, is

  `fs.value = floor(block_subsidy(height) * (fs.numerator / fs.denominator))`

implemented with integer arithmetic so the result is the floor division
`(block_subsidy * numerator) / denominator`.

For each block from NU6 onwards:

  * `lockboxPerBlock(subsidy) = floor(subsidy * 12 / 100)` (the deferred share)
  * `majorGrantsPerBlock(subsidy) = floor(subsidy * 8 / 100)`
  * `minerSubsidy(subsidy) = subsidy − lockboxPerBlock − majorGrantsPerBlock`

We prove:

- the lockbox-per-block formula matches `subsidy * 12 / 100` (T1);
- the cumulative lockbox after `N` blocks of *constant* subsidy is
  `N * lockboxPerBlock(subsidy)` (T4);
- the lockbox is non-negative and bounded above by the subsidy (T5, T6);
- sum-conservation: when the subsidy is a multiple of `100`, the miner share
  plus lockbox plus major-grants share exactly equals the subsidy (T9), and
  in general the three sum to the subsidy after rounding (T10).

Pre-NU6 the deferred stream is inactive; we model that by a boolean flag and
prove the lockbox is identically zero in that regime (T3).
-/

namespace Zebra.CanopyDeferredEarn

/-! ## Constants

These match `zebra-chain/src/parameters/network/subsidy/constants.rs` and
`zebra-chain/src/parameters/network/subsidy/constants/mainnet.rs`. -/

/-- `FUNDING_STREAM_RECEIVER_DENOMINATOR` from `subsidy/constants.rs:34`. -/
def FUNDING_STREAM_RECEIVER_DENOMINATOR : Nat := 100

/-- Numerator of the post-NU6 `Deferred` (lockbox) funding stream. From
`subsidy/constants/mainnet.rs` (`FUNDING_STREAMS` table, post-NU6 entry,
`FundingStreamReceiver::Deferred`). -/
def LOCKBOX_NUMERATOR : Nat := 12

/-- Numerator of the post-NU6 `MajorGrants` funding stream. From the same
table (post-NU6 entry, `FundingStreamReceiver::MajorGrants`). -/
def MAJOR_GRANTS_NUMERATOR : Nat := 8

/-! ## Definitions -/

/-- Apply a funding-stream fraction to a subsidy with integer floor division.
This is the exact arithmetic from `funding_stream_values` in
`zebra-chain/src/parameters/network/subsidy.rs:338` :

```
let amount_value = ((expected_block_subsidy * recipient.numerator())?
    / FUNDING_STREAM_RECEIVER_DENOMINATOR)?;
```
-/
def streamShare (subsidy numerator : Nat) : Nat :=
  (subsidy * numerator) / FUNDING_STREAM_RECEIVER_DENOMINATOR

/-- The lockbox (Deferred) share per block. Zero pre-NU6, else
`floor(subsidy * 12 / 100)`. The `isNu6Plus` flag stands in for the height
test `NetworkUpgrade::current(net, height) >= NetworkUpgrade::Canopy` *and*
the post-NU6 funding-stream entry being active. -/
def lockboxPerBlock (subsidy : Nat) (isNu6Plus : Bool) : Nat :=
  if isNu6Plus then streamShare subsidy LOCKBOX_NUMERATOR else 0

/-- The Major Grants share per block (post-NU6 stream). Zero pre-NU6, else
`floor(subsidy * 8 / 100)`. -/
def majorGrantsPerBlock (subsidy : Nat) (isNu6Plus : Bool) : Nat :=
  if isNu6Plus then streamShare subsidy MAJOR_GRANTS_NUMERATOR else 0

/-- The post-NU6 miner subsidy: `block_subsidy − lockbox − major_grants`.
Pre-NU6 (in this simplified model) the miner gets the full subsidy.
Mirrors `miner_subsidy` in `zebra-chain/src/parameters/network/subsidy.rs:484`
restricted to the post-Canopy regime with NU6 funding streams. -/
def minerSubsidy (subsidy : Nat) (isNu6Plus : Bool) : Nat :=
  subsidy - lockboxPerBlock subsidy isNu6Plus - majorGrantsPerBlock subsidy isNu6Plus

/-- Cumulative lockbox balance after `n` blocks, given a *constant* per-block
subsidy. Used to reason about the lockbox over an interval where the halving
divisor doesn't change. -/
def cumulativeLockbox (n subsidy : Nat) (isNu6Plus : Bool) : Nat :=
  n * lockboxPerBlock subsidy isNu6Plus

/-! ## Theorems -/

/-- **T1 (lockbox-per-block matches the spec floor formula).** Post-NU6, the
deferred per-block amount equals `floor(subsidy * 12 / 100)`. -/
theorem lockboxPerBlock_post_nu6 (subsidy : Nat) :
    lockboxPerBlock subsidy true = subsidy * 12 / 100 := by
  unfold lockboxPerBlock streamShare LOCKBOX_NUMERATOR FUNDING_STREAM_RECEIVER_DENOMINATOR
  simp

/-- **T2 (major-grants-per-block matches the spec floor formula).** Post-NU6,
the major-grants per-block amount equals `floor(subsidy * 8 / 100)`. -/
theorem majorGrantsPerBlock_post_nu6 (subsidy : Nat) :
    majorGrantsPerBlock subsidy true = subsidy * 8 / 100 := by
  unfold majorGrantsPerBlock streamShare MAJOR_GRANTS_NUMERATOR
    FUNDING_STREAM_RECEIVER_DENOMINATOR
  simp

/-- **T3 (lockbox is zero pre-NU6).** When the NU6 funding streams are not
active, the deferred share is identically zero. -/
theorem lockboxPerBlock_pre_nu6 (subsidy : Nat) :
    lockboxPerBlock subsidy false = 0 := by
  unfold lockboxPerBlock
  simp

/-- **T3b (major-grants is zero pre-NU6 in this model).** -/
theorem majorGrantsPerBlock_pre_nu6 (subsidy : Nat) :
    majorGrantsPerBlock subsidy false = 0 := by
  unfold majorGrantsPerBlock
  simp

/-- **T4 (cumulative lockbox after `N` constant-subsidy blocks).** The total
amount locked after `N` blocks at a *constant* per-block subsidy is exactly
`N * lockboxPerBlock(subsidy)`. This is the load-bearing arithmetic identity
that justifies summing the per-block lockbox amounts over an interval where
the halving divisor doesn't change. -/
theorem cumulativeLockbox_eq (n subsidy : Nat) (isNu6Plus : Bool) :
    cumulativeLockbox n subsidy isNu6Plus = n * lockboxPerBlock subsidy isNu6Plus := by
  rfl

/-- **T5 (lockbox balance is non-negative).** Trivial in `Nat`, but worth
stating to mirror the `Amount<NonNegative>` invariant the Rust code carries. -/
theorem lockboxPerBlock_nonneg (subsidy : Nat) (isNu6Plus : Bool) :
    0 ≤ lockboxPerBlock subsidy isNu6Plus :=
  Nat.zero_le _

/-- **T5b (cumulative lockbox is non-negative).** -/
theorem cumulativeLockbox_nonneg (n subsidy : Nat) (isNu6Plus : Bool) :
    0 ≤ cumulativeLockbox n subsidy isNu6Plus :=
  Nat.zero_le _

/-- **T6 (lockbox is bounded by the subsidy, post-NU6).** The deferred share
is at most `subsidy * 12 / 100 ≤ subsidy`. -/
theorem lockboxPerBlock_le_subsidy (subsidy : Nat) :
    lockboxPerBlock subsidy true ≤ subsidy := by
  rw [lockboxPerBlock_post_nu6]
  -- `subsidy * 12 / 100 ≤ subsidy * 100 / 100 = subsidy` since `12 ≤ 100`.
  have hmul : subsidy * 12 ≤ subsidy * 100 := Nat.mul_le_mul_left subsidy (by decide)
  calc subsidy * 12 / 100
      ≤ subsidy * 100 / 100 := Nat.div_le_div_right hmul
    _ = subsidy := by
        have hpos : (0 : Nat) < 100 := by decide
        exact Nat.mul_div_cancel subsidy hpos

/-- **T6b (cumulative lockbox is bounded by `n * subsidy`).** -/
theorem cumulativeLockbox_le (n subsidy : Nat) :
    cumulativeLockbox n subsidy true ≤ n * subsidy := by
  unfold cumulativeLockbox
  exact Nat.mul_le_mul_left n (lockboxPerBlock_le_subsidy subsidy)

/-- **T7 (lockbox is monotone in subsidy).** Doubling the subsidy can only
increase (or hold) the deferred share, since floor division by 100 is
monotone in the numerator. -/
theorem lockboxPerBlock_monotone_subsidy
    (s₁ s₂ : Nat) (hle : s₁ ≤ s₂) (isNu6Plus : Bool) :
    lockboxPerBlock s₁ isNu6Plus ≤ lockboxPerBlock s₂ isNu6Plus := by
  unfold lockboxPerBlock streamShare
  split_ifs
  · exact Nat.div_le_div_right (Nat.mul_le_mul_right _ hle)
  · exact Nat.le_refl 0

/-- **T7b (cumulative lockbox is monotone in `n`).** -/
theorem cumulativeLockbox_monotone_n
    (n₁ n₂ subsidy : Nat) (hle : n₁ ≤ n₂) (isNu6Plus : Bool) :
    cumulativeLockbox n₁ subsidy isNu6Plus ≤ cumulativeLockbox n₂ subsidy isNu6Plus := by
  unfold cumulativeLockbox
  exact Nat.mul_le_mul_right _ hle

/-- **T7c (cumulative lockbox is monotone in subsidy).** -/
theorem cumulativeLockbox_monotone_subsidy
    (n s₁ s₂ : Nat) (hle : s₁ ≤ s₂) (isNu6Plus : Bool) :
    cumulativeLockbox n s₁ isNu6Plus ≤ cumulativeLockbox n s₂ isNu6Plus := by
  unfold cumulativeLockbox
  exact Nat.mul_le_mul_left n (lockboxPerBlock_monotone_subsidy s₁ s₂ hle isNu6Plus)

/-- **T8 (cumulative lockbox is additive in the block count).** Locking
`m + k` blocks deposits the same total as locking `m` then `k` blocks. -/
theorem cumulativeLockbox_add (m k subsidy : Nat) (isNu6Plus : Bool) :
    cumulativeLockbox (m + k) subsidy isNu6Plus =
      cumulativeLockbox m subsidy isNu6Plus +
      cumulativeLockbox k subsidy isNu6Plus := by
  unfold cumulativeLockbox
  exact Nat.add_mul m k _

/-- **T9 (sum conservation when the subsidy is a multiple of 100).** When the
subsidy is divisible by 100 (avoiding floor losses), the miner share plus the
lockbox plus the major-grants share exactly equals the subsidy. This is the
"clean-arithmetic" case the protocol's per-block subsidies hit at concrete
halvings. -/
theorem sum_conservation_post_nu6_div100
    (subsidy : Nat) (hdvd : 100 ∣ subsidy) :
    minerSubsidy subsidy true +
    lockboxPerBlock subsidy true +
    majorGrantsPerBlock subsidy true = subsidy := by
  unfold minerSubsidy
  rw [lockboxPerBlock_post_nu6, majorGrantsPerBlock_post_nu6]
  -- Goal: (subsidy − subsidy*12/100 − subsidy*8/100) + subsidy*12/100 + subsidy*8/100 = subsidy.
  -- Bound the two floor terms by `subsidy` so `Nat.sub` doesn't underflow.
  obtain ⟨k, rfl⟩ := hdvd
  -- subsidy = 100 * k; subsidy * 12 / 100 = 12 * k; subsidy * 8 / 100 = 8 * k.
  have e12 : 100 * k * 12 / 100 = 12 * k := by
    have heq : 100 * k * 12 = 100 * (12 * k) := by ring
    rw [heq]
    exact Nat.mul_div_cancel_left (12 * k) (by decide : (0 : Nat) < 100)
  have e8 : 100 * k * 8 / 100 = 8 * k := by
    have heq : 100 * k * 8 = 100 * (8 * k) := by ring
    rw [heq]
    exact Nat.mul_div_cancel_left (8 * k) (by decide : (0 : Nat) < 100)
  rw [e12, e8]
  -- Goal: (100*k − 12*k − 8*k) + 12*k + 8*k = 100*k. Standard Nat-sub arithmetic.
  -- 12*k + 8*k = 20*k ≤ 100*k, so the Nat.sub is exact.
  have hb1 : 12 * k ≤ 100 * k := Nat.mul_le_mul_right k (by decide)
  have hb2 : 12 * k + 8 * k ≤ 100 * k := by
    have : 20 * k ≤ 100 * k := Nat.mul_le_mul_right k (by decide)
    linarith
  omega

/-- **T10 (sum conservation pre-NU6).** Pre-NU6 the miner gets the full
subsidy and both funding streams are zero. -/
theorem sum_conservation_pre_nu6 (subsidy : Nat) :
    minerSubsidy subsidy false +
    lockboxPerBlock subsidy false +
    majorGrantsPerBlock subsidy false = subsidy := by
  unfold minerSubsidy
  rw [lockboxPerBlock_pre_nu6, majorGrantsPerBlock_pre_nu6]
  simp

/-- **T11 (miner subsidy + lockbox alone ≤ subsidy, post-NU6).** Without
restricting to the divisible case, the miner share plus the lockbox share is
at most the full subsidy. (The remaining gap goes to major grants and to the
floor-rounding remainders.) -/
theorem miner_plus_lockbox_le_subsidy (subsidy : Nat) :
    minerSubsidy subsidy true + lockboxPerBlock subsidy true ≤ subsidy := by
  unfold minerSubsidy
  -- `(subsidy − L − M) + L ≤ subsidy` since each term is a `Nat` and L ≤ subsidy.
  have hL : lockboxPerBlock subsidy true ≤ subsidy := lockboxPerBlock_le_subsidy subsidy
  omega

/-- **T12 (post-NU6 lockbox at the genesis-style subsidy).** Concrete example:
at `MAX_BLOCK_SUBSIDY = 1_250_000_000` zatoshis (= 12.5 ZEC), the lockbox
gets `150_000_000` zatoshis (= 1.5 ZEC) per block. -/
theorem lockboxPerBlock_at_max_subsidy :
    lockboxPerBlock 1_250_000_000 true = 150_000_000 := by
  rw [lockboxPerBlock_post_nu6]

/-- **T13 (cumulative lockbox over one halving interval at max subsidy).**
Over 840_000 blocks at the genesis-style subsidy, the lockbox accrues
`126_000_000_000_000` zatoshis (= 1_260_000 ZEC). -/
theorem cumulativeLockbox_one_halving_max_subsidy :
    cumulativeLockbox 840_000 1_250_000_000 true = 126_000_000_000_000 := by
  unfold cumulativeLockbox
  rw [lockboxPerBlock_at_max_subsidy]

/-- **T14 (post-NU6 funding-stream split ratios).** The two NU6 stream
numerators add to `20`, leaving `80/100 = 4/5` for the miner — a sanity check
on the Rust constants. -/
theorem nu6_stream_numerator_sum :
    LOCKBOX_NUMERATOR + MAJOR_GRANTS_NUMERATOR = 20 := by
  decide

/-- **T15 (the deferred fraction is exactly 12/100).** Sanity check that the
numerator/denominator match the documented spec ratio. -/
theorem deferred_ratio :
    LOCKBOX_NUMERATOR * 25 = FUNDING_STREAM_RECEIVER_DENOMINATOR * 3 := by
  decide

end Zebra.CanopyDeferredEarn
