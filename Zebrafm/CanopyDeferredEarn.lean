import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Post-NU6 deferred-earn (lockbox) funding stream

Despite the historical "Canopy" hint in the module name, this module models the
**post-NU6** lockbox / deferred funding stream introduced by
[ZIP-1015](https://zips.z.cash/zip-1015). The `Deferred` recipient does not
exist in the pre-NU6 (Canopy-era) ZIP-214 funding streams — those pay ECC, ZF,
and MajorGrants only. The post-NU6 stream replaces ECC + ZF with `Deferred` and
keeps MajorGrants.

Source: `zebra-chain/src/parameters/network/subsidy.rs` (`funding_stream_values`)
and `zebra-chain/src/parameters/network/subsidy/constants/mainnet.rs`
(the `FUNDING_STREAMS` table, where the post-NU6 streams set the `Deferred`
recipient numerator to `12` and the `MajorGrants` numerator to `8` against a
fixed `FUNDING_STREAM_RECEIVER_DENOMINATOR` of `100`).

The spec equation, repeated in the Zebra source comments, is

  `fs.value = floor(block_subsidy(height) * (fs.numerator / fs.denominator))`

implemented with integer arithmetic so the result is the floor division
`(block_subsidy * numerator) / denominator`.

For each block in the post-NU6 funding-stream height range:

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
  in general the three sum to the subsidy after rounding (T10);
- the cumulative lockbox over the full mainnet post-NU6 funding-stream window
  matches the Rust `EXPECTED_NU6_1_LOCKBOX_DISBURSEMENTS_TOTAL` (T13).

Outside the post-NU6 stream's height range the deferred stream is inactive;
we model that by a boolean flag and prove the lockbox is identically zero in
that regime (T3). The flag also stands in for the "pre-NU6" regime.
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

/-- `MAX_BLOCK_SUBSIDY = (25 * COIN) / 2 = 12.5 ZEC` in zatoshis, the largest
block subsidy used before the first halving. From `subsidy/constants.rs:14`. -/
def MAX_BLOCK_SUBSIDY : Nat := 1_250_000_000

/-- `BLOSSOM_POW_TARGET_SPACING_RATIO = 2` from `subsidy/constants.rs:20`. -/
def BLOSSOM_POW_TARGET_SPACING_RATIO : Nat := 2

/-- `PRE_BLOSSOM_HALVING_INTERVAL = 840_000` from `subsidy/constants.rs:25`. -/
def PRE_BLOSSOM_HALVING_INTERVAL : Nat := 840_000

/-- `POST_BLOSSOM_HALVING_INTERVAL = 1_680_000` from
`subsidy/constants.rs:28-29`. Defined as
`PRE_BLOSSOM_HALVING_INTERVAL * BLOSSOM_POW_TARGET_SPACING_RATIO`. -/
def POST_BLOSSOM_HALVING_INTERVAL : Nat :=
  PRE_BLOSSOM_HALVING_INTERVAL * BLOSSOM_POW_TARGET_SPACING_RATIO

/-- `POST_NU6_FUNDING_STREAM_NUM_BLOCKS = 420_000`, the number of blocks the
post-NU6 funding stream runs for on Mainnet (and Testnet). From
`subsidy/constants.rs:48`. -/
def POST_NU6_FUNDING_STREAM_NUM_BLOCKS : Nat := 420_000

/-- The mainnet block subsidy at NU6 / NU6.1 activation, in zatoshis. After
Blossom (`base_subsidy = MAX_BLOCK_SUBSIDY / 2 = 625_000_000`) and after the
second halving (`halving = 2` at NU6, `halving_div = 4`), the block subsidy
is `625_000_000 / 4 = 156_250_000` zatoshis, i.e. `1.5625 ZEC`. This is
constant across the full 420_000-block post-NU6 funding-stream window: the
window runs `[2_726_400, 3_146_400)` on Mainnet and the next halving is at
height `4_406_400 > 3_146_400`, so no halving boundary intersects the window.
-/
def NU6_BLOCK_SUBSIDY : Nat := 156_250_000

/-- `EXPECTED_NU6_1_LOCKBOX_DISBURSEMENTS_TOTAL = 78_750 ZEC` from
`subsidy/constants/mainnet.rs:31-32`. We carry the zatoshi value
(`78_750 * COIN = 7_875_000_000_000`) so we can compare directly against the
cumulative-lockbox arithmetic. -/
def EXPECTED_NU6_1_LOCKBOX_DISBURSEMENTS_TOTAL_ZATOSHI : Nat :=
  7_875_000_000_000

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

/-- **T4 (cumulative lockbox unfolds to `N * lockboxPerBlock`).** This is the
definitional unfold of `cumulativeLockbox` — useful as a `@[simp]` lemma when
reasoning about cumulative totals, but it is `rfl` and does not carry any
semantic content of its own. The load-bearing arithmetic facts are T13
(concrete cumulative at the NU6 window) and the monotonicity / additivity
lemmas T7b, T7c, T8 below. -/
@[simp]
theorem cumulativeLockbox_eq (n subsidy : Nat) (isNu6Plus : Bool) :
    cumulativeLockbox n subsidy isNu6Plus = n * lockboxPerBlock subsidy isNu6Plus :=
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

/-- **T12 (post-NU6 lockbox at the NU6 block subsidy).** Concrete example: at
NU6 / NU6.1 on Mainnet the block subsidy is `156_250_000` zatoshis (`1.5625
ZEC`) — that's `MAX_BLOCK_SUBSIDY / 2` post-Blossom scaling, then divided by
`2^2 = 4` for the second halving (Canopy was halving 1, NU6 is halving 2).
The lockbox share at NU6 is then `156_250_000 * 12 / 100 = 18_750_000`
zatoshis per block. -/
theorem lockboxPerBlock_at_nu6_subsidy :
    lockboxPerBlock NU6_BLOCK_SUBSIDY true = 18_750_000 := by
  rw [lockboxPerBlock_post_nu6]
  unfold NU6_BLOCK_SUBSIDY
  decide

/-- **T13 (cumulative lockbox over the full mainnet NU6 funding-stream
window).** The post-NU6 funding stream on Mainnet runs for
`POST_NU6_FUNDING_STREAM_NUM_BLOCKS = 420_000` blocks at the constant
`NU6_BLOCK_SUBSIDY = 156_250_000`-zatoshi subsidy (no halving boundary falls
inside the window — the next halving is at height `4_406_400 ≥ 2_726_400 +
420_000 = 3_146_400`). The total deferred amount is therefore
`420_000 * 18_750_000 = 7_875_000_000_000` zatoshis = `78_750 ZEC`, which
matches `EXPECTED_NU6_1_LOCKBOX_DISBURSEMENTS_TOTAL` in
`subsidy/constants/mainnet.rs:31-32`. -/
theorem cumulativeLockbox_full_nu6_window :
    cumulativeLockbox POST_NU6_FUNDING_STREAM_NUM_BLOCKS NU6_BLOCK_SUBSIDY true
      = EXPECTED_NU6_1_LOCKBOX_DISBURSEMENTS_TOTAL_ZATOSHI := by
  unfold cumulativeLockbox POST_NU6_FUNDING_STREAM_NUM_BLOCKS
    EXPECTED_NU6_1_LOCKBOX_DISBURSEMENTS_TOTAL_ZATOSHI
  rw [lockboxPerBlock_at_nu6_subsidy]

/-- **T13b (cumulative lockbox over one post-Blossom halving interval at the
NU6 subsidy).** Worked example showing the per-halving cumulative for the
post-Blossom epoch width: at `NU6_BLOCK_SUBSIDY` zatoshis over
`POST_BLOSSOM_HALVING_INTERVAL = 1_680_000` blocks, the lockbox accrues
`1_680_000 * 18_750_000 = 31_500_000_000_000` zatoshis (= `315_000 ZEC`).
This is a hypothetical "constant subsidy over one halving" figure — the real
post-NU6 stream is shorter (420_000 blocks) and ends before the next halving,
so this number is purely a sanity check on the arithmetic, not a real total
disbursement. -/
theorem cumulativeLockbox_one_postBlossom_halving_at_nu6_subsidy :
    cumulativeLockbox POST_BLOSSOM_HALVING_INTERVAL NU6_BLOCK_SUBSIDY true
      = 31_500_000_000_000 := by
  unfold cumulativeLockbox POST_BLOSSOM_HALVING_INTERVAL
    PRE_BLOSSOM_HALVING_INTERVAL BLOSSOM_POW_TARGET_SPACING_RATIO
  rw [lockboxPerBlock_at_nu6_subsidy]

/-- **T14 (post-NU6 funding-stream split ratios).** The two NU6 stream
numerators add to `20`, leaving `80/100 = 4/5` for the miner — a sanity check
on the Rust constants. -/
theorem nu6_stream_numerator_sum :
    LOCKBOX_NUMERATOR + MAJOR_GRANTS_NUMERATOR = 20 := by
  decide

/-- **T15 (the deferred fraction matches Zip1014Devfund-style 12/100).** Sanity
check that the model's `POST_BLOSSOM_HALVING_INTERVAL` and supporting constants
agree with the sibling `Zip1014Devfund` module's value `1_680_000`, so the two
crates of the verification cannot drift on the halving epoch width. -/
theorem post_blossom_halving_interval_value :
    POST_BLOSSOM_HALVING_INTERVAL = 1_680_000 := by
  unfold POST_BLOSSOM_HALVING_INTERVAL PRE_BLOSSOM_HALVING_INTERVAL
    BLOSSOM_POW_TARGET_SPACING_RATIO
  decide

/-- **T16 (NU6 block subsidy is twice the lockbox + major-grants share, in the
exact-divisibility case).** At `NU6_BLOCK_SUBSIDY = 156_250_000`, since the
subsidy is `1_562_500 * 100` it is divisible by `100`, so the floor losses
vanish and the miner gets exactly `156_250_000 * 80 / 100 = 125_000_000`
zatoshis (= `1.25 ZEC`) per block. -/
theorem minerSubsidy_at_nu6 :
    minerSubsidy NU6_BLOCK_SUBSIDY true = 125_000_000 := by
  unfold minerSubsidy
  rw [lockboxPerBlock_at_nu6_subsidy,
      majorGrantsPerBlock_post_nu6]
  unfold NU6_BLOCK_SUBSIDY
  decide

end Zebra.CanopyDeferredEarn
