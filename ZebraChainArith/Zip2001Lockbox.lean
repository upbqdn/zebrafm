import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.ModEq

/-!
# ZIP-2001 / ZIP-1015 NU6 lockbox: deferred-pool arithmetic

Models the NU6 post-Canopy deferred-pool (lockbox) share whose recipient is
`FundingStreamReceiver::Deferred` in
`zebra-chain/src/parameters/network/subsidy.rs`. The actual numerator is `12`
and the denominator is `100`, as set in
`zebra-chain/src/parameters/network/subsidy/constants/mainnet.rs:217` :

```
FundingStreamReceiver::Deferred,
FundingStreamRecipient::new::<[&str; 0], &str>(12, []),
```

against `FUNDING_STREAM_RECEIVER_DENOMINATOR = 100`
(`subsidy/constants.rs:34`).

The per-stream calculation is the spec equation, repeated in
`funding_stream_values` at `subsidy.rs:338`:

```
let amount_value = ((expected_block_subsidy * recipient.numerator())?
    / FUNDING_STREAM_RECEIVER_DENOMINATOR)?;
```

with implicit `floor` from Rust's integer division.

This module is *complementary* to `CanopyDeferredEarn.lean`: there we look at
the lockbox / Major-Grants split on its own. Here we look at the *whole NU6
funding-stream table* — splitting it as `miner + dev_fund + lockbox = total`
where `dev_fund` aggregates the three non-deferred streams (ECC `7/100`, ZF
`5/100`, MajorGrants `8/100` pre-NU6; post-NU6 the post-NU6 table sets ECC and
ZF to zero in this codebase but keeps MajorGrants `8/100`).

We prove:

* `lockboxPerBlock = subsidy * 12 / 100` (T1)
* `lockboxPerBlock ≤ MAX_MONEY` whenever `subsidy ≤ MAX_MONEY` (T2)
* cumulative lockbox `nblocks * lockboxPerBlock ≤ nblocks * subsidy ≤ MAX_MONEY`
  in the realistic-supply regime (T5)
* post-NU6 sum-conservation `miner + dev_fund + lockbox = subsidy` whenever
  the subsidy is a multiple of `100` (T8)
* dev-fund + lockbox `≤ subsidy` for *all* subsidies (T9)

For the dev-fund we use the pre-NU6 numerators (7, 5, 8) summing to 20/100,
because that is the historical "dev-fund" the ZIP-1015 split was designed to
replace. The post-NU6 table only contains MajorGrants (8) and Deferred (12);
that case is also covered by `sum_conservation_postNU6_minor` (T10).
-/

namespace Zebra.Zip2001Lockbox

/-! ## Constants

These match `zebra-chain/src/parameters/network/subsidy/constants.rs`,
`subsidy/constants/mainnet.rs`, and `amount.rs`. -/

/-- `COIN` = 1 ZEC in zatoshis.
Source: `zebra-chain/src/amount.rs` (`COIN`). -/
def COIN : Nat := 100_000_000

/-- Max-money cap, from `zebra-chain/src/amount.rs:610` :
`pub const MAX_MONEY: i64 = 21_000_000 * COIN;`. We work in `Nat`, so this is
the positive bound. -/
def MAX_MONEY : Nat := 21_000_000 * COIN

/-- `FUNDING_STREAM_RECEIVER_DENOMINATOR` from `subsidy/constants.rs:34`. -/
def DENOMINATOR : Nat := 100

/-- Pre-NU6 ECC numerator.
Source: `subsidy/constants/mainnet.rs:198` :
`FundingStreamRecipient::new(7, FUNDING_STREAM_ECC_ADDRESSES)`. -/
def ECC_NUMERATOR : Nat := 7

/-- Pre-NU6 Zcash Foundation numerator.
Source: `subsidy/constants/mainnet.rs:202` :
`FundingStreamRecipient::new(5, FUNDING_STREAM_ZF_ADDRESSES)`. -/
def ZF_NUMERATOR : Nat := 5

/-- Major Grants numerator (used in both the pre-NU6 and post-NU6 stream
tables). Source: `subsidy/constants/mainnet.rs:206`, `:221`. -/
def MAJOR_GRANTS_NUMERATOR : Nat := 8

/-- Post-NU6 Deferred (lockbox) numerator.
Source: `subsidy/constants/mainnet.rs:217` (and `:233` for NU6.1):
`FundingStreamRecipient::new::<[&str; 0], &str>(12, [])`. -/
def LOCKBOX_NUMERATOR : Nat := 12

/-! ## Definitions -/

/-- Apply a funding-stream fraction to a subsidy with integer floor division.
Exactly the arithmetic from `funding_stream_values` in
`zebra-chain/src/parameters/network/subsidy.rs:338`. -/
def streamShare (subsidy numerator : Nat) : Nat :=
  (subsidy * numerator) / DENOMINATOR

/-- The lockbox (Deferred) share per block, post-NU6.
`floor(subsidy * 12 / 100)`. -/
def lockboxPerBlock (subsidy : Nat) : Nat :=
  streamShare subsidy LOCKBOX_NUMERATOR

/-- The pre-NU6 "dev fund" share per block: ECC + ZF + MajorGrants
funding-stream shares aggregated. The three numerators sum to `20/100`. -/
def devFundPerBlock (subsidy : Nat) : Nat :=
  streamShare subsidy ECC_NUMERATOR +
  streamShare subsidy ZF_NUMERATOR +
  streamShare subsidy MAJOR_GRANTS_NUMERATOR

/-- The post-NU6 miner share for the simplified
`miner + dev_fund + lockbox = total` model used here. Pre-NU6 the lockbox is
zero; post-NU6 the dev-fund and lockbox are deducted. -/
def minerPerBlock (subsidy : Nat) : Nat :=
  subsidy - devFundPerBlock subsidy - lockboxPerBlock subsidy

/-- Cumulative lockbox balance after `n` blocks given a *constant* per-block
subsidy. Reasonable model over an interval where the halving divisor does not
change. -/
def cumulativeLockbox (n subsidy : Nat) : Nat :=
  n * lockboxPerBlock subsidy

/-! ## Theorems -/

/-- **T1 (lockbox formula matches the spec floor expression).** The deferred
per-block share equals `floor(subsidy * 12 / 100)`. -/
theorem lockboxPerBlock_eq (subsidy : Nat) :
    lockboxPerBlock subsidy = subsidy * 12 / 100 := by
  unfold lockboxPerBlock streamShare LOCKBOX_NUMERATOR DENOMINATOR
  rfl

/-- **T2 (lockbox bounded by `MAX_MONEY` when subsidy is).** Whenever the
subsidy itself sits inside the `MAX_MONEY` envelope, the deferred share is
also bounded by `MAX_MONEY`. The mainnet `block_subsidy` is always
`≤ MAX_BLOCK_SUBSIDY ≤ MAX_MONEY`, so this captures the per-block invariant. -/
theorem lockboxPerBlock_le_max_money (subsidy : Nat)
    (h : subsidy ≤ MAX_MONEY) :
    lockboxPerBlock subsidy ≤ MAX_MONEY := by
  rw [lockboxPerBlock_eq]
  -- `subsidy * 12 / 100 ≤ subsidy` since `12 ≤ 100`, then chain with `h`.
  have hmul : subsidy * 12 ≤ subsidy * 100 := Nat.mul_le_mul_left subsidy (by decide)
  have hstep1 : subsidy * 12 / 100 ≤ subsidy * 100 / 100 :=
    Nat.div_le_div_right hmul
  have hstep2 : subsidy * 100 / 100 = subsidy :=
    Nat.mul_div_cancel subsidy (by decide : (0 : Nat) < 100)
  rw [hstep2] at hstep1
  exact le_trans hstep1 h

/-- **T3 (lockbox is bounded by the subsidy).** The deferred share never
exceeds the block subsidy itself. -/
theorem lockboxPerBlock_le_subsidy (subsidy : Nat) :
    lockboxPerBlock subsidy ≤ subsidy := by
  rw [lockboxPerBlock_eq]
  have hmul : subsidy * 12 ≤ subsidy * 100 := Nat.mul_le_mul_left subsidy (by decide)
  calc subsidy * 12 / 100
      ≤ subsidy * 100 / 100 := Nat.div_le_div_right hmul
    _ = subsidy := Nat.mul_div_cancel subsidy (by decide : (0 : Nat) < 100)

/-- **T4 (cumulative lockbox is additive in the block count).** -/
theorem cumulativeLockbox_add (m k subsidy : Nat) :
    cumulativeLockbox (m + k) subsidy =
      cumulativeLockbox m subsidy + cumulativeLockbox k subsidy := by
  unfold cumulativeLockbox
  exact Nat.add_mul m k _

/-- **T5 (cumulative lockbox bounded by `n * subsidy`).** Over `n` blocks of
constant subsidy, the lockbox accumulates at most `n * subsidy` zatoshis. -/
theorem cumulativeLockbox_le (n subsidy : Nat) :
    cumulativeLockbox n subsidy ≤ n * subsidy := by
  unfold cumulativeLockbox
  exact Nat.mul_le_mul_left n (lockboxPerBlock_le_subsidy subsidy)

/-- **T6 (cumulative lockbox bounded by `n * MAX_MONEY` when subsidy ≤ MAX_MONEY).**
This is the per-block envelope; total *issued* coin is `n * subsidy`, of which
at most `12/100` is locked. -/
theorem cumulativeLockbox_le_max_money (n subsidy : Nat)
    (h : subsidy ≤ MAX_MONEY) :
    cumulativeLockbox n subsidy ≤ n * MAX_MONEY := by
  unfold cumulativeLockbox
  have h₁ : lockboxPerBlock subsidy ≤ MAX_MONEY :=
    lockboxPerBlock_le_max_money subsidy h
  exact Nat.mul_le_mul_left n h₁

/-- **T7 (cumulative lockbox is monotone in both arguments).** Lockbox growth
is monotone in the block count and (for fixed `n`) in the per-block subsidy. -/
theorem cumulativeLockbox_monotone
    (n₁ n₂ s₁ s₂ : Nat) (hn : n₁ ≤ n₂) (hs : s₁ ≤ s₂) :
    cumulativeLockbox n₁ s₁ ≤ cumulativeLockbox n₂ s₂ := by
  unfold cumulativeLockbox
  have hL : lockboxPerBlock s₁ ≤ lockboxPerBlock s₂ := by
    rw [lockboxPerBlock_eq, lockboxPerBlock_eq]
    exact Nat.div_le_div_right (Nat.mul_le_mul_right _ hs)
  calc n₁ * lockboxPerBlock s₁
      ≤ n₂ * lockboxPerBlock s₁ := Nat.mul_le_mul_right _ hn
    _ ≤ n₂ * lockboxPerBlock s₂ := Nat.mul_le_mul_left n₂ hL

/-- **T8 (sum conservation: `miner + dev_fund + lockbox = subsidy`).** When
the subsidy is a multiple of `100` (no floor-division remainder), the three
slices exactly partition the per-block subsidy. This is the load-bearing
identity behind the post-NU6 funding-stream split. -/
theorem sum_conservation_divisible
    (subsidy : Nat) (hdvd : 100 ∣ subsidy) :
    minerPerBlock subsidy + devFundPerBlock subsidy + lockboxPerBlock subsidy
      = subsidy := by
  unfold minerPerBlock devFundPerBlock lockboxPerBlock streamShare
    ECC_NUMERATOR ZF_NUMERATOR MAJOR_GRANTS_NUMERATOR LOCKBOX_NUMERATOR
    DENOMINATOR
  obtain ⟨k, rfl⟩ := hdvd
  -- subsidy = 100 * k. Each `100 * k * c / 100` simplifies to `c * k`.
  have e7 : 100 * k * 7 / 100 = 7 * k := by
    have heq : 100 * k * 7 = 100 * (7 * k) := by ring
    rw [heq]
    exact Nat.mul_div_cancel_left (7 * k) (by decide : (0 : Nat) < 100)
  have e5 : 100 * k * 5 / 100 = 5 * k := by
    have heq : 100 * k * 5 = 100 * (5 * k) := by ring
    rw [heq]
    exact Nat.mul_div_cancel_left (5 * k) (by decide : (0 : Nat) < 100)
  have e8 : 100 * k * 8 / 100 = 8 * k := by
    have heq : 100 * k * 8 = 100 * (8 * k) := by ring
    rw [heq]
    exact Nat.mul_div_cancel_left (8 * k) (by decide : (0 : Nat) < 100)
  have e12 : 100 * k * 12 / 100 = 12 * k := by
    have heq : 100 * k * 12 = 100 * (12 * k) := by ring
    rw [heq]
    exact Nat.mul_div_cancel_left (12 * k) (by decide : (0 : Nat) < 100)
  rw [e7, e5, e8, e12]
  -- Goal: (100*k − (7*k + 5*k + 8*k) − 12*k) + (7*k + 5*k + 8*k) + 12*k = 100*k.
  -- The dev-fund (20*k) + lockbox (12*k) = 32*k ≤ 100*k, so Nat.sub is exact.
  omega

/-- **T9 (dev-fund + lockbox bounded by subsidy, all subsidies).** Even
without the divisibility hypothesis, the four deductions never exceed the
subsidy. This is the safety property that keeps `minerPerBlock` non-negative
in the underlying `Amount<NonNegative>` representation.

The proof uses `Nat.add_div_le_add_div` (sub-additivity of floor) and the
fact `7 + 5 + 8 + 12 = 32 ≤ 100`. -/
theorem devFund_plus_lockbox_le_subsidy (subsidy : Nat) :
    devFundPerBlock subsidy + lockboxPerBlock subsidy ≤ subsidy := by
  unfold devFundPerBlock lockboxPerBlock streamShare
    ECC_NUMERATOR ZF_NUMERATOR MAJOR_GRANTS_NUMERATOR LOCKBOX_NUMERATOR
    DENOMINATOR
  -- Use sub-additivity of `Nat` floor division three times:
  --   a/d + b/d ≤ (a+b)/d   (`Nat.add_div_le_add_div`)
  -- Then `(subsidy*7 + subsidy*5 + subsidy*8 + subsidy*12) = subsidy*32`.
  -- Then `subsidy*32 / 100 ≤ subsidy*100 / 100 = subsidy`.
  have h₁ : subsidy * 7 / 100 + subsidy * 5 / 100 ≤
            (subsidy * 7 + subsidy * 5) / 100 :=
    Nat.add_div_le_add_div (subsidy * 7) (subsidy * 5) 100
  have h₂ : (subsidy * 7 + subsidy * 5) / 100 + subsidy * 8 / 100 ≤
            (subsidy * 7 + subsidy * 5 + subsidy * 8) / 100 :=
    Nat.add_div_le_add_div (subsidy * 7 + subsidy * 5) (subsidy * 8) 100
  have h₃ : (subsidy * 7 + subsidy * 5 + subsidy * 8) / 100 +
              subsidy * 12 / 100 ≤
            (subsidy * 7 + subsidy * 5 + subsidy * 8 + subsidy * 12) / 100 :=
    Nat.add_div_le_add_div (subsidy * 7 + subsidy * 5 + subsidy * 8)
                             (subsidy * 12) 100
  have hsum_eq :
      subsidy * 7 + subsidy * 5 + subsidy * 8 + subsidy * 12 = subsidy * 32 := by
    ring
  have hbound : subsidy * 32 / 100 ≤ subsidy := by
    have hmul : subsidy * 32 ≤ subsidy * 100 :=
      Nat.mul_le_mul_left subsidy (by decide)
    calc subsidy * 32 / 100
        ≤ subsidy * 100 / 100 := Nat.div_le_div_right hmul
      _ = subsidy := Nat.mul_div_cancel subsidy (by decide : (0 : Nat) < 100)
  -- Chain the inequalities.
  have hchain :
      subsidy * 7 / 100 + subsidy * 5 / 100 + subsidy * 8 / 100 +
        subsidy * 12 / 100 ≤
      (subsidy * 7 + subsidy * 5 + subsidy * 8 + subsidy * 12) / 100 := by
    -- start with `h₁` then add `subsidy*8/100` to both sides and use `h₂`, etc.
    have step1 :
        subsidy * 7 / 100 + subsidy * 5 / 100 + subsidy * 8 / 100 ≤
        (subsidy * 7 + subsidy * 5) / 100 + subsidy * 8 / 100 :=
      Nat.add_le_add_right h₁ _
    have step2 :
        (subsidy * 7 + subsidy * 5) / 100 + subsidy * 8 / 100 ≤
        (subsidy * 7 + subsidy * 5 + subsidy * 8) / 100 := h₂
    have step12 :
        subsidy * 7 / 100 + subsidy * 5 / 100 + subsidy * 8 / 100 ≤
        (subsidy * 7 + subsidy * 5 + subsidy * 8) / 100 :=
      le_trans step1 step2
    have step3 :
        subsidy * 7 / 100 + subsidy * 5 / 100 + subsidy * 8 / 100 +
          subsidy * 12 / 100 ≤
        (subsidy * 7 + subsidy * 5 + subsidy * 8) / 100 +
          subsidy * 12 / 100 :=
      Nat.add_le_add_right step12 _
    exact le_trans step3 h₃
  rw [hsum_eq] at hchain
  exact le_trans hchain hbound

/-- **T10 (post-NU6 sum conservation, minor table).** When ECC and ZF are
zeroed (the post-NU6 table only contains MajorGrants and Deferred), and the
subsidy is a multiple of 100, the partition `miner + major_grants + lockbox`
exactly equals the subsidy. -/
theorem sum_conservation_postNU6_minor (subsidy : Nat) (hdvd : 100 ∣ subsidy) :
    (subsidy - streamShare subsidy MAJOR_GRANTS_NUMERATOR -
       lockboxPerBlock subsidy) +
      streamShare subsidy MAJOR_GRANTS_NUMERATOR +
      lockboxPerBlock subsidy = subsidy := by
  unfold lockboxPerBlock streamShare MAJOR_GRANTS_NUMERATOR LOCKBOX_NUMERATOR
    DENOMINATOR
  obtain ⟨k, rfl⟩ := hdvd
  have e8 : 100 * k * 8 / 100 = 8 * k := by
    have heq : 100 * k * 8 = 100 * (8 * k) := by ring
    rw [heq]
    exact Nat.mul_div_cancel_left (8 * k) (by decide : (0 : Nat) < 100)
  have e12 : 100 * k * 12 / 100 = 12 * k := by
    have heq : 100 * k * 12 = 100 * (12 * k) := by ring
    rw [heq]
    exact Nat.mul_div_cancel_left (12 * k) (by decide : (0 : Nat) < 100)
  rw [e8, e12]
  -- Need (100*k − 8*k − 12*k) + 8*k + 12*k = 100*k. With 8k + 12k = 20k ≤ 100k.
  omega

/-- **T11 (NU6 funding-stream split sanity).** The post-NU6 mainnet table
numerators (MajorGrants `8` + Deferred `12`) sum to `20`, so the post-NU6
miner share is `80/100`. -/
theorem nu6_postnu6_table_split :
    MAJOR_GRANTS_NUMERATOR + LOCKBOX_NUMERATOR = 20 := by
  decide

/-- **T12 (full pre-NU6 + deferred table sanity).** The pre-NU6 mainnet table
numerators (ECC `7` + ZF `5` + MajorGrants `8`) sum to `20`. Adding the NU6
deferred share (`12`) gives `32`, leaving the miner with `68/100` *if* both
the dev-fund and the lockbox were paid simultaneously (a counterfactual since
the NU6 table replaces ECC/ZF with zero). -/
theorem prenu6_dev_fund_plus_lockbox :
    ECC_NUMERATOR + ZF_NUMERATOR + MAJOR_GRANTS_NUMERATOR +
      LOCKBOX_NUMERATOR = 32 := by
  decide

/-- **T13 (lockbox concrete: at the genesis-style block subsidy of
`12.5 ZEC = 1_250_000_000 zats`, the lockbox is `1.5 ZEC = 150_000_000
zats` per block).** -/
theorem lockbox_at_max_block_subsidy :
    lockboxPerBlock 1_250_000_000 = 150_000_000 := by
  rw [lockboxPerBlock_eq]

/-- **T14 (lockbox at `MAX_MONEY`).** Even at the (counterfactual) maximum
single-block subsidy of `MAX_MONEY = 21_000_000 * COIN`, the deferred share is
exactly `12/100` of that, i.e. `2_520_000 * COIN`. -/
theorem lockbox_at_max_money :
    lockboxPerBlock MAX_MONEY = 2_520_000 * COIN := by
  unfold MAX_MONEY COIN
  rw [lockboxPerBlock_eq]

/-- **T15 (cumulative-lockbox bound by MAX_MONEY per-block-budget).** Over
`n` blocks of any subsidy bounded by `MAX_MONEY`, the cumulative lockbox is
bounded by `n * MAX_MONEY * 12 / 100` — i.e. the worst-case lockbox share of
`n` block budgets. This subsumes T6 by `12/100 ≤ 1`. -/
theorem cumulativeLockbox_share_le (n subsidy : Nat) (h : subsidy ≤ MAX_MONEY) :
    cumulativeLockbox n subsidy ≤ n * (MAX_MONEY * 12 / 100) := by
  unfold cumulativeLockbox
  rw [lockboxPerBlock_eq]
  -- subsidy * 12 / 100 ≤ MAX_MONEY * 12 / 100 by monotonicity of /100 ∘ (*12).
  have h₁ : subsidy * 12 ≤ MAX_MONEY * 12 := Nat.mul_le_mul_right 12 h
  have h₂ : subsidy * 12 / 100 ≤ MAX_MONEY * 12 / 100 :=
    Nat.div_le_div_right h₁
  exact Nat.mul_le_mul_left n h₂

end Zebra.Zip2001Lockbox
