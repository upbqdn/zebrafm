import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.ModEq

/-!
# ZIP-1015 NU6 lockbox: deferred-pool arithmetic

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

## Note on module name

The module is named `Zip2001Lockbox` for historical reasons in this repo,
but the underlying ZIP is **ZIP-1015** (deferred dev fund) layered with
ZIP-214 (funding streams). There is no published ZIP-2001 governing
lockboxes. See the sibling `Zip1015FundingStreams` module for the full
Era-aware split.

## What this module proves

This module is *focused* on the deferred (lockbox) share specifically and on
the per-era partition identity. The three funding-stream tables in
`subsidy/constants/mainnet.rs:192-243` are **disjoint in height**:

* Pre-NU6 (Canopy era), `1_046_400..2_726_400`: ECC `7`, ZF `5`, MajorGrants
  `8`, Deferred `0`.
* Post-NU6, `2_726_400..3_146_400`: Deferred `12`, MajorGrants `8`, ECC and
  ZF zeroed.
* Post-NU6.1, `NU6_1..4_406_400`: same numerators as post-NU6 (Deferred
  `12`, MajorGrants `8`).

So at any single height the `minerPerBlock` budget is the subsidy minus the
recipients of *one* table, not both at once. We model this with an `Era` tag
and prove conservation per era.

Bounds established:

* `lockboxPerBlock = floor(subsidy * 12 / 100)` (T1, `@[simp]`).
* `lockboxPerBlock ≤ subsidy` always (T3).
* `lockboxPerBlock ≤ MAX_MONEY` when `subsidy ≤ MAX_MONEY` (T2).
* `cumulativeLockbox` additive in the block count (T4), monotone (T7).
* Cumulative bound by `n * MAX_BLOCK_SUBSIDY * 12 / 100` (T6'), tighter than
  the historical `n * MAX_MONEY` bound.
* Per-era sum conservation: `miner(e) + Σ recipients(e) = subsidy` when
  `100 ∣ subsidy` (T8, T10).
* Per-era safety: `Σ recipients(e) ≤ subsidy` without divisibility (T9).
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

/-- Maximum per-block subsidy, `MAX_BLOCK_SUBSIDY = 1_250_000_000` zatoshis
(= 12.5 ZEC). Source: `subsidy/constants.rs` (`MAX_BLOCK_SUBSIDY`). -/
def MAX_BLOCK_SUBSIDY : Nat := 1_250_000_000

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

/-- Post-NU6 mainnet start height.
Source: `subsidy/constants/mainnet.rs:15` :
`POST_NU6_FUNDING_STREAM_START_HEIGHT: u32 = 2_726_400`. -/
def POST_NU6_START : Nat := 2_726_400

/-- Number of blocks in the post-NU6 funding stream window.
Source: `subsidy/constants.rs:48` :
`POST_NU6_FUNDING_STREAM_NUM_BLOCKS: u32 = 420_000`. -/
def POST_NU6_NUM_BLOCKS : Nat := 420_000

/-! ## Era model

The Rust `FUNDING_STREAMS` table in `subsidy/constants/mainnet.rs:192-243`
defines three disjoint height ranges. Lockboxes are paid only in the post-NU6
ranges; the pre-NU6 dev fund is paid only in the pre-NU6 range. We encode
this with an `Era` tag so that the per-block partition is well-typed. -/

/-- The two ZIP-1015/ZIP-214 funding-stream eras relevant to lockboxes. NU6
and NU6.1 are layout-identical in numerator terms (only the MajorGrants
address set differs), so they share `Era.postNu6`. -/
inductive Era
  | preNu6
  | postNu6
deriving DecidableEq, Repr

/-! ## Definitions -/

/-- Apply a funding-stream fraction to a subsidy with integer floor division.
Exactly the arithmetic from `funding_stream_values` in
`zebra-chain/src/parameters/network/subsidy.rs:338`. -/
def streamShare (subsidy numerator : Nat) : Nat :=
  (subsidy * numerator) / DENOMINATOR

/-- The lockbox (Deferred) share per block, post-NU6.
`floor(subsidy * 12 / 100)`. Pre-NU6 this is structurally zero (no Deferred
recipient in the table). -/
def lockboxPerBlock (subsidy : Nat) : Nat :=
  streamShare subsidy LOCKBOX_NUMERATOR

/-- The era-tagged lockbox share per block. Zero in `preNu6`. -/
def lockboxPerBlockEra : Era → Nat → Nat
  | Era.preNu6,  _       => 0
  | Era.postNu6, subsidy => lockboxPerBlock subsidy

/-- The pre-NU6 dev-fund recipients aggregated:
ECC (7) + ZF (5) + MajorGrants (8). Total numerator `20/100`. -/
def devFundPreNu6 (subsidy : Nat) : Nat :=
  streamShare subsidy ECC_NUMERATOR +
  streamShare subsidy ZF_NUMERATOR +
  streamShare subsidy MAJOR_GRANTS_NUMERATOR

/-- The post-NU6 funding-stream recipients aggregated: Deferred (12) +
MajorGrants (8). Total numerator `20/100`. Note ECC and ZF are zeroed in
this table (`mainnet.rs:212-227` and `:228-242`). -/
def fundedPostNu6 (subsidy : Nat) : Nat :=
  streamShare subsidy MAJOR_GRANTS_NUMERATOR +
  lockboxPerBlock subsidy

/-- The era-tagged sum of all funding-stream recipients at a height. -/
def totalRecipientsEra : Era → Nat → Nat
  | Era.preNu6,  subsidy => devFundPreNu6 subsidy
  | Era.postNu6, subsidy => fundedPostNu6 subsidy

/-- The miner share per block at a given era: `subsidy` minus the active
funding-stream recipients for that era. This mirrors the Rust behaviour:
`funding_stream_values` deducts only the recipients present in the active
table at the given height (see `subsidy.rs:338-367` and the disjoint
`FUNDING_STREAMS` height ranges in `mainnet.rs:192-243`). -/
def minerPerBlockEra (e : Era) (subsidy : Nat) : Nat :=
  subsidy - totalRecipientsEra e subsidy

/-- Cumulative lockbox balance after `n` blocks given a *constant* per-block
subsidy. Reasonable model over an interval where the halving divisor does not
change. -/
def cumulativeLockbox (n subsidy : Nat) : Nat :=
  n * lockboxPerBlock subsidy

/-! ## Theorems -/

/-- **T1 (lockbox formula matches the spec floor expression).** The deferred
per-block share equals `floor(subsidy * 12 / 100)`. Tagged `@[simp]` so
downstream rewriting can unfold the wrapper. -/
@[simp]
theorem lockboxPerBlock_eq (subsidy : Nat) :
    lockboxPerBlock subsidy = subsidy * 12 / 100 := by
  unfold lockboxPerBlock streamShare LOCKBOX_NUMERATOR DENOMINATOR
  rfl

/-- **T2 (lockbox bounded by `MAX_MONEY` when subsidy is).** Whenever the
subsidy itself sits inside the `MAX_MONEY` envelope, the deferred share is
also bounded by `MAX_MONEY`. -/
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

/-- **T6 (cumulative lockbox bounded by `n * MAX_BLOCK_SUBSIDY`).** The
realistic per-block envelope: the lockbox cannot exceed `n * MAX_BLOCK_SUBSIDY`
over `n` blocks. This is much tighter than `n * MAX_MONEY` since every block
on mainnet is capped at `MAX_BLOCK_SUBSIDY = 1.25e9` zatoshis. -/
theorem cumulativeLockbox_le_n_max_block_subsidy (n subsidy : Nat)
    (h : subsidy ≤ MAX_BLOCK_SUBSIDY) :
    cumulativeLockbox n subsidy ≤ n * MAX_BLOCK_SUBSIDY := by
  unfold cumulativeLockbox
  have h₁ : lockboxPerBlock subsidy ≤ MAX_BLOCK_SUBSIDY :=
    le_trans (lockboxPerBlock_le_subsidy subsidy) h
  exact Nat.mul_le_mul_left n h₁

/-- **T6' (tight cumulative lockbox bound, 12 % of `n * MAX_BLOCK_SUBSIDY`).**
The Deferred numerator is 12/100, so over `n` blocks each capped at
`MAX_BLOCK_SUBSIDY` the cumulative lockbox can grow at most
`n * (MAX_BLOCK_SUBSIDY * 12 / 100)`. This is the tightest envelope and
addresses the loose-bound finding. -/
theorem cumulativeLockbox_share_of_max_block_subsidy (n subsidy : Nat)
    (h : subsidy ≤ MAX_BLOCK_SUBSIDY) :
    cumulativeLockbox n subsidy ≤ n * (MAX_BLOCK_SUBSIDY * 12 / 100) := by
  unfold cumulativeLockbox
  rw [lockboxPerBlock_eq]
  have h₁ : subsidy * 12 ≤ MAX_BLOCK_SUBSIDY * 12 := Nat.mul_le_mul_right 12 h
  have h₂ : subsidy * 12 / 100 ≤ MAX_BLOCK_SUBSIDY * 12 / 100 :=
    Nat.div_le_div_right h₁
  exact Nat.mul_le_mul_left n h₂

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

/-- **T8 (pre-NU6 sum conservation).** In the pre-NU6 era the active
recipients are ECC (7) + ZF (5) + MG (8) = 20/100; lockbox is structurally
zero. When `100 ∣ subsidy` the partition
`miner + ECC + ZF + MG = subsidy` holds exactly. This is the era-correct
analogue of the old T8 — it no longer mixes the pre- and post-NU6 tables. -/
theorem sum_conservation_preNu6
    (subsidy : Nat) (hdvd : 100 ∣ subsidy) :
    minerPerBlockEra Era.preNu6 subsidy +
      streamShare subsidy ECC_NUMERATOR +
      streamShare subsidy ZF_NUMERATOR +
      streamShare subsidy MAJOR_GRANTS_NUMERATOR
      = subsidy := by
  change subsidy - totalRecipientsEra Era.preNu6 subsidy +
      streamShare subsidy ECC_NUMERATOR +
      streamShare subsidy ZF_NUMERATOR +
      streamShare subsidy MAJOR_GRANTS_NUMERATOR = subsidy
  change subsidy - devFundPreNu6 subsidy +
      streamShare subsidy ECC_NUMERATOR +
      streamShare subsidy ZF_NUMERATOR +
      streamShare subsidy MAJOR_GRANTS_NUMERATOR = subsidy
  unfold devFundPreNu6 streamShare
    ECC_NUMERATOR ZF_NUMERATOR MAJOR_GRANTS_NUMERATOR DENOMINATOR
  obtain ⟨k, rfl⟩ := hdvd
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
  rw [e7, e5, e8]
  -- Goal: (100*k − (7*k + 5*k + 8*k)) + 7*k + 5*k + 8*k = 100*k.
  -- 20*k ≤ 100*k so Nat.sub is exact.
  omega

/-- **T9 (pre-NU6 dev-fund bounded by subsidy, all subsidies).** Even without
the divisibility hypothesis, the three pre-NU6 dev-fund streams together
never exceed the subsidy. Safety property keeping `minerPerBlockEra preNu6`
non-negative. -/
theorem devFundPreNu6_le_subsidy (subsidy : Nat) :
    devFundPreNu6 subsidy ≤ subsidy := by
  unfold devFundPreNu6 streamShare
    ECC_NUMERATOR ZF_NUMERATOR MAJOR_GRANTS_NUMERATOR DENOMINATOR
  -- Use sub-additivity of `Nat` floor division: a/d + b/d ≤ (a+b)/d.
  have h₁ : subsidy * 7 / 100 + subsidy * 5 / 100 ≤
            (subsidy * 7 + subsidy * 5) / 100 :=
    Nat.add_div_le_add_div (subsidy * 7) (subsidy * 5) 100
  have h₂ : (subsidy * 7 + subsidy * 5) / 100 + subsidy * 8 / 100 ≤
            (subsidy * 7 + subsidy * 5 + subsidy * 8) / 100 :=
    Nat.add_div_le_add_div (subsidy * 7 + subsidy * 5) (subsidy * 8) 100
  have hchain :
      subsidy * 7 / 100 + subsidy * 5 / 100 + subsidy * 8 / 100 ≤
      (subsidy * 7 + subsidy * 5 + subsidy * 8) / 100 := by
    have step1 :
        subsidy * 7 / 100 + subsidy * 5 / 100 + subsidy * 8 / 100 ≤
        (subsidy * 7 + subsidy * 5) / 100 + subsidy * 8 / 100 :=
      Nat.add_le_add_right h₁ _
    exact le_trans step1 h₂
  have hsum_eq : subsidy * 7 + subsidy * 5 + subsidy * 8 = subsidy * 20 := by ring
  have hbound : subsidy * 20 / 100 ≤ subsidy := by
    have hmul : subsidy * 20 ≤ subsidy * 100 :=
      Nat.mul_le_mul_left subsidy (by decide)
    calc subsidy * 20 / 100
        ≤ subsidy * 100 / 100 := Nat.div_le_div_right hmul
      _ = subsidy := Nat.mul_div_cancel subsidy (by decide : (0 : Nat) < 100)
  rw [hsum_eq] at hchain
  exact le_trans hchain hbound

/-- **T10 (post-NU6 sum conservation).** In the post-NU6 era the active
recipients are MajorGrants (8) + Deferred (12) = 20/100. When
`100 ∣ subsidy` the partition `miner + MG + lockbox = subsidy` holds. -/
theorem sum_conservation_postNu6
    (subsidy : Nat) (hdvd : 100 ∣ subsidy) :
    minerPerBlockEra Era.postNu6 subsidy +
      streamShare subsidy MAJOR_GRANTS_NUMERATOR +
      lockboxPerBlock subsidy = subsidy := by
  change subsidy - totalRecipientsEra Era.postNu6 subsidy +
      streamShare subsidy MAJOR_GRANTS_NUMERATOR +
      lockboxPerBlock subsidy = subsidy
  change subsidy - fundedPostNu6 subsidy +
      streamShare subsidy MAJOR_GRANTS_NUMERATOR +
      lockboxPerBlock subsidy = subsidy
  unfold fundedPostNu6
    lockboxPerBlock streamShare MAJOR_GRANTS_NUMERATOR LOCKBOX_NUMERATOR
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
  -- Need (100*k − (8*k + 12*k)) + 8*k + 12*k = 100*k. 20k ≤ 100k.
  omega

/-- **T11 (post-NU6 funded-recipient sum bounded by subsidy).** Even without
divisibility, the two post-NU6 recipients (MajorGrants + Deferred) together
never exceed the subsidy. -/
theorem fundedPostNu6_le_subsidy (subsidy : Nat) :
    fundedPostNu6 subsidy ≤ subsidy := by
  unfold fundedPostNu6 lockboxPerBlock streamShare
    MAJOR_GRANTS_NUMERATOR LOCKBOX_NUMERATOR DENOMINATOR
  have h₁ : subsidy * 8 / 100 + subsidy * 12 / 100 ≤
            (subsidy * 8 + subsidy * 12) / 100 :=
    Nat.add_div_le_add_div (subsidy * 8) (subsidy * 12) 100
  have hsum_eq : subsidy * 8 + subsidy * 12 = subsidy * 20 := by ring
  have hbound : subsidy * 20 / 100 ≤ subsidy := by
    have hmul : subsidy * 20 ≤ subsidy * 100 :=
      Nat.mul_le_mul_left subsidy (by decide)
    calc subsidy * 20 / 100
        ≤ subsidy * 100 / 100 := Nat.div_le_div_right hmul
      _ = subsidy := Nat.mul_div_cancel subsidy (by decide : (0 : Nat) < 100)
  rw [hsum_eq] at h₁
  exact le_trans h₁ hbound

/-- **T12 (total recipient deduction bounded by subsidy, both eras).** -/
theorem totalRecipientsEra_le_subsidy (e : Era) (subsidy : Nat) :
    totalRecipientsEra e subsidy ≤ subsidy := by
  cases e with
  | preNu6  => exact devFundPreNu6_le_subsidy subsidy
  | postNu6 => exact fundedPostNu6_le_subsidy subsidy

/-- **T13 (era-tagged lockbox is zero pre-NU6, equal to the post-NU6 share
otherwise).** Captures the disjointness from `mainnet.rs:192-243`: only the
post-NU6 tables contain a Deferred entry. -/
theorem lockboxPerBlockEra_cases (subsidy : Nat) :
    lockboxPerBlockEra Era.preNu6 subsidy = 0 ∧
      lockboxPerBlockEra Era.postNu6 subsidy = lockboxPerBlock subsidy := by
  refine ⟨rfl, rfl⟩

/-- **T14 (pre-NU6 numerator sum is 20).** ZIP-214 splits 20 % of the
subsidy across ECC, ZF, MG. -/
theorem preNu6_numerator_sum :
    ECC_NUMERATOR + ZF_NUMERATOR + MAJOR_GRANTS_NUMERATOR = 20 := by
  decide

/-- **T15 (post-NU6 numerator sum is 20).** ZIP-1015 also splits exactly
20 % of the subsidy: 8 % to MajorGrants, 12 % to the Deferred lockbox. -/
theorem postNu6_numerator_sum :
    MAJOR_GRANTS_NUMERATOR + LOCKBOX_NUMERATOR = 20 := by
  decide

/-- **T16 (lockbox concrete at `MAX_BLOCK_SUBSIDY`).** At the maximum
per-block subsidy of `12.5 ZEC = 1_250_000_000` zats, the lockbox is
`1.5 ZEC = 150_000_000` zats per block. -/
theorem lockbox_at_max_block_subsidy :
    lockboxPerBlock MAX_BLOCK_SUBSIDY = 150_000_000 := by
  unfold MAX_BLOCK_SUBSIDY
  rw [lockboxPerBlock_eq]

/-- **T17 (lockbox at `MAX_MONEY`).** Even at the (counterfactual) maximum
single-block subsidy of `MAX_MONEY = 21_000_000 * COIN`, the deferred share is
exactly `12/100` of that, i.e. `2_520_000 * COIN`. -/
theorem lockbox_at_max_money :
    lockboxPerBlock MAX_MONEY = 2_520_000 * COIN := by
  unfold MAX_MONEY COIN
  rw [lockboxPerBlock_eq]

/-- **T18 (cumulative lockbox over the post-NU6 funding window is bounded
by `POST_NU6_NUM_BLOCKS * MAX_BLOCK_SUBSIDY * 12 / 100`).** The funding
stream window spans `POST_NU6_NUM_BLOCKS = 420_000` blocks
(`subsidy/constants.rs:48`); over that window the lockbox cannot exceed
`420_000 * 1.5 ZEC = 630_000 ZEC`. -/
theorem cumulativeLockbox_over_window
    (subsidy : Nat) (h : subsidy ≤ MAX_BLOCK_SUBSIDY) :
    cumulativeLockbox POST_NU6_NUM_BLOCKS subsidy ≤
      POST_NU6_NUM_BLOCKS * (MAX_BLOCK_SUBSIDY * 12 / 100) :=
  cumulativeLockbox_share_of_max_block_subsidy POST_NU6_NUM_BLOCKS subsidy h

/-- **T19 (era-tagged lockbox bounded by subsidy).** -/
theorem lockboxPerBlockEra_le_subsidy (e : Era) (subsidy : Nat) :
    lockboxPerBlockEra e subsidy ≤ subsidy := by
  cases e with
  | preNu6  => exact Nat.zero_le _
  | postNu6 => exact lockboxPerBlock_le_subsidy subsidy

end Zebra.Zip2001Lockbox
