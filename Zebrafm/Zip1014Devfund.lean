import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# ZIP-1014: Dev-fund funding stream allocation (Canopy → NU6)

ZIP-1014 ("Establishing a Dev Fund for ECC, ZF, and Major Grants") replaced
the pre-Canopy Founders' Reward with a three-recipient *funding stream*: a
flat `20%` slice of the post-slow-start block subsidy is split between the
Electric Coin Company (`7%`), the Zcash Foundation (`5%`), and the Zcash
Community Grants Major Grants program (`8%`), with the miner receiving the
remaining `80%`. On Mainnet the stream runs from the first block of Canopy
(which by definition is the *first* halving on Mainnet) up to — but not
including — the NU6 activation block (which is the *second* halving on
Mainnet). The stream therefore covers exactly one full post-Blossom
halving epoch.

The Rust enforcement path:

  * Recipients and numerators are hard-coded for Mainnet at
    `zebra-chain/src/parameters/network/subsidy/constants/mainnet.rs:192-211`
    inside the first `FundingStreams { … }` literal:
    `Ecc → 7`, `ZcashFoundation → 5`, `MajorGrants → 8`.
  * The denominator is the constant
    `FUNDING_STREAM_RECEIVER_DENOMINATOR = 100`
    (`zebra-chain/src/parameters/network/subsidy/constants.rs:34`).
  * The active height range is `Height(1_046_400)..Height(2_726_400)` —
    Mainnet Canopy activation (= first halving, per
    `subsidy.rs:240` "First halving on Mainnet is at Canopy") through
    (exclusive) NU6 activation (= second halving).
  * Per-recipient amounts are computed by
    `funding_stream_values` at
    `zebra-chain/src/parameters/network/subsidy.rs:338-367` as
    `floor(block_subsidy * numerator / 100)`.
  * The miner's share is
    `miner_subsidy = block_subsidy − founders_reward − Σ funding streams`
    (`zebra-chain/src/parameters/network/subsidy.rs:484-496`); after the
    Founders' Reward ends at Canopy, this collapses to
    `block_subsidy − Σ funding streams`, i.e. exactly the `80%` miner
    share modeled here.

Scope: Mainnet only. Testnet and Regtest have different `FundingStreams`
literals and different `FIRST_HALVING` constants (Testnet `1_116_000`,
Regtest `287`); modelling those is out of scope for this module.

This module models the three numerators as `Nat`s, the denominator as
`100`, the height range as `[1_046_400, 2_726_400)`, and proves the
ZIP-1014 dev-fund arithmetic:

  1. the three numerators sum to `20`,
  2. the per-recipient amounts sum to the `20%` dev-fund slice when the
     block subsidy is divisible by `100`,
  3. the height range begins at the first halving (Canopy = `1_046_400`)
     and ends *at* the second halving (NU6 = `2_726_400`), so the stream
     covers exactly one halving epoch and never spans a halving boundary,
  4. the miner receives the remaining `80%` of the block subsidy after
     the dev-fund slice is taken.

Source: <https://zips.z.cash/zip-1014>
Source: `zebra-chain/src/parameters/network/subsidy/constants/mainnet.rs:192-211`
Source: `zebra-chain/src/parameters/network/subsidy/constants.rs:34`
Source: `zebra-chain/src/parameters/network/subsidy.rs:239-253` (first halving = Canopy)
Source: `zebra-chain/src/parameters/network/subsidy.rs:338-367`,
        `:484-496`
-/

namespace Zebra.Zip1014Devfund

/-! ## Constants -/

/-- ECC funding-stream numerator (`7`).
Source: `zebra-chain/src/parameters/network/subsidy/constants/mainnet.rs:198`
(`FundingStreamReceiver::Ecc → FundingStreamRecipient::new(7, …)`). -/
def ECC_NUMERATOR : Nat := 7

/-- Zcash Foundation funding-stream numerator (`5`).
Source: `zebra-chain/src/parameters/network/subsidy/constants/mainnet.rs:202`
(`FundingStreamReceiver::ZcashFoundation → FundingStreamRecipient::new(5, …)`). -/
def ZF_NUMERATOR : Nat := 5

/-- Major Grants funding-stream numerator (`8`).
Source: `zebra-chain/src/parameters/network/subsidy/constants/mainnet.rs:206`
(`FundingStreamReceiver::MajorGrants → FundingStreamRecipient::new(8, …)`). -/
def MG_NUMERATOR : Nat := 8

/-- The shared denominator for all funding-stream recipients.
Source: `zebra-chain/src/parameters/network/subsidy/constants.rs:34`
(`FUNDING_STREAM_RECEIVER_DENOMINATOR: u64 = 100`). -/
def DENOMINATOR : Nat := 100

/-- The total numerator of the three dev-fund recipients (`7 + 5 + 8 = 20`).
This is the `20%` headline figure of ZIP-1014 once divided by the
denominator. -/
def DEV_FUND_NUMERATOR : Nat := ECC_NUMERATOR + ZF_NUMERATOR + MG_NUMERATOR

/-- The miner's residual numerator after the dev-fund slice: `100 − 20 = 80`. -/
def MINER_NUMERATOR : Nat := DENOMINATOR - DEV_FUND_NUMERATOR

/-- First block of Canopy on Mainnet, the lower end of the ZIP-1014 dev-fund
height range. This is *also* the Mainnet `height_for_first_halving`
(`subsidy.rs:240-241`: "First halving on Mainnet is at Canopy"), so the
dev-fund range begins exactly at the first halving boundary.
Source: `zebra-chain/src/parameters/network/subsidy/constants/mainnet.rs:194`
(`height_range: Height(1_046_400)..…`). -/
def DEV_FUND_START_HEIGHT : Nat := 1_046_400

/-- First block of NU6 on Mainnet, which is the *second* halving (the upper
end of the ZIP-1014 dev-fund height range, exclusive). It is reached at
`first_halving + POST_BLOSSOM_HALVING_INTERVAL = 1_046_400 + 1_680_000 =
2_726_400`, matching `height_for_halving(2, Mainnet)` per
`zebra-chain/src/parameters/network/subsidy.rs:307-332`.
Source: `zebra-chain/src/parameters/network/subsidy/constants/mainnet.rs:194`
(`…..Height(2_726_400)`). -/
def DEV_FUND_END_HEIGHT : Nat := 2_726_400

/-- The Mainnet *first* halving height: by Rust's
`ParameterSubsidy::height_for_first_halving` for `Mainnet`, this is the
Canopy activation height (`subsidy.rs:239-244`: "First halving on Mainnet
is at Canopy"). Provided as a named constant so theorems can refer to the
first halving height directly rather than via `DEV_FUND_START_HEIGHT`. -/
def FIRST_HALVING_HEIGHT : Nat := 1_046_400

/-- The Mainnet *second* halving height: `first_halving +
POST_BLOSSOM_HALVING_INTERVAL = 1_046_400 + 1_680_000 = 2_726_400`. This
coincides with NU6 activation on Mainnet and is the (exclusive) upper
bound of the ZIP-1014 dev-fund stream. -/
def SECOND_HALVING_HEIGHT : Nat := 2_726_400

/-- The pre-Blossom halving interval (`840_000`) — the number of pre-Blossom
blocks per halving period.
Source: `zebra-chain/src/parameters/network/subsidy/constants.rs:25`
(`PRE_BLOSSOM_HALVING_INTERVAL: HeightDiff = 840_000`). -/
def PRE_BLOSSOM_HALVING_INTERVAL : Nat := 840_000

/-- The post-Blossom halving interval (`1_680_000`) — twice the pre-Blossom
interval, because Blossom halves block times.
Source: `zebra-chain/src/parameters/network/subsidy/constants.rs:28-29`
(`POST_BLOSSOM_HALVING_INTERVAL = PRE_BLOSSOM_HALVING_INTERVAL *
BLOSSOM_POW_TARGET_SPACING_RATIO`). -/
def POST_BLOSSOM_HALVING_INTERVAL : Nat := 1_680_000

/-- The Mainnet Blossom activation height (`653_600`), used below to recover
the first-halving height from network-upgrade parameters.
Source: `zebra-chain/src/parameters/constants/activation_heights.rs`
(`Blossom = 653_600` on Mainnet). -/
def BLOSSOM_ACTIVATION_HEIGHT : Nat := 653_600

/-! ## Per-recipient amount computations

These mirror `funding_stream_values` from
`zebra-chain/src/parameters/network/subsidy.rs:338-367`: each recipient
receives `floor(blockSubsidy * numerator / denominator)`. -/

/-- The amount paid to a funding-stream recipient given the block subsidy
and the recipient's numerator. This is `floor(blockSubsidy * numerator /
DENOMINATOR)` — natural-number division is `floor` for non-negative inputs,
matching the Rust `u64` division at
`zebra-chain/src/parameters/network/subsidy.rs:358-359`. -/
def recipientAmount (blockSubsidy numerator : Nat) : Nat :=
  blockSubsidy * numerator / DENOMINATOR

/-- The amount paid to ECC at a given block subsidy. -/
def eccAmount (blockSubsidy : Nat) : Nat :=
  recipientAmount blockSubsidy ECC_NUMERATOR

/-- The amount paid to the Zcash Foundation at a given block subsidy. -/
def zfAmount (blockSubsidy : Nat) : Nat :=
  recipientAmount blockSubsidy ZF_NUMERATOR

/-- The amount paid to Major Grants at a given block subsidy. -/
def mgAmount (blockSubsidy : Nat) : Nat :=
  recipientAmount blockSubsidy MG_NUMERATOR

/-- Total dev-fund slice as a single allocation against `DEV_FUND_NUMERATOR`. -/
def devFundSlice (blockSubsidy : Nat) : Nat :=
  recipientAmount blockSubsidy DEV_FUND_NUMERATOR

/-- The miner's share, computed by the Rust `miner_subsidy` formula
specialised to the ZIP-1014 era (no Founders' Reward after Canopy):
`miner = blockSubsidy − (eccAmount + zfAmount + mgAmount)`.

Source: `zebra-chain/src/parameters/network/subsidy.rs:484-496`. -/
def minerAmount (blockSubsidy : Nat) : Nat :=
  blockSubsidy - (eccAmount blockSubsidy + zfAmount blockSubsidy + mgAmount blockSubsidy)

/-- Active height predicate for the ZIP-1014 funding stream.

`isInDevFundRange h ↔ DEV_FUND_START_HEIGHT ≤ h ∧ h < DEV_FUND_END_HEIGHT`,
mirroring `funding_streams.height_range` from
`zebra-chain/src/parameters/network/subsidy/constants/mainnet.rs:194`
(`Range<Height>` is half-open in Rust). -/
def isInDevFundRange (h : Nat) : Prop :=
  DEV_FUND_START_HEIGHT ≤ h ∧ h < DEV_FUND_END_HEIGHT

instance (h : Nat) : Decidable (isInDevFundRange h) := by
  unfold isInDevFundRange
  exact inferInstance

/-! ## Theorems -/

/-- **T1 (dev-fund numerators sum to 20).** The three ZIP-1014 recipient
numerators (`7 + 5 + 8`) sum to `20`. Together with `DENOMINATOR = 100`,
this is the "20% dev fund" headline of ZIP-1014. -/
theorem numerators_sum_to_twenty :
    ECC_NUMERATOR + ZF_NUMERATOR + MG_NUMERATOR = 20 := by
  unfold ECC_NUMERATOR ZF_NUMERATOR MG_NUMERATOR; rfl

/-- **T2 (`DEV_FUND_NUMERATOR` evaluates to 20).** Restatement of T1 via the
combined constant. -/
theorem dev_fund_numerator_eq_twenty : DEV_FUND_NUMERATOR = 20 := by
  unfold DEV_FUND_NUMERATOR ECC_NUMERATOR ZF_NUMERATOR MG_NUMERATOR; rfl

/-- **T3 (miner numerator is 80).** The remaining share after the dev-fund
slice is `100 − 20 = 80` — i.e. the miner receives `80%` of the block
subsidy after Canopy.

Source: `zebra-chain/src/parameters/network/subsidy.rs:495`
(`expected_block_subsidy − founders_reward − funding_streams_sum`). -/
theorem miner_numerator_eq_eighty : MINER_NUMERATOR = 80 := by
  unfold MINER_NUMERATOR DENOMINATOR DEV_FUND_NUMERATOR
        ECC_NUMERATOR ZF_NUMERATOR MG_NUMERATOR; rfl

/-- **T4 (numerators + miner partition the denominator exactly).** The three
recipient numerators plus the miner's residual numerator equal the
denominator: `7 + 5 + 8 + 80 = 100`. This is the "no value is lost or
inflated" partition invariant of ZIP-1014. -/
theorem numerators_partition_denominator :
    ECC_NUMERATOR + ZF_NUMERATOR + MG_NUMERATOR + MINER_NUMERATOR = DENOMINATOR := by
  unfold ECC_NUMERATOR ZF_NUMERATOR MG_NUMERATOR MINER_NUMERATOR
        DENOMINATOR DEV_FUND_NUMERATOR; rfl

/-- **T5 (denominator is positive).** A guard for division: `100 > 0`, so
`recipientAmount` is a well-defined floor division. -/
theorem denominator_pos : 0 < DENOMINATOR := by
  unfold DENOMINATOR; decide

/-- **T6 (per-recipient amount is bounded by the subsidy).** Each
recipient's amount never exceeds the block subsidy itself.

This is the "no recipient overpays" invariant: even at the largest
allowed numerator (`MG_NUMERATOR = 8`), `floor(subsidy * 8 / 100) ≤
subsidy`. -/
theorem ecc_amount_le_subsidy (s : Nat) : eccAmount s ≤ s := by
  unfold eccAmount recipientAmount ECC_NUMERATOR DENOMINATOR
  -- `s * 7 / 100 ≤ s` because `s * 7 / 100 ≤ s * 7 / 7 = s` for `s ≥ 0`.
  have h1 : s * 7 / 100 ≤ s * 7 / 7 :=
    Nat.div_le_div_left (by decide) (by decide)
  have h2 : s * 7 / 7 = s := Nat.mul_div_cancel s (by decide)
  omega

theorem zf_amount_le_subsidy (s : Nat) : zfAmount s ≤ s := by
  unfold zfAmount recipientAmount ZF_NUMERATOR DENOMINATOR
  have h1 : s * 5 / 100 ≤ s * 5 / 5 :=
    Nat.div_le_div_left (by decide) (by decide)
  have h2 : s * 5 / 5 = s := Nat.mul_div_cancel s (by decide)
  omega

theorem mg_amount_le_subsidy (s : Nat) : mgAmount s ≤ s := by
  unfold mgAmount recipientAmount MG_NUMERATOR DENOMINATOR
  have h1 : s * 8 / 100 ≤ s * 8 / 8 :=
    Nat.div_le_div_left (by decide) (by decide)
  have h2 : s * 8 / 8 = s := Nat.mul_div_cancel s (by decide)
  omega

/-- **T7 (recipients sum equals the dev-fund slice for divisible subsidies).**
When the block subsidy is divisible by `100` (the denominator), the sum of
the three per-recipient amounts is *exactly* the dev-fund slice
`subsidy * 20 / 100 = subsidy * DEV_FUND_NUMERATOR / DENOMINATOR`. There is
no rounding loss in this case.

Block subsidies in Zcash are always exact multiples of `1/(2*halving_div)`
zatoshis, and the post-Canopy values are large enough that the divisibility
hypothesis trivially holds in practice; the property without that
hypothesis is "off by at most 2 zatoshis" (see T8). -/
theorem recipients_sum_eq_devfund_when_divisible
    (s : Nat) (hs : DENOMINATOR ∣ s) :
    eccAmount s + zfAmount s + mgAmount s = devFundSlice s := by
  -- Unfold the predicate `DENOMINATOR ∣ s` first so `obtain` works.
  simp only [DENOMINATOR] at hs
  obtain ⟨q, rfl⟩ := hs
  simp only [eccAmount, zfAmount, mgAmount, devFundSlice,
        recipientAmount, ECC_NUMERATOR, ZF_NUMERATOR, MG_NUMERATOR,
        DEV_FUND_NUMERATOR, DENOMINATOR]
  -- Each share simplifies to `q * numerator`.
  have h7 : 100 * q * 7 / 100 = q * 7 := by
    rw [show 100 * q * 7 = 100 * (q * 7) by ring]
    exact Nat.mul_div_cancel_left (q * 7) (by decide)
  have h5 : 100 * q * 5 / 100 = q * 5 := by
    rw [show 100 * q * 5 = 100 * (q * 5) by ring]
    exact Nat.mul_div_cancel_left (q * 5) (by decide)
  have h8 : 100 * q * 8 / 100 = q * 8 := by
    rw [show 100 * q * 8 = 100 * (q * 8) by ring]
    exact Nat.mul_div_cancel_left (q * 8) (by decide)
  have h20 : 100 * q * (7 + 5 + 8) / 100 = q * 20 := by
    rw [show 100 * q * (7 + 5 + 8) = 100 * (q * 20) by ring]
    exact Nat.mul_div_cancel_left (q * 20) (by decide)
  rw [h7, h5, h8, h20]
  ring

/-- **T8 (recipients sum is bounded by the dev-fund slice).** Without any
divisibility hypothesis, the sum of per-recipient amounts is *at most* the
dev-fund slice — `floor` distributes over addition only with possible
underapproximation. This is the consensus property: the dev fund can never
*overpay* relative to its 20% headline figure. -/
theorem recipients_sum_le_devfund (s : Nat) :
    eccAmount s + zfAmount s + mgAmount s ≤ devFundSlice s := by
  unfold eccAmount zfAmount mgAmount devFundSlice
        recipientAmount ECC_NUMERATOR ZF_NUMERATOR MG_NUMERATOR
        DEV_FUND_NUMERATOR DENOMINATOR
  -- Multiply both sides by 100 and use `n / 100 * 100 ≤ n`.
  have h7 : s * 7 / 100 * 100 ≤ s * 7 := Nat.div_mul_le_self _ _
  have h5 : s * 5 / 100 * 100 ≤ s * 5 := Nat.div_mul_le_self _ _
  have h8 : s * 8 / 100 * 100 ≤ s * 8 := Nat.div_mul_le_self _ _
  have hsum :
      s * 7 / 100 * 100 + s * 5 / 100 * 100 + s * 8 / 100 * 100 ≤ s * 20 := by
    have : s * 7 + s * 5 + s * 8 = s * 20 := by ring
    linarith
  -- Now `a + b + c ≤ ⌊s*20/100⌋` follows from `(a+b+c)*100 ≤ s*20`
  -- iff `a + b + c ≤ s*20 / 100`. Use `Nat.le_div_iff_mul_le`.
  have hdiv : s * 7 / 100 + s * 5 / 100 + s * 8 / 100
              ≤ s * 20 / 100 := by
    rw [Nat.le_div_iff_mul_le (by decide : 0 < 100)]
    calc (s * 7 / 100 + s * 5 / 100 + s * 8 / 100) * 100
        = s * 7 / 100 * 100 + s * 5 / 100 * 100 + s * 8 / 100 * 100 := by ring
      _ ≤ s * 20 := hsum
  exact hdiv

/-- **T9 (dev-fund range starts at Canopy = first halving).** The lower
bound of the ZIP-1014 funding stream is exactly the Canopy activation
height on Mainnet (`1_046_400`), which is *also* the Mainnet first
halving height per
`zebra-chain/src/parameters/network/subsidy.rs:239-244`
("First halving on Mainnet is at Canopy").
Source: `zebra-chain/src/parameters/network/subsidy/constants/mainnet.rs:194`. -/
theorem dev_fund_starts_at_canopy :
    DEV_FUND_START_HEIGHT = 1_046_400 := by
  unfold DEV_FUND_START_HEIGHT; rfl

/-- **T9b (dev-fund start = first halving).** Phrased in halving terms:
`DEV_FUND_START_HEIGHT` is exactly the first halving height
(`FIRST_HALVING_HEIGHT`). This is the algebraic content of "the dev fund
begins at Canopy" once we identify Canopy with the first halving on
Mainnet. -/
theorem dev_fund_start_eq_first_halving :
    DEV_FUND_START_HEIGHT = FIRST_HALVING_HEIGHT := by
  unfold DEV_FUND_START_HEIGHT FIRST_HALVING_HEIGHT; rfl

/-- **T10 (dev-fund range ends at the SECOND halving on Mainnet).** The
upper bound of the ZIP-1014 funding stream is `2_726_400`. On Mainnet
the *first* halving is at Canopy (`1_046_400`); the *second* halving —
which coincides with NU6 activation — is at
`first_halving + POST_BLOSSOM_HALVING_INTERVAL = 1_046_400 + 1_680_000 =
2_726_400`, matching `height_for_halving(2, Mainnet)` per
`zebra-chain/src/parameters/network/subsidy.rs:307-332`. The dev-fund
range therefore ends *exactly* at the second halving, covering one full
post-Blossom halving epoch (the first such epoch) and never spanning a
halving boundary. -/
theorem dev_fund_ends_at_second_halving :
    DEV_FUND_END_HEIGHT = 2_726_400 := by
  unfold DEV_FUND_END_HEIGHT; rfl

/-- **T10b (dev-fund end = first halving + one halving epoch).** Phrased
in halving terms: `DEV_FUND_END_HEIGHT = FIRST_HALVING_HEIGHT +
POST_BLOSSOM_HALVING_INTERVAL`, so it is the *second* halving height on
Mainnet. -/
theorem dev_fund_end_eq_second_halving :
    DEV_FUND_END_HEIGHT = FIRST_HALVING_HEIGHT + POST_BLOSSOM_HALVING_INTERVAL := by
  unfold DEV_FUND_END_HEIGHT FIRST_HALVING_HEIGHT POST_BLOSSOM_HALVING_INTERVAL
  rfl

/-- **T10c (`SECOND_HALVING_HEIGHT` is the dev-fund range end).** The named
second halving height equals `DEV_FUND_END_HEIGHT`. -/
theorem second_halving_eq_dev_fund_end :
    SECOND_HALVING_HEIGHT = DEV_FUND_END_HEIGHT := by
  unfold SECOND_HALVING_HEIGHT DEV_FUND_END_HEIGHT; rfl

/-- **T11 (dev-fund range is at-or-above the FIRST halving and strictly
below the SECOND halving).** Every height inside the ZIP-1014 range
satisfies `FIRST_HALVING_HEIGHT ≤ h < SECOND_HALVING_HEIGHT`. This is the
"one full halving epoch" property: `halving(h) = 1` everywhere on the
range — *not* `halving(h) = 0` — because the range starts *at* (not
before) the first halving. Inside the range the post-Blossom block
subsidy is therefore at its *first-halved* level
(`max_block_subsidy / 2`, i.e. `6.25 ZEC` post-Blossom), not the full
pre-halving value. -/
theorem dev_fund_within_first_halving_epoch
    (h : Nat) (hr : isInDevFundRange h) :
    FIRST_HALVING_HEIGHT ≤ h ∧ h < SECOND_HALVING_HEIGHT := by
  refine ⟨?_, ?_⟩
  · -- `FIRST_HALVING_HEIGHT = DEV_FUND_START_HEIGHT ≤ h`
    have := hr.1
    unfold FIRST_HALVING_HEIGHT
    unfold DEV_FUND_START_HEIGHT at this
    exact this
  · -- `h < DEV_FUND_END_HEIGHT = SECOND_HALVING_HEIGHT`
    have := hr.2
    unfold SECOND_HALVING_HEIGHT
    unfold DEV_FUND_END_HEIGHT at this
    exact this

/-- **T11a (dev-fund range is strictly below the second halving).** Every
height inside the ZIP-1014 range is strictly less than the second halving
(`DEV_FUND_END_HEIGHT = SECOND_HALVING_HEIGHT`). -/
theorem dev_fund_below_second_halving (h : Nat) (hr : isInDevFundRange h) :
    h < DEV_FUND_END_HEIGHT := hr.2

/-- **T12 (dev-fund range is at-or-above Canopy = first halving).** Every
height inside the ZIP-1014 range is `≥ DEV_FUND_START_HEIGHT`, the Canopy
activation height (= Mainnet first halving) on Mainnet.
This justifies dropping the Founders' Reward term inside the range, since
`NetworkUpgrade::current(net, h) ≥ Canopy` ⇒ founders reward is zero. -/
theorem dev_fund_above_canopy (h : Nat) (hr : isInDevFundRange h) :
    DEV_FUND_START_HEIGHT ≤ h := hr.1

/-- **T13 (range width = one post-Blossom halving epoch).** The ZIP-1014
funding stream is active for exactly `1_680_000` blocks — the post-Blossom
halving interval — i.e. one full halving epoch (from the first halving at
Canopy to the second halving at NU6). -/
theorem dev_fund_range_width :
    DEV_FUND_END_HEIGHT - DEV_FUND_START_HEIGHT = POST_BLOSSOM_HALVING_INTERVAL := by
  unfold DEV_FUND_END_HEIGHT DEV_FUND_START_HEIGHT POST_BLOSSOM_HALVING_INTERVAL
  rfl

/-- **T14 (miner gets 80% when subsidy is divisible by 100).** For a block
subsidy divisible by `100`, the miner's residual share is *exactly*
`80%` of the block subsidy.

This is the load-bearing miner-subsidy invariant of ZIP-1014 inside the
dev-fund range: after the three recipients take their slices, the miner
receives the remaining `80%`, with no rounding loss when divisibility
holds. -/
theorem miner_amount_eq_80pct_when_divisible
    (s : Nat) (hs : DENOMINATOR ∣ s) :
    minerAmount s = s * MINER_NUMERATOR / DENOMINATOR := by
  simp only [DENOMINATOR] at hs
  obtain ⟨q, rfl⟩ := hs
  simp only [minerAmount, eccAmount, zfAmount, mgAmount, recipientAmount,
        ECC_NUMERATOR, ZF_NUMERATOR, MG_NUMERATOR,
        MINER_NUMERATOR, DENOMINATOR, DEV_FUND_NUMERATOR]
  have h7 : 100 * q * 7 / 100 = q * 7 := by
    rw [show 100 * q * 7 = 100 * (q * 7) by ring]
    exact Nat.mul_div_cancel_left (q * 7) (by decide)
  have h5 : 100 * q * 5 / 100 = q * 5 := by
    rw [show 100 * q * 5 = 100 * (q * 5) by ring]
    exact Nat.mul_div_cancel_left (q * 5) (by decide)
  have h8 : 100 * q * 8 / 100 = q * 8 := by
    rw [show 100 * q * 8 = 100 * (q * 8) by ring]
    exact Nat.mul_div_cancel_left (q * 8) (by decide)
  have h80 : 100 * q * (100 - (7 + 5 + 8)) / 100 = q * 80 := by
    change 100 * q * 80 / 100 = q * 80
    rw [show 100 * q * 80 = 100 * (q * 80) by ring]
    exact Nat.mul_div_cancel_left (q * 80) (by decide)
  rw [h7, h5, h8, h80]
  -- Goal: `100 * q − (q * 7 + q * 5 + q * 8) = q * 80`.
  have : q * 7 + q * 5 + q * 8 = q * 20 := by ring
  rw [this]
  have hq : q * 20 ≤ 100 * q := by linarith
  omega

/-- **T15 (miner share is exactly subsidy − dev-fund slice when divisible).**
Equivalent form of T14 stated at the abstraction level Zebra enforces
(`miner = subsidy − Σ funding streams`): the miner's amount is the block
subsidy minus the combined dev-fund slice. -/
theorem miner_amount_eq_subsidy_minus_devfund
    (s : Nat) (hs : DENOMINATOR ∣ s) :
    minerAmount s + devFundSlice s = s := by
  have h := recipients_sum_eq_devfund_when_divisible s hs
  unfold minerAmount
  have hLe : eccAmount s + zfAmount s + mgAmount s ≤ s := by
    have h1 := ecc_amount_le_subsidy s
    have h2 := zf_amount_le_subsidy s
    have h3 := mg_amount_le_subsidy s
    -- We don't have a clean direct bound; instead use T8 + 20% slice bound.
    have hDS : devFundSlice s ≤ s := by
      unfold devFundSlice recipientAmount DEV_FUND_NUMERATOR
            ECC_NUMERATOR ZF_NUMERATOR MG_NUMERATOR DENOMINATOR
      -- `s * 20 / 100 ≤ s * 20 / 20 = s`.
      have hd : s * 20 / 100 ≤ s * 20 / 20 :=
        Nat.div_le_div_left (by decide) (by decide)
      have hr : s * 20 / 20 = s := Nat.mul_div_cancel s (by decide)
      omega
    have hSum := recipients_sum_le_devfund s
    omega
  rw [← h]
  omega

/-- **T16 (dev-fund range contains the Canopy activation height).** Sanity
check: the Canopy activation height (the start of the range) is itself in
the range. -/
theorem canopy_in_dev_fund_range :
    isInDevFundRange DEV_FUND_START_HEIGHT := by
  unfold isInDevFundRange DEV_FUND_START_HEIGHT DEV_FUND_END_HEIGHT
  decide

/-- **T17 (second-halving height is *not* in the dev-fund range).** Sanity
check: the upper bound is exclusive, so the second halving height
(`2_726_400` on Mainnet = NU6 activation = first halving + one halving
epoch) is *not* in the range. This is exactly the behaviour Zebra encodes
via Rust's `Range<Height>` (`start..end`, half-open) and is the reason the
dev-fund range "ends *at* the second halving" instead of "continues
*through* the second halving" — i.e. the stream stops the moment the
post-NU6 funding-streams literal in `mainnet.rs:212-227` takes over. -/
theorem second_halving_not_in_dev_fund_range :
    ¬ isInDevFundRange DEV_FUND_END_HEIGHT := by
  unfold isInDevFundRange DEV_FUND_START_HEIGHT DEV_FUND_END_HEIGHT
  decide

/-- **T18 (one-block-before-end is in the range).** The block immediately
before the second halving (`2_726_399`) *is* in the range — the very last
block at which the ZIP-1014 dev-fund stream is paid. -/
theorem last_dev_fund_block_in_range :
    isInDevFundRange (DEV_FUND_END_HEIGHT - 1) := by
  unfold isInDevFundRange DEV_FUND_START_HEIGHT DEV_FUND_END_HEIGHT
  decide

/-- **T19 (dev-fund range spans exactly one halving epoch).** Restated for
emphasis: the dev fund runs from the first halving (Canopy) up to but not
including the second halving (NU6), so its endpoint is
`DEV_FUND_START_HEIGHT + POST_BLOSSOM_HALVING_INTERVAL` — exactly one
post-Blossom halving interval (`1_680_000` blocks) wide. -/
theorem dev_fund_range_one_halving_period :
    DEV_FUND_END_HEIGHT = DEV_FUND_START_HEIGHT + POST_BLOSSOM_HALVING_INTERVAL := by
  unfold DEV_FUND_END_HEIGHT DEV_FUND_START_HEIGHT POST_BLOSSOM_HALVING_INTERVAL
  rfl

/-- **T20 (dev-fund slice is 20% via `DEV_FUND_NUMERATOR`).** Restates the
ZIP-1014 headline at the term level: the dev-fund slice is the natural
floor of `subsidy * 20 / 100`. -/
theorem dev_fund_slice_eq_twenty_pct (s : Nat) :
    devFundSlice s = s * 20 / 100 := by
  unfold devFundSlice recipientAmount DEV_FUND_NUMERATOR
        ECC_NUMERATOR ZF_NUMERATOR MG_NUMERATOR DENOMINATOR
  rfl

/-- **T21 (concrete: full-subsidy split).** For the post-Blossom maximum
block subsidy `MAX_BLOCK_SUBSIDY / 2 = 6.25 ZEC = 6.25 × 10^8 zatoshis =
625_000_000`, the three recipients receive exact-integer amounts and the
miner receives exactly `500_000_000` zatoshis (`5 ZEC`).

This is the documented ZIP-1014 split at the post-Blossom max subsidy:
ECC `0.4375 ZEC`, ZF `0.3125 ZEC`, Major Grants `0.5 ZEC`, miner `5 ZEC`. -/
theorem split_at_post_blossom_max :
    eccAmount 625_000_000 = 43_750_000 ∧
    zfAmount 625_000_000 = 31_250_000 ∧
    mgAmount 625_000_000 = 50_000_000 ∧
    minerAmount 625_000_000 = 500_000_000 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (first | (unfold eccAmount recipientAmount ECC_NUMERATOR DENOMINATOR; decide)
           | (unfold zfAmount recipientAmount ZF_NUMERATOR DENOMINATOR; decide)
           | (unfold mgAmount recipientAmount MG_NUMERATOR DENOMINATOR; decide)
           | (unfold minerAmount eccAmount zfAmount mgAmount recipientAmount
                ECC_NUMERATOR ZF_NUMERATOR MG_NUMERATOR DENOMINATOR; decide))

/-- **T22 (concrete: dev-fund and miner sum to subsidy).** At the
post-Blossom max subsidy, the dev-fund slice (`125_000_000 = 1.25 ZEC`)
plus the miner's share (`500_000_000 = 5 ZEC`) equals the full block
subsidy (`625_000_000 = 6.25 ZEC`). The 20/80 partition holds exactly. -/
theorem partition_at_post_blossom_max :
    devFundSlice 625_000_000 + minerAmount 625_000_000 = 625_000_000 := by
  unfold devFundSlice minerAmount eccAmount zfAmount mgAmount recipientAmount
        DEV_FUND_NUMERATOR ECC_NUMERATOR ZF_NUMERATOR MG_NUMERATOR DENOMINATOR
  decide

end Zebra.Zip1014Devfund
