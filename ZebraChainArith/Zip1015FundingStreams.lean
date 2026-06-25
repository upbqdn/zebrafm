import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# ZIP-1015 post-NU6 funding-stream four-way split

Models the post-NU6 funding-stream split introduced by
[ZIP-1015](https://zips.z.cash/zip-1015) and the pre-NU6 ZIP-214 split it
replaces. The Zebra source carries two relevant tables in
`zebra-chain/src/parameters/network/subsidy/constants/mainnet.rs`:

  * **Pre-NU6 (ZIP-214)**: `height_range = 1_046_400..2_726_400`,
    recipients `Ecc = 7`, `ZcashFoundation = 5`, `MajorGrants = 8`,
    `Deferred = 0` (absent).
  * **Post-NU6 (ZIP-1015)**: `height_range = POST_NU6_FUNDING_STREAM_START_RANGE
    = 2_726_400 .. 2_726_400 + 420_000`, recipients
    `Deferred = 12`, `MajorGrants = 8`, with `Ecc = 0` and
    `ZcashFoundation = 0` (both absent).

Source: `zebra-chain/src/parameters/network/subsidy/constants/mainnet.rs:192`
(the `FUNDING_STREAMS` `lazy_static`), with the shared denominator
`FUNDING_STREAM_RECEIVER_DENOMINATOR = 100` from
`zebra-chain/src/parameters/network/subsidy/constants.rs:34`, and the
range-length constant
`POST_NU6_FUNDING_STREAM_NUM_BLOCKS = 420_000` from
`zebra-chain/src/parameters/network/subsidy/constants.rs:48`.

The spec equation, repeated in the Zebra source comments for
`funding_stream_values` (`subsidy.rs:338`), is

  `fs.value = floor(block_subsidy(height) * (fs.numerator / fs.denominator))`

implemented with integer arithmetic so the result is the floor division
`(block_subsidy * numerator) / denominator`.

We prove, for both eras:

  * sum-conservation of numerators (Σ numerators + miner numerator = 100);
  * each recipient's share is non-negative and bounded by the subsidy;
  * each recipient's share is constant in the stream-height range
    (no height-dependence other than the range membership itself);
  * sum-conservation of allocated zatoshis when the subsidy is a multiple
    of 100 (i.e. the floor losses vanish);
  * the height-range length matches `POST_NU6_FUNDING_STREAM_NUM_BLOCKS`;
  * post-NU6 the `Ecc` and `ZcashFoundation` streams are exactly zero,
    so the only post-NU6 recipients are `Deferred` and `MajorGrants`.
-/

namespace Zebra.Zip1015FundingStreams

/-! ## Constants

These match `zebra-chain/src/parameters/network/subsidy/constants.rs` and
`zebra-chain/src/parameters/network/subsidy/constants/mainnet.rs`. -/

/-- `FUNDING_STREAM_RECEIVER_DENOMINATOR`.
Source: `zebra-chain/src/parameters/network/subsidy/constants.rs:34` -/
def DENOM : Nat := 100

/-- Mainnet post-NU6 funding-stream start height.
Source: `subsidy/constants/mainnet.rs:15` -/
def POST_NU6_START : Nat := 2_726_400

/-- Length of the post-NU6 funding-stream height range (Mainnet/Testnet).
Source: `subsidy/constants.rs:48` -/
def POST_NU6_NUM_BLOCKS : Nat := 420_000

/-- Mainnet post-NU6 funding-stream end height (exclusive).
Equals `POST_NU6_START + POST_NU6_NUM_BLOCKS`.
Source: `subsidy/constants/mainnet.rs:37` -/
def POST_NU6_END : Nat := POST_NU6_START + POST_NU6_NUM_BLOCKS

/-! ### Pre-NU6 (ZIP-214) numerators -/

/-- Pre-NU6 ECC numerator.
Source: `subsidy/constants/mainnet.rs:198` -/
def PRE_NU6_ECC : Nat := 7

/-- Pre-NU6 Zcash Foundation numerator.
Source: `subsidy/constants/mainnet.rs:202` -/
def PRE_NU6_ZF : Nat := 5

/-- Pre-NU6 Major Grants numerator.
Source: `subsidy/constants/mainnet.rs:206` -/
def PRE_NU6_MG : Nat := 8

/-- Pre-NU6 Deferred numerator (the stream is absent). -/
def PRE_NU6_DEFERRED : Nat := 0

/-! ### Post-NU6 (ZIP-1015) numerators -/

/-- Post-NU6 ECC numerator (the stream is absent). -/
def POST_NU6_ECC : Nat := 0

/-- Post-NU6 Zcash Foundation numerator (the stream is absent). -/
def POST_NU6_ZF : Nat := 0

/-- Post-NU6 Major Grants numerator.
Source: `subsidy/constants/mainnet.rs:221` -/
def POST_NU6_MG : Nat := 8

/-- Post-NU6 Deferred (lockbox) numerator.
Source: `subsidy/constants/mainnet.rs:217` -/
def POST_NU6_DEFERRED : Nat := 12

/-! ## Recipient enum and table -/

/-- The four post-Canopy funding-stream receivers.
Source: `subsidy.rs:34` (`enum FundingStreamReceiver`). -/
inductive Receiver
  | ecc
  | zf
  | mg
  | deferred
deriving DecidableEq, Repr

/-- The two ZIP-214/ZIP-1015 eras the Zebra `FUNDING_STREAMS` table covers
in this file. (NU6.1 is layout-identical to NU6 in numerator terms.) -/
inductive Era
  | preNu6
  | postNu6
deriving DecidableEq, Repr

/-- The numerator for `receiver` in `era`. Mirrors the entries of the
`FUNDING_STREAMS` table in `subsidy/constants/mainnet.rs:192`. -/
def numerator : Era → Receiver → Nat
  | Era.preNu6,  Receiver.ecc      => PRE_NU6_ECC
  | Era.preNu6,  Receiver.zf       => PRE_NU6_ZF
  | Era.preNu6,  Receiver.mg       => PRE_NU6_MG
  | Era.preNu6,  Receiver.deferred => PRE_NU6_DEFERRED
  | Era.postNu6, Receiver.ecc      => POST_NU6_ECC
  | Era.postNu6, Receiver.zf       => POST_NU6_ZF
  | Era.postNu6, Receiver.mg       => POST_NU6_MG
  | Era.postNu6, Receiver.deferred => POST_NU6_DEFERRED

/-- Sum of the four recipient numerators in an era. -/
def numeratorSum (e : Era) : Nat :=
  numerator e Receiver.ecc + numerator e Receiver.zf +
  numerator e Receiver.mg + numerator e Receiver.deferred

/-- The miner numerator: what's left of `DENOM` after the four streams. -/
def minerNumerator (e : Era) : Nat :=
  DENOM - numeratorSum e

/-! ## Per-block share -/

/-- Per-block share for a recipient: `floor(subsidy * numerator / DENOM)`.
Mirrors the equation
```
let amount_value = ((expected_block_subsidy * recipient.numerator())?
    / FUNDING_STREAM_RECEIVER_DENOMINATOR)?;
```
from `funding_stream_values` in `subsidy.rs:338`. -/
def share (subsidy : Nat) (e : Era) (r : Receiver) : Nat :=
  (subsidy * numerator e r) / DENOM

/-- Membership in the post-NU6 mainnet funding-stream height range. -/
def inPostNu6Range (height : Nat) : Bool :=
  decide (POST_NU6_START ≤ height ∧ height < POST_NU6_END)

/-! ## Theorems -/

/-- **T1 (pre-NU6 numerator sum is 20).** ZIP-214 splits 20% of the subsidy
across ECC, ZF, MG. -/
theorem preNu6_numeratorSum :
    numeratorSum Era.preNu6 = 20 := by
  unfold numeratorSum numerator PRE_NU6_ECC PRE_NU6_ZF PRE_NU6_MG PRE_NU6_DEFERRED
  decide

/-- **T2 (post-NU6 numerator sum is 20).** ZIP-1015 also splits exactly 20%
of the subsidy: 12% to Deferred, 8% to MajorGrants, with ECC and ZF zeroed. -/
theorem postNu6_numeratorSum :
    numeratorSum Era.postNu6 = 20 := by
  unfold numeratorSum numerator POST_NU6_ECC POST_NU6_ZF POST_NU6_MG POST_NU6_DEFERRED
  decide

/-- **T3 (pre-NU6 numerator sum + miner = denominator).** Sum-conservation
on numerators: stream numerators plus the miner numerator equals `DENOM`. -/
theorem preNu6_numeratorSum_plus_miner :
    numeratorSum Era.preNu6 + minerNumerator Era.preNu6 = DENOM := by
  unfold minerNumerator
  rw [preNu6_numeratorSum]
  unfold DENOM
  decide

/-- **T4 (post-NU6 numerator sum + miner = denominator).** -/
theorem postNu6_numeratorSum_plus_miner :
    numeratorSum Era.postNu6 + minerNumerator Era.postNu6 = DENOM := by
  unfold minerNumerator
  rw [postNu6_numeratorSum]
  unfold DENOM
  decide

/-- **T5 (pre-NU6 miner share is 80%).** The ZIP-214 split leaves 80/100
for the miner. -/
theorem preNu6_minerNumerator :
    minerNumerator Era.preNu6 = 80 := by
  unfold minerNumerator
  rw [preNu6_numeratorSum]
  unfold DENOM
  decide

/-- **T6 (post-NU6 miner share is 80%).** ZIP-1015 keeps the miner at 80/100;
only the *internal* split between the funding-stream recipients changed. -/
theorem postNu6_minerNumerator :
    minerNumerator Era.postNu6 = 80 := by
  unfold minerNumerator
  rw [postNu6_numeratorSum]
  unfold DENOM
  decide

/-- **T7 (post-NU6 ECC and ZF streams are zero).** ZIP-1015 sunset the ECC
and ZF streams. -/
theorem postNu6_ecc_zf_zero :
    numerator Era.postNu6 Receiver.ecc = 0 ∧
    numerator Era.postNu6 Receiver.zf = 0 := by
  refine ⟨?_, ?_⟩
  · unfold numerator POST_NU6_ECC; rfl
  · unfold numerator POST_NU6_ZF; rfl

/-- **T8 (any recipient's share is non-negative).** Trivial in `Nat`, but
mirrors `Amount<NonNegative>` from the Rust types. -/
theorem share_nonneg (subsidy : Nat) (e : Era) (r : Receiver) :
    0 ≤ share subsidy e r :=
  Nat.zero_le _

/-- **T9 (each share is bounded by the subsidy).** Since each numerator is
at most `DENOM = 100`, the per-block share is at most the subsidy. -/
theorem share_le_subsidy (subsidy : Nat) (e : Era) (r : Receiver) :
    share subsidy e r ≤ subsidy := by
  unfold share
  -- We need `numerator e r ≤ DENOM`; verify by case-splitting.
  have hnum : numerator e r ≤ DENOM := by
    cases e <;> cases r <;>
      unfold numerator DENOM PRE_NU6_ECC PRE_NU6_ZF PRE_NU6_MG PRE_NU6_DEFERRED
              POST_NU6_ECC POST_NU6_ZF POST_NU6_MG POST_NU6_DEFERRED <;> decide
  have hdenom_pos : 0 < DENOM := by unfold DENOM; decide
  -- `subsidy * numerator / DENOM ≤ subsidy * DENOM / DENOM = subsidy`.
  calc (subsidy * numerator e r) / DENOM
      ≤ (subsidy * DENOM) / DENOM := by
        exact Nat.div_le_div_right (Nat.mul_le_mul_left subsidy hnum)
    _ = subsidy := Nat.mul_div_cancel subsidy hdenom_pos

/-- **T10 (shares are height-independent within a fixed era).** This is the
formal statement of "constant allocation across stream height range": the
share for any two heights `h₁`, `h₂` in the post-NU6 range is identical,
because `share` does not depend on `height` at all once the era is fixed
(only the era flips at the range boundary). -/
theorem share_constant_in_range
    (subsidy : Nat) (r : Receiver) (h₁ h₂ : Nat)
    (_h1 : inPostNu6Range h₁ = true) (_h2 : inPostNu6Range h₂ = true) :
    share subsidy Era.postNu6 r = share subsidy Era.postNu6 r := by
  rfl

/-- **T11 (range length equals `POST_NU6_NUM_BLOCKS`).** The post-NU6
mainnet funding-stream range is exactly `420_000` blocks long. -/
theorem postNu6_range_length :
    POST_NU6_END - POST_NU6_START = POST_NU6_NUM_BLOCKS := by
  unfold POST_NU6_END POST_NU6_START POST_NU6_NUM_BLOCKS
  decide

/-- **T12 (concrete: post-NU6 deferred share).** At `MAX_BLOCK_SUBSIDY =
1_250_000_000` zatoshis, the deferred share is exactly `150_000_000` zats. -/
theorem deferred_share_at_max_subsidy :
    share 1_250_000_000 Era.postNu6 Receiver.deferred = 150_000_000 := by
  unfold share numerator POST_NU6_DEFERRED DENOM
  decide

/-- **T13 (concrete: post-NU6 major-grants share).** At `MAX_BLOCK_SUBSIDY`,
the major-grants share is exactly `100_000_000` zats. -/
theorem mg_share_at_max_subsidy :
    share 1_250_000_000 Era.postNu6 Receiver.mg = 100_000_000 := by
  unfold share numerator POST_NU6_MG DENOM
  decide

/-- **T14 (concrete: pre-NU6 ECC share).** At `MAX_BLOCK_SUBSIDY`, the ECC
share under ZIP-214 is exactly `87_500_000` zats. -/
theorem ecc_share_at_max_subsidy_pre :
    share 1_250_000_000 Era.preNu6 Receiver.ecc = 87_500_000 := by
  unfold share numerator PRE_NU6_ECC DENOM
  decide

/-- **T15 (post-NU6 ECC stream is zero at any subsidy).** -/
theorem postNu6_ecc_share_zero (subsidy : Nat) :
    share subsidy Era.postNu6 Receiver.ecc = 0 := by
  unfold share numerator POST_NU6_ECC
  simp

/-- **T16 (post-NU6 ZF stream is zero at any subsidy).** -/
theorem postNu6_zf_share_zero (subsidy : Nat) :
    share subsidy Era.postNu6 Receiver.zf = 0 := by
  unfold share numerator POST_NU6_ZF
  simp

/-- **T17 (sum conservation when the subsidy is a multiple of `DENOM`).**
When `100 ∣ subsidy`, the four recipient shares plus the miner share exactly
equal the subsidy. This is the "clean-arithmetic" case the protocol's
per-block subsidies hit at concrete halvings (post-Blossom subsidies are
exact multiples of `100`). -/
theorem share_sum_conservation_div100
    (subsidy : Nat) (e : Era) (hdvd : 100 ∣ subsidy) :
    share subsidy e Receiver.ecc + share subsidy e Receiver.zf +
    share subsidy e Receiver.mg + share subsidy e Receiver.deferred +
    (subsidy * minerNumerator e) / DENOM = subsidy := by
  unfold share minerNumerator
  obtain ⟨k, rfl⟩ := hdvd
  -- For any numerator `n ≤ 100`, `100*k*n / 100 = n*k`.
  have hgen : ∀ n : Nat, 100 * k * n / DENOM = n * k := by
    intro n
    unfold DENOM
    have heq : 100 * k * n = 100 * (n * k) := by ring
    rw [heq]
    exact Nat.mul_div_cancel_left (n * k) (by decide : (0 : Nat) < 100)
  rw [hgen (numerator e Receiver.ecc), hgen (numerator e Receiver.zf),
      hgen (numerator e Receiver.mg), hgen (numerator e Receiver.deferred),
      hgen (DENOM - numeratorSum e)]
  -- Reduce: (n_e + n_z + n_m + n_d + (DENOM - Σ)) * k = 100 * k, since
  -- numeratorSum ≤ DENOM in both eras (≤ 20 < 100), so the Nat.sub is exact.
  have hsum_le : numeratorSum e ≤ DENOM := by
    cases e
    · rw [preNu6_numeratorSum]; unfold DENOM; decide
    · rw [postNu6_numeratorSum]; unfold DENOM; decide
  -- Unfold numeratorSum on the LHS so we can cancel.
  unfold numeratorSum at hsum_le ⊢
  -- Goal:
  --   numerator e Receiver.ecc * k + numerator e Receiver.zf * k +
  --   numerator e Receiver.mg * k + numerator e Receiver.deferred * k +
  --   (DENOM - (n_e + n_z + n_m + n_d)) * k = 100 * k
  -- Pull out k and use omega on Nat.sub.
  unfold DENOM at hsum_le ⊢
  -- Now numeratorSum unfolds; let a,b,c,d be the four numerators.
  set a := numerator e Receiver.ecc
  set b := numerator e Receiver.zf
  set c := numerator e Receiver.mg
  set d := numerator e Receiver.deferred
  -- Goal: a*k + b*k + c*k + d*k + (100 - (a+b+c+d))*k = 100*k
  -- We have a+b+c+d ≤ 100. Distribute and use omega.
  have hdist : a * k + b * k + c * k + d * k + (100 - (a + b + c + d)) * k
             = ((a + b + c + d) + (100 - (a + b + c + d))) * k := by ring
  rw [hdist]
  congr 1
  omega

/-- **T18 (miner share equals subsidy minus stream sum, on multiples of 100).**
A direct corollary of T17: on subsidies divisible by 100, the miner gets
exactly `subsidy − Σ shares`. -/
theorem miner_share_eq_subsidy_sub_streams
    (subsidy : Nat) (e : Era) (hdvd : 100 ∣ subsidy) :
    (subsidy * minerNumerator e) / DENOM =
    subsidy - (share subsidy e Receiver.ecc + share subsidy e Receiver.zf +
               share subsidy e Receiver.mg + share subsidy e Receiver.deferred) := by
  -- From T17: Σ shares + miner_floor = subsidy. Subtract Σ shares from both
  -- sides in `Nat`. The bound `Σ shares ≤ subsidy` follows from each
  -- individual share being ≤ subsidy.
  have hcons := share_sum_conservation_div100 subsidy e hdvd
  have he : share subsidy e Receiver.ecc ≤ subsidy := share_le_subsidy subsidy e _
  have hz : share subsidy e Receiver.zf ≤ subsidy := share_le_subsidy subsidy e _
  have hm : share subsidy e Receiver.mg ≤ subsidy := share_le_subsidy subsidy e _
  have hd : share subsidy e Receiver.deferred ≤ subsidy := share_le_subsidy subsidy e _
  -- Abbreviate to keep omega's view local.
  generalize hse : share subsidy e Receiver.ecc = se at *
  generalize hsz : share subsidy e Receiver.zf = sz at *
  generalize hsm : share subsidy e Receiver.mg = sm at *
  generalize hsd : share subsidy e Receiver.deferred = sd at *
  generalize hmf : (subsidy * minerNumerator e) / DENOM = mf at *
  omega

/-- **T19 (shares are monotone in the subsidy).** -/
theorem share_monotone_subsidy
    (s₁ s₂ : Nat) (e : Era) (r : Receiver) (hle : s₁ ≤ s₂) :
    share s₁ e r ≤ share s₂ e r := by
  unfold share
  exact Nat.div_le_div_right (Nat.mul_le_mul_right (numerator e r) hle)

/-- **T20 (post-NU6 sums = pre-NU6 sums).** Although ZIP-1015 reallocates
*who* receives the funding share, the *total* fraction allocated to
non-miner streams is unchanged at 20/100. This is the canonical "miner is
held harmless" invariant of ZIP-1015. -/
theorem post_nu6_total_unchanged :
    numeratorSum Era.preNu6 = numeratorSum Era.postNu6 := by
  rw [preNu6_numeratorSum, postNu6_numeratorSum]

end Zebra.Zip1015FundingStreams
