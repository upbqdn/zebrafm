import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# ZIP-1015 post-NU6 funding-stream four-way split

Models the post-NU6 funding-stream split introduced by
[ZIP-1015](https://zips.z.cash/zip-1015), the pre-NU6 ZIP-214 split it
replaces, and the post-NU6.1 continuation. The Zebra source carries three
relevant tables in `zebra-chain/src/parameters/network/subsidy/constants/mainnet.rs`:

  * **Pre-NU6 (ZIP-214)**: `height_range = 1_046_400..2_726_400`,
    recipients `Ecc = 7`, `ZcashFoundation = 5`, `MajorGrants = 8`,
    `Deferred = 0` (absent).
  * **Post-NU6 (ZIP-1015)**: `height_range = POST_NU6_FUNDING_STREAM_START_RANGE
    = 2_726_400 .. 2_726_400 + 420_000 = 3_146_400`, recipients
    `Deferred = 12`, `MajorGrants = 8`, with `Ecc = 0` and
    `ZcashFoundation = 0` (both absent).
  * **Post-NU6.1 (ZIP-1015 continuation)**: `height_range = NU6_1 .. 4_406_400`
    `= 3_146_400 .. 4_406_400`, a range that is **3x longer** than the
    post-NU6 range. Numerators match post-NU6.

Sources:
  * `subsidy/constants/mainnet.rs:192` (the `FUNDING_STREAMS` `lazy_static`),
  * `subsidy/constants.rs:34` (`FUNDING_STREAM_RECEIVER_DENOMINATOR = 100`),
  * `subsidy/constants.rs:48` (`POST_NU6_FUNDING_STREAM_NUM_BLOCKS = 420_000`),
  * `parameters/constants.rs:93` (`mainnet::NU6_1 = 3_146_400`).

The spec equation, repeated in the Zebra source comments for
`funding_stream_values` (`subsidy.rs:338`), is

  `fs.value = floor(block_subsidy(height) * (fs.numerator / fs.denominator))`

implemented with integer arithmetic so the result is the floor division
`(block_subsidy * numerator) / denominator`.

We prove, for all three eras:

  * sum-conservation of numerators (Σ numerators + miner numerator = 100);
  * each recipient's share is non-negative and bounded by the subsidy;
  * each recipient's share is era-determined, so for two heights in the
    same era the per-height share is identical (height-independence
    *within* an era is the audit-meaningful statement, not the trivial
    `share s e r = share s e r`);
  * sum-conservation of allocated zatoshis when the subsidy is a multiple
    of 100 (i.e. the floor losses vanish);
  * the post-NU6 range length is `420_000`, the post-NU6.1 range length is
    `1_260_000`, and they differ by exactly a factor of 3;
  * post-NU6 and post-NU6.1, the `Ecc` and `ZcashFoundation` streams are
    exactly zero, so the only stream recipients are `Deferred` and
    `MajorGrants`.
-/

namespace Zebra.Zip1015FundingStreams

/-! ## Constants

These match `zebra-chain/src/parameters/network/subsidy/constants.rs`,
`zebra-chain/src/parameters/network/subsidy/constants/mainnet.rs`, and
`zebra-chain/src/parameters/constants.rs` (NU6.1 mainnet activation). -/

/-- `FUNDING_STREAM_RECEIVER_DENOMINATOR`.
Source: `zebra-chain/src/parameters/network/subsidy/constants.rs:34` -/
def DENOM : Nat := 100

/-- Mainnet pre-NU6 (ZIP-214) funding-stream start height (= Canopy activation).
Source: `subsidy/constants/mainnet.rs:194` -/
def PRE_NU6_START : Nat := 1_046_400

/-- Mainnet pre-NU6 funding-stream end height (exclusive) (= NU6 activation).
Source: `subsidy/constants/mainnet.rs:194` -/
def PRE_NU6_END : Nat := 2_726_400

/-- Mainnet post-NU6 funding-stream start height (= NU6 activation).
Source: `subsidy/constants/mainnet.rs:15` -/
def POST_NU6_START : Nat := 2_726_400

/-- Length of the post-NU6 funding-stream height range (Mainnet/Testnet).
Source: `subsidy/constants.rs:48` -/
def POST_NU6_NUM_BLOCKS : Nat := 420_000

/-- Mainnet post-NU6 funding-stream end height (exclusive).
Equals `POST_NU6_START + POST_NU6_NUM_BLOCKS = NU6_1` activation.
Source: `subsidy/constants/mainnet.rs:37` -/
def POST_NU6_END : Nat := POST_NU6_START + POST_NU6_NUM_BLOCKS

/-- Mainnet NU6.1 activation height; also the post-NU6.1 funding-stream start.
Source: `parameters/constants.rs:93` (`mainnet::NU6_1`). -/
def POST_NU6_1_START : Nat := 3_146_400

/-- Mainnet post-NU6.1 funding-stream end height (exclusive).
Source: `subsidy/constants/mainnet.rs:229` (literal `Height(4_406_400)`). -/
def POST_NU6_1_END : Nat := 4_406_400

/-- Length of the post-NU6.1 funding-stream height range on Mainnet.
Note this is **3x** the post-NU6 length (`1_260_000 = 3 * 420_000`). -/
def POST_NU6_1_NUM_BLOCKS : Nat := POST_NU6_1_END - POST_NU6_1_START

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

/-! ### Post-NU6 / post-NU6.1 (ZIP-1015) numerators

NU6.1 reuses the post-NU6 numerator allocation; only the address sets and
height ranges change (see `subsidy/constants/mainnet.rs:228`). -/

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

/-! ## Recipient enum and era -/

/-- The four post-Canopy funding-stream receivers.
Source: `subsidy.rs:34` (`enum FundingStreamReceiver`). -/
inductive Receiver
  | ecc
  | zf
  | mg
  | deferred
deriving DecidableEq, Repr

/-- The three ZIP-214/ZIP-1015 eras the Zebra `FUNDING_STREAMS` table
covers in this file. `postNu6` and `postNu6_1` share the same numerator
table but have *different* height ranges. -/
inductive Era
  | preNu6
  | postNu6
  | postNu6_1
deriving DecidableEq, Repr

/-- The numerator for `receiver` in `era`. Mirrors the entries of the
`FUNDING_STREAMS` table in `subsidy/constants/mainnet.rs:192`. -/
def numerator : Era → Receiver → Nat
  | Era.preNu6,    Receiver.ecc      => PRE_NU6_ECC
  | Era.preNu6,    Receiver.zf       => PRE_NU6_ZF
  | Era.preNu6,    Receiver.mg       => PRE_NU6_MG
  | Era.preNu6,    Receiver.deferred => PRE_NU6_DEFERRED
  | Era.postNu6,   Receiver.ecc      => POST_NU6_ECC
  | Era.postNu6,   Receiver.zf       => POST_NU6_ZF
  | Era.postNu6,   Receiver.mg       => POST_NU6_MG
  | Era.postNu6,   Receiver.deferred => POST_NU6_DEFERRED
  | Era.postNu6_1, Receiver.ecc      => POST_NU6_ECC
  | Era.postNu6_1, Receiver.zf       => POST_NU6_ZF
  | Era.postNu6_1, Receiver.mg       => POST_NU6_MG
  | Era.postNu6_1, Receiver.deferred => POST_NU6_DEFERRED

/-- Sum of the four recipient numerators in an era. -/
def numeratorSum (e : Era) : Nat :=
  numerator e Receiver.ecc + numerator e Receiver.zf +
  numerator e Receiver.mg + numerator e Receiver.deferred

/-- The miner numerator: what's left of `DENOM` after the four streams. -/
def minerNumerator (e : Era) : Nat :=
  DENOM - numeratorSum e

/-! ## Per-block share -/

/-- Per-block share for a recipient in a fixed era.
`floor(subsidy * numerator / DENOM)`.

Mirrors the equation
```
let amount_value = ((expected_block_subsidy * recipient.numerator())?
    / FUNDING_STREAM_RECEIVER_DENOMINATOR)?;
```
from `funding_stream_values` in `subsidy.rs:338`. -/
def share (subsidy : Nat) (e : Era) (r : Receiver) : Nat :=
  (subsidy * numerator e r) / DENOM

/-! ### Height-driven dispatch

In Zebra, `funding_stream_values(height, ...)` walks `FUNDING_STREAMS` and
picks the entry whose `height_range` contains `height`. We model that with
`eraAtHeight` and the height-indexed `shareAt`. This makes the
"share is constant across the height range" claim a non-trivial statement
about `shareAt`, not a tautology about `share`. -/

/-- Membership in the pre-NU6 (ZIP-214) mainnet funding-stream height range. -/
def inPreNu6Range (height : Nat) : Bool :=
  decide (PRE_NU6_START ≤ height ∧ height < PRE_NU6_END)

/-- Membership in the post-NU6 mainnet funding-stream height range. -/
def inPostNu6Range (height : Nat) : Bool :=
  decide (POST_NU6_START ≤ height ∧ height < POST_NU6_END)

/-- Membership in the post-NU6.1 mainnet funding-stream height range. -/
def inPostNu6_1Range (height : Nat) : Bool :=
  decide (POST_NU6_1_START ≤ height ∧ height < POST_NU6_1_END)

/-- The era assigned to a height by Zebra's `FUNDING_STREAMS` walk.
`none` if the height is outside every stream range. -/
def eraAtHeight (height : Nat) : Option Era :=
  if PRE_NU6_START ≤ height ∧ height < PRE_NU6_END then some Era.preNu6
  else if POST_NU6_START ≤ height ∧ height < POST_NU6_END then some Era.postNu6
  else if POST_NU6_1_START ≤ height ∧ height < POST_NU6_1_END then some Era.postNu6_1
  else none

/-- Height-driven per-block share. Returns 0 outside any funding-stream
range (`numerator` is undefined on `none`, so we conventionally pay 0). -/
def shareAt (height subsidy : Nat) (r : Receiver) : Nat :=
  match eraAtHeight height with
  | some e => share subsidy e r
  | none   => 0

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

/-- **T2.1 (post-NU6.1 numerator sum is 20).** NU6.1 reuses the post-NU6
allocation. -/
theorem postNu6_1_numeratorSum :
    numeratorSum Era.postNu6_1 = 20 := by
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

/-- **T4.1 (post-NU6.1 numerator sum + miner = denominator).** -/
theorem postNu6_1_numeratorSum_plus_miner :
    numeratorSum Era.postNu6_1 + minerNumerator Era.postNu6_1 = DENOM := by
  unfold minerNumerator
  rw [postNu6_1_numeratorSum]
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

/-- **T6.1 (post-NU6.1 miner share is 80%).** -/
theorem postNu6_1_minerNumerator :
    minerNumerator Era.postNu6_1 = 80 := by
  unfold minerNumerator
  rw [postNu6_1_numeratorSum]
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

/-- **T7.1 (post-NU6.1 ECC and ZF streams are zero).** Inherited from the
post-NU6 allocation. -/
theorem postNu6_1_ecc_zf_zero :
    numerator Era.postNu6_1 Receiver.ecc = 0 ∧
    numerator Era.postNu6_1 Receiver.zf = 0 := by
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

/-- **T10a (`shareAt` is constant within the post-NU6 range).** For any two
heights `h₁`, `h₂` in the post-NU6 range, `shareAt h subsidy r` returns the
same value for both. This is the substantive height-independence claim:
unlike the previous tautological `share s e r = share s e r`, this
statement actually depends on the hypotheses.

Mirrors the Rust loop in `funding_stream_values` that walks
`FUNDING_STREAMS` and uses the entry's `height_range` to dispatch. -/
theorem shareAt_constant_in_postNu6_range
    (subsidy : Nat) (r : Receiver) (h₁ h₂ : Nat)
    (hh1 : inPostNu6Range h₁ = true) (hh2 : inPostNu6Range h₂ = true) :
    shareAt h₁ subsidy r = shareAt h₂ subsidy r := by
  -- Both heights are in [POST_NU6_START, POST_NU6_END), so neither is in
  -- the pre-NU6 range. Reduce `eraAtHeight` for both via `eraAtHeight_postNu6`.
  unfold inPostNu6Range at hh1 hh2
  simp only [decide_eq_true_eq] at hh1 hh2
  obtain ⟨hh1a, hh1b⟩ := hh1
  obtain ⟨hh2a, hh2b⟩ := hh2
  -- Show h₁ is not in pre-NU6 range, so era resolves to postNu6.
  -- PRE_NU6_END = 2_726_400 = POST_NU6_START, so h₁ < PRE_NU6_END
  -- contradicts POST_NU6_START ≤ h₁.
  have hh1a' : 2_726_400 ≤ h₁ := by unfold POST_NU6_START at hh1a; exact hh1a
  have hh2a' : 2_726_400 ≤ h₂ := by unfold POST_NU6_START at hh2a; exact hh2a
  have hnotpre1 : ¬ (PRE_NU6_START ≤ h₁ ∧ h₁ < PRE_NU6_END) := by
    intro ⟨_, hlt⟩
    unfold PRE_NU6_END at hlt
    omega
  have hnotpre2 : ¬ (PRE_NU6_START ≤ h₂ ∧ h₂ < PRE_NU6_END) := by
    intro ⟨_, hlt⟩
    unfold PRE_NU6_END at hlt
    omega
  have hera1 : eraAtHeight h₁ = some Era.postNu6 := by
    unfold eraAtHeight
    rw [if_neg hnotpre1, if_pos ⟨hh1a, hh1b⟩]
  have hera2 : eraAtHeight h₂ = some Era.postNu6 := by
    unfold eraAtHeight
    rw [if_neg hnotpre2, if_pos ⟨hh2a, hh2b⟩]
  unfold shareAt
  rw [hera1, hera2]

/-- **T10b (`shareAt` is constant within the post-NU6.1 range).** Analogous
to T10a for the NU6.1 era. -/
theorem shareAt_constant_in_postNu6_1_range
    (subsidy : Nat) (r : Receiver) (h₁ h₂ : Nat)
    (hh1 : inPostNu6_1Range h₁ = true) (hh2 : inPostNu6_1Range h₂ = true) :
    shareAt h₁ subsidy r = shareAt h₂ subsidy r := by
  unfold inPostNu6_1Range at hh1 hh2
  simp only [decide_eq_true_eq] at hh1 hh2
  obtain ⟨hh1a, hh1b⟩ := hh1
  obtain ⟨hh2a, hh2b⟩ := hh2
  -- Show neither h is in pre-NU6 range nor in post-NU6 range.
  have hh1a' : 3_146_400 ≤ h₁ := by unfold POST_NU6_1_START at hh1a; exact hh1a
  have hh2a' : 3_146_400 ≤ h₂ := by unfold POST_NU6_1_START at hh2a; exact hh2a
  have hnotpre1 : ¬ (PRE_NU6_START ≤ h₁ ∧ h₁ < PRE_NU6_END) := by
    intro ⟨_, hlt⟩
    unfold PRE_NU6_END at hlt
    omega
  have hnotpre2 : ¬ (PRE_NU6_START ≤ h₂ ∧ h₂ < PRE_NU6_END) := by
    intro ⟨_, hlt⟩
    unfold PRE_NU6_END at hlt
    omega
  have hnotpost1 : ¬ (POST_NU6_START ≤ h₁ ∧ h₁ < POST_NU6_END) := by
    intro ⟨_, hlt⟩
    unfold POST_NU6_END POST_NU6_START POST_NU6_NUM_BLOCKS at hlt
    omega
  have hnotpost2 : ¬ (POST_NU6_START ≤ h₂ ∧ h₂ < POST_NU6_END) := by
    intro ⟨_, hlt⟩
    unfold POST_NU6_END POST_NU6_START POST_NU6_NUM_BLOCKS at hlt
    omega
  have hera1 : eraAtHeight h₁ = some Era.postNu6_1 := by
    unfold eraAtHeight
    rw [if_neg hnotpre1, if_neg hnotpost1, if_pos ⟨hh1a, hh1b⟩]
  have hera2 : eraAtHeight h₂ = some Era.postNu6_1 := by
    unfold eraAtHeight
    rw [if_neg hnotpre2, if_neg hnotpost2, if_pos ⟨hh2a, hh2b⟩]
  unfold shareAt
  rw [hera1, hera2]

/-- **T10c (`shareAt` is constant within the pre-NU6 range).** -/
theorem shareAt_constant_in_preNu6_range
    (subsidy : Nat) (r : Receiver) (h₁ h₂ : Nat)
    (hh1 : inPreNu6Range h₁ = true) (hh2 : inPreNu6Range h₂ = true) :
    shareAt h₁ subsidy r = shareAt h₂ subsidy r := by
  unfold inPreNu6Range at hh1 hh2
  simp only [decide_eq_true_eq] at hh1 hh2
  obtain ⟨hh1a, hh1b⟩ := hh1
  obtain ⟨hh2a, hh2b⟩ := hh2
  have hera1 : eraAtHeight h₁ = some Era.preNu6 := by
    unfold eraAtHeight
    rw [if_pos ⟨hh1a, hh1b⟩]
  have hera2 : eraAtHeight h₂ = some Era.preNu6 := by
    unfold eraAtHeight
    rw [if_pos ⟨hh2a, hh2b⟩]
  unfold shareAt
  rw [hera1, hera2]

/-- **T11 (range length equals `POST_NU6_NUM_BLOCKS`).** The post-NU6
mainnet funding-stream range is exactly `420_000` blocks long. -/
theorem postNu6_range_length :
    POST_NU6_END - POST_NU6_START = POST_NU6_NUM_BLOCKS := by
  unfold POST_NU6_END POST_NU6_START POST_NU6_NUM_BLOCKS
  decide

/-- **T11.1 (post-NU6.1 range length is `1_260_000`).** -/
theorem postNu6_1_range_length :
    POST_NU6_1_END - POST_NU6_1_START = 1_260_000 := by
  unfold POST_NU6_1_END POST_NU6_1_START
  decide

/-- **T11.2 (post-NU6.1 range is exactly 3x the post-NU6 range).** This is
the *audit-meaningful* statement on the NU6 vs NU6.1 range distinction:
they are not the same length — NU6.1 lasts three full post-NU6 epochs.
The previous model conflated the two. -/
theorem postNu6_1_range_is_3x_postNu6 :
    POST_NU6_1_END - POST_NU6_1_START = 3 * (POST_NU6_END - POST_NU6_START) := by
  unfold POST_NU6_1_END POST_NU6_1_START POST_NU6_END POST_NU6_START POST_NU6_NUM_BLOCKS
  decide

/-- **T11.3 (post-NU6 and post-NU6.1 ranges abut contiguously).** The
post-NU6 range ends precisely where the post-NU6.1 range begins
(at `NU6_1 = 3_146_400`). -/
theorem postNu6_end_eq_postNu6_1_start :
    POST_NU6_END = POST_NU6_1_START := by
  unfold POST_NU6_END POST_NU6_START POST_NU6_NUM_BLOCKS POST_NU6_1_START
  decide

/-- **T11.4 (post-NU6 and post-NU6.1 ranges are disjoint).** No height
falls in both ranges. Follows from contiguous abutment. -/
theorem postNu6_postNu6_1_disjoint (h : Nat) :
    ¬ (inPostNu6Range h = true ∧ inPostNu6_1Range h = true) := by
  intro ⟨h1, h2⟩
  unfold inPostNu6Range at h1
  unfold inPostNu6_1Range at h2
  simp only [decide_eq_true_eq] at h1 h2
  obtain ⟨_, hlt1⟩ := h1
  obtain ⟨hge2, _⟩ := h2
  unfold POST_NU6_END POST_NU6_START POST_NU6_NUM_BLOCKS at hlt1
  unfold POST_NU6_1_START at hge2
  omega

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

/-- **T16.1 (post-NU6.1 ECC and ZF streams are zero at any subsidy).** -/
theorem postNu6_1_ecc_zf_share_zero (subsidy : Nat) :
    share subsidy Era.postNu6_1 Receiver.ecc = 0 ∧
    share subsidy Era.postNu6_1 Receiver.zf = 0 := by
  refine ⟨?_, ?_⟩
  · unfold share numerator POST_NU6_ECC; simp
  · unfold share numerator POST_NU6_ZF; simp

/-- **T17 (sum conservation when the subsidy is a multiple of `DENOM`).**
When `100 ∣ subsidy`, the four recipient shares plus the miner share exactly
equal the subsidy. This is the "clean-arithmetic" case the protocol's
per-block subsidies hit at concrete halvings (post-Blossom subsidies are
exact multiples of `100`). Holds for all three eras. -/
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
  -- numeratorSum ≤ DENOM in all eras (≤ 20 < 100), so the Nat.sub is exact.
  have hsum_le : numeratorSum e ≤ DENOM := by
    cases e
    · rw [preNu6_numeratorSum]; unfold DENOM; decide
    · rw [postNu6_numeratorSum]; unfold DENOM; decide
    · rw [postNu6_1_numeratorSum]; unfold DENOM; decide
  -- Unfold numeratorSum on the LHS so we can cancel.
  unfold numeratorSum at hsum_le ⊢
  unfold DENOM at hsum_le ⊢
  -- Now numeratorSum unfolds; let a,b,c,d be the four numerators.
  set a := numerator e Receiver.ecc
  set b := numerator e Receiver.zf
  set c := numerator e Receiver.mg
  set d := numerator e Receiver.deferred
  -- Goal: a*k + b*k + c*k + d*k + (100 - (a+b+c+d))*k = 100*k
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

/-- **T20 (post-NU6 / post-NU6.1 stream totals equal pre-NU6 stream total).**
Although ZIP-1015 reallocates *who* receives the funding share, the *total*
fraction allocated to non-miner streams is unchanged at 20/100 across all
three eras. This is the canonical "miner is held harmless" invariant of
ZIP-1015 — restated as a per-era equation against the pre-NU6 baseline,
so the proof actually depends on all three numerator tables, not on the
single tautology `20 = 20`. -/
theorem stream_total_unchanged_across_eras :
    (numeratorSum Era.preNu6 = numeratorSum Era.postNu6) ∧
    (numeratorSum Era.preNu6 = numeratorSum Era.postNu6_1) ∧
    (numeratorSum Era.postNu6 = numeratorSum Era.postNu6_1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [preNu6_numeratorSum, postNu6_numeratorSum]
  · rw [preNu6_numeratorSum, postNu6_1_numeratorSum]
  · rw [postNu6_numeratorSum, postNu6_1_numeratorSum]

/-- **T21 (`eraAtHeight` is determined at canonical witness heights).**
Pin the era for a representative height in each range. This validates the
`eraAtHeight` dispatch against the three known `FUNDING_STREAMS` entries. -/
theorem eraAtHeight_witnesses :
    eraAtHeight 1_046_400 = some Era.preNu6 ∧
    eraAtHeight 2_726_400 = some Era.postNu6 ∧
    eraAtHeight 3_146_400 = some Era.postNu6_1 ∧
    eraAtHeight 0 = none ∧
    eraAtHeight 4_406_400 = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals unfold eraAtHeight PRE_NU6_START PRE_NU6_END POST_NU6_START
                  POST_NU6_END POST_NU6_NUM_BLOCKS POST_NU6_1_START POST_NU6_1_END
  all_goals decide

end Zebra.Zip1015FundingStreams
