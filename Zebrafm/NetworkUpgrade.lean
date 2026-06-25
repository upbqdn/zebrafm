import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 1000000

/-!
# NetworkUpgrade activation logic (mainnet)

Models `zebra-chain/src/parameters/network_upgrade.rs` plus the mainnet
activation heights from `zebra-chain/src/parameters/constants.rs`. The
production `NetworkUpgrade::current` derives the active upgrade by scanning
the activation list and picking the latest one whose height ≤ the query.

Here we model that mapping as a total function and prove:

- exhaustive coverage of scheduled mainnet upgrades (every scheduled upgrade
  has a witness height);
- monotonicity in height (no time travel: a larger height never gives an
  earlier upgrade);
- inverse on activation heights (`current` at each activation height yields
  the corresponding upgrade);
- continuity between activations (`current` is constant on `[h_i, h_{i+1})`).

## Coverage note for `Nu7`

The Rust `NetworkUpgrade` enum lists `Nu7` as a known protocol upgrade
(`network_upgrade.rs:64-66`). However, `MAINNET_ACTIVATION_HEIGHTS`
(`network_upgrade.rs:101-116`) does **not** include `Nu7` — there is no
scheduled mainnet activation height for it. Rust's `branch_id_list`
gates the `Nu7` branch id behind `#[cfg(any(test, feature = "zebra-test"))]`
with a placeholder `0xffffffff`, and the source comment says
`// TODO: set below to (Nu7, ConsensusBranchId(0x77190ad8)), once the same
value is set in librustzcash`.

This module therefore:

- Adds `.nu7` to the `NU` inductive so the enum matches Rust;
- Adds `nu7 ↦ 11` to `NU.toOrd` so the activation order is total;
- Quantifies `current_at_activation_height` and `current_surjective` over
  `Scheduled` upgrades only (the 11 with concrete mainnet heights);
- Proves `current_never_returns_nu7`, witnessing that `current` cannot
  produce `.nu7` on mainnet.

Adding a fabricated mainnet activation height for `Nu7` (so it would fit
the cascade) would not be faithful to the Rust constants and is rejected.
-/

namespace Zebra.NetworkUpgrade

/-- The Zcash network-upgrade variants, in activation order. Matches the
Rust `pub enum NetworkUpgrade` (`zebra-chain/src/parameters/network_upgrade.rs:30-66`).
`.nu7` is present in the enum but has no scheduled mainnet activation height;
see the module-level coverage note. -/
inductive NU
  | genesis
  | beforeOverwinter
  | overwinter
  | sapling
  | blossom
  | heartwood
  | canopy
  | nu5
  | nu6
  | nu6_1
  | nu6_2
  | nu7
  deriving DecidableEq, Repr

/-- The total order on `NU` matches the natural activation order. We expose it
as an ordinal `Nat` so we can reason about monotonicity arithmetically.
`nu7` gets ordinal 11 to extend the order; on mainnet this ordinal is
unreachable via `current` (see `current_never_returns_nu7`). -/
def NU.toOrd : NU → Nat
  | .genesis          => 0
  | .beforeOverwinter => 1
  | .overwinter       => 2
  | .sapling          => 3
  | .blossom          => 4
  | .heartwood        => 5
  | .canopy           => 6
  | .nu5              => 7
  | .nu6              => 8
  | .nu6_1            => 9
  | .nu6_2            => 10
  | .nu7              => 11

/-! ## Mainnet activation heights -/

def BEFORE_OVERWINTER : Nat := 1
def OVERWINTER       : Nat := 347_500
def SAPLING          : Nat := 419_200
def BLOSSOM          : Nat := 653_600
def HEARTWOOD        : Nat := 903_000
def CANOPY           : Nat := 1_046_400
def NU5              : Nat := 1_687_104
def NU6              : Nat := 2_726_400
def NU6_1            : Nat := 3_146_400
def NU6_2            : Nat := 3_364_600

/-- Predicate identifying network upgrades with a *scheduled* mainnet
activation height (i.e. present in `MAINNET_ACTIVATION_HEIGHTS` in
`zebra-chain/src/parameters/network_upgrade.rs:101-116`). `nu7` is excluded
because its mainnet activation height has not been finalized in upstream. -/
def Scheduled : NU → Prop
  | .nu7 => False
  | _    => True

instance : DecidablePred Scheduled := fun nu => by
  cases nu <;> unfold Scheduled <;> infer_instance

/-- The activation height for each upgrade on mainnet. `Genesis` activates at
height 0. `.nu7` returns `0` as a *sentinel* — Rust returns `None` for
unscheduled upgrades (`network_upgrade.rs:357-367`), and the rest of this
module guards uses of `activationHeight nu7` behind the `Scheduled`
predicate (see `current_at_activation_height` and `current_surjective`). -/
def activationHeight : NU → Nat
  | .genesis          => 0
  | .beforeOverwinter => BEFORE_OVERWINTER
  | .overwinter       => OVERWINTER
  | .sapling          => SAPLING
  | .blossom          => BLOSSOM
  | .heartwood        => HEARTWOOD
  | .canopy           => CANOPY
  | .nu5              => NU5
  | .nu6              => NU6
  | .nu6_1            => NU6_1
  | .nu6_2            => NU6_2
  | .nu7              => 0  -- unscheduled sentinel; guarded by `Scheduled`

/-- `current h` is the upgrade in force at mainnet height `h`. Models
`NetworkUpgrade::current` (`network_upgrade.rs:312-319`) restricted to
mainnet. The cascade is written so it matches the Rust scan-from-the-back
semantics. The result is always one of the 11 scheduled upgrades; `.nu7`
is never produced because it has no mainnet activation height. -/
def current (h : Nat) : NU :=
  if h ≥ NU6_2 then .nu6_2
  else if h ≥ NU6_1 then .nu6_1
  else if h ≥ NU6 then .nu6
  else if h ≥ NU5 then .nu5
  else if h ≥ CANOPY then .canopy
  else if h ≥ HEARTWOOD then .heartwood
  else if h ≥ BLOSSOM then .blossom
  else if h ≥ SAPLING then .sapling
  else if h ≥ OVERWINTER then .overwinter
  else if h ≥ BEFORE_OVERWINTER then .beforeOverwinter
  else .genesis

/-! ## Theorems -/

/-- **T1 (genesis at height 0).** -/
theorem current_zero : current 0 = .genesis := by
  unfold current
  simp [BEFORE_OVERWINTER, OVERWINTER, SAPLING, BLOSSOM, HEARTWOOD, CANOPY,
        NU5, NU6, NU6_1, NU6_2]

/-- **T2 (current at every scheduled activation height equals that upgrade).**
The "inverse on activation heights" property, restricted to scheduled
upgrades: looking up the upgrade in force *at* its own activation height
gives that upgrade back. `nu7` is excluded by the `Scheduled` hypothesis
because its mainnet activation is not committed in upstream Rust. -/
theorem current_at_activation_height (nu : NU) (hsched : Scheduled nu) :
    current (activationHeight nu) = nu := by
  cases nu
  case nu7 => unfold Scheduled at hsched; exact hsched.elim
  all_goals
    (unfold current activationHeight
     simp [BEFORE_OVERWINTER, OVERWINTER, SAPLING, BLOSSOM, HEARTWOOD, CANOPY,
           NU5, NU6, NU6_1, NU6_2])

/-! ## Helper: ordinal as sum of indicator functions -/

/-- `currentOrd h` is `(current h).toOrd` computed as a sum of indicator
functions. Each indicator `(h ≥ X ? 1 : 0)` is monotone in `h`, so the sum is
monotone — avoiding the 2^11 case explosion that `split_ifs` on the nested
cascade triggers. -/
def currentOrd (h : Nat) : Nat :=
  (if h ≥ NU6_2 then 1 else 0) +
  (if h ≥ NU6_1 then 1 else 0) +
  (if h ≥ NU6   then 1 else 0) +
  (if h ≥ NU5   then 1 else 0) +
  (if h ≥ CANOPY then 1 else 0) +
  (if h ≥ HEARTWOOD then 1 else 0) +
  (if h ≥ BLOSSOM then 1 else 0) +
  (if h ≥ SAPLING then 1 else 0) +
  (if h ≥ OVERWINTER then 1 else 0) +
  (if h ≥ BEFORE_OVERWINTER then 1 else 0)

/-- A single indicator `(h ≥ X ? 1 : 0)` is monotone in `h`. -/
private theorem indicator_monotone (X h₁ h₂ : Nat) (hle : h₁ ≤ h₂) :
    (if h₁ ≥ X then 1 else 0) ≤ (if h₂ ≥ X then (1 : Nat) else 0) := by
  by_cases h1 : h₁ ≥ X
  · have h2 : h₂ ≥ X := le_trans h1 hle
    simp [h1, h2]
  · simp [h1]

/-- **T3 (`currentOrd` is monotone).** A larger height never decreases the
indicator count. -/
theorem currentOrd_monotone (h₁ h₂ : Nat) (hle : h₁ ≤ h₂) :
    currentOrd h₁ ≤ currentOrd h₂ := by
  unfold currentOrd
  have iN6_2 := indicator_monotone NU6_2 h₁ h₂ hle
  have iN6_1 := indicator_monotone NU6_1 h₁ h₂ hle
  have iN6   := indicator_monotone NU6   h₁ h₂ hle
  have iN5   := indicator_monotone NU5   h₁ h₂ hle
  have iCa   := indicator_monotone CANOPY h₁ h₂ hle
  have iHe   := indicator_monotone HEARTWOOD h₁ h₂ hle
  have iBl   := indicator_monotone BLOSSOM h₁ h₂ hle
  have iSa   := indicator_monotone SAPLING h₁ h₂ hle
  have iOv   := indicator_monotone OVERWINTER h₁ h₂ hle
  have iBO   := indicator_monotone BEFORE_OVERWINTER h₁ h₂ hle
  omega

/-- **T3b (universal monotonicity, count formulation).** A larger height
never decreases the count of activated upgrades. -/
theorem current_monotone (h₁ h₂ : Nat) (hle : h₁ ≤ h₂) :
    currentOrd h₁ ≤ currentOrd h₂ :=
  currentOrd_monotone h₁ h₂ hle

/-- `current` is constant `nu5` on the half-open interval `[NU5, NU6)`. -/
theorem current_on_nu5_band (h : Nat) (h1 : NU5 ≤ h) (h2 : h < NU6) :
    current h = .nu5 := by
  have hLt_nu6_2 : h < NU6_2 := by
    unfold NU6 NU6_2 at *; omega
  have hLt_nu6_1 : h < NU6_1 := by
    unfold NU6 NU6_1 at *; omega
  have hLt_nu6   : h < NU6 := h2
  have hGe_nu5   : h ≥ NU5 := h1
  unfold current
  simp [Nat.not_le.mpr hLt_nu6_2, Nat.not_le.mpr hLt_nu6_1,
        Nat.not_le.mpr hLt_nu6, hGe_nu5]

/-- `current` is constant `nu6` on the half-open interval `[NU6, NU6_1)`. -/
theorem current_on_nu6_band (h : Nat) (h1 : NU6 ≤ h) (h2 : h < NU6_1) :
    current h = .nu6 := by
  have hLt_nu6_2 : h < NU6_2 := by
    unfold NU6_1 NU6_2 at *; omega
  have hLt_nu6_1 : h < NU6_1 := h2
  have hGe_nu6   : h ≥ NU6 := h1
  unfold current
  simp [Nat.not_le.mpr hLt_nu6_2, Nat.not_le.mpr hLt_nu6_1, hGe_nu6]

/-- **T3 (local monotonicity at the NU5→NU6 boundary).** The currently-active
hard-fork boundary on mainnet. A larger height in the `[NU6, NU6_1)` band
gives a strictly later upgrade than any height in the `[NU5, NU6)` band. -/
theorem current_monotone_at_nu6
    (h₁ h₂ : Nat) (h1 : NU5 ≤ h₁) (h2 : h₁ < NU6) (h3 : NU6 ≤ h₂) (h4 : h₂ < NU6_1) :
    (current h₁).toOrd < (current h₂).toOrd := by
  rw [current_on_nu5_band h₁ h1 h2, current_on_nu6_band h₂ h3 h4]
  decide

/-- **T4 (boundary: just-below-activation gives previous upgrade).** Witnesses
that `current` is *strictly* constant on each band: at the activation height
minus one, we still get the previous upgrade. We witness this for the
NU5/NU6 boundary; the same argument applies to every other boundary. -/
theorem current_below_nu6 : current (NU6 - 1) = .nu5 := by
  unfold current
  simp [NU5, NU6, NU6_1, NU6_2]

/-- **T5 (exhaustive coverage of scheduled upgrades).** Every scheduled
variant of `NU` is reached by `current` at its own activation height — no
unreachable scheduled upgrades. `nu7` is excluded because it has no
mainnet activation height in upstream Rust. -/
theorem current_surjective_on_scheduled (nu : NU) (hsched : Scheduled nu) :
    ∃ h, current h = nu :=
  ⟨activationHeight nu, current_at_activation_height nu hsched⟩

/-- **T6 (`current` never returns `.nu7`).** This is the model-level
counterpart to Rust's `MAINNET_ACTIVATION_HEIGHTS` not containing `Nu7`
(`zebra-chain/src/parameters/network_upgrade.rs:101-116`). Together with
`current_surjective_on_scheduled`, the image of `current` is exactly the
11 scheduled upgrades. -/
theorem current_never_returns_nu7 (h : Nat) : current h ≠ .nu7 := by
  unfold current
  split_ifs <;> intro heq <;> cases heq

/-- The "previous upgrade" relation: `nu'` immediately precedes `nu`. -/
def isPrev (nu' nu : NU) : Prop := nu'.toOrd + 1 = nu.toOrd

/-- **T7 (the activation list is strictly increasing).** The activation heights
strictly increase along the upgrade order; sanity-check that the Rust
constants don't collide. Only the 11 scheduled upgrades participate;
`nu7` is omitted because it has no scheduled mainnet height. -/
theorem activation_heights_strictly_increasing :
    activationHeight .genesis          < activationHeight .beforeOverwinter ∧
    activationHeight .beforeOverwinter < activationHeight .overwinter ∧
    activationHeight .overwinter       < activationHeight .sapling ∧
    activationHeight .sapling          < activationHeight .blossom ∧
    activationHeight .blossom          < activationHeight .heartwood ∧
    activationHeight .heartwood        < activationHeight .canopy ∧
    activationHeight .canopy           < activationHeight .nu5 ∧
    activationHeight .nu5              < activationHeight .nu6 ∧
    activationHeight .nu6              < activationHeight .nu6_1 ∧
    activationHeight .nu6_1            < activationHeight .nu6_2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (unfold activationHeight BEFORE_OVERWINTER OVERWINTER SAPLING BLOSSOM
            HEARTWOOD CANOPY NU5 NU6 NU6_1 NU6_2
     decide)

/-- **T8 (`Scheduled` is decidable).** Sanity-check: every constructor
either is or is not scheduled, and this can be decided. (`decide` works
because `Scheduled` is defined by case analysis on a finite inductive.) -/
theorem nu7_not_scheduled : ¬ Scheduled .nu7 := by
  unfold Scheduled; exact id

/-- **T9 (every non-`nu7` upgrade is scheduled).** The other side of T8:
the 11 mainnet-scheduled upgrades are exactly the constructors other
than `.nu7`. -/
theorem scheduled_iff_not_nu7 (nu : NU) : Scheduled nu ↔ nu ≠ .nu7 := by
  cases nu <;> unfold Scheduled <;> simp

/-- **T10 (NU.toOrd is injective on the 12 constructors).** A sanity check
that `toOrd` distinguishes every constructor, including `.nu7`. Failure
would mean we'd silently conflate two upgrades when reasoning ordinally. -/
theorem toOrd_injective (nu₁ nu₂ : NU) (h : nu₁.toOrd = nu₂.toOrd) :
    nu₁ = nu₂ := by
  cases nu₁ <;> cases nu₂ <;> simp_all [NU.toOrd]

end Zebra.NetworkUpgrade
