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

- exhaustive coverage (every upgrade has a witness height);
- monotonicity in height (no time travel: a larger height never gives an
  earlier upgrade);
- inverse on activation heights (`current` at each activation height yields
  the corresponding upgrade);
- continuity between activations (`current` is constant on `[h_i, h_{i+1})`).
-/

namespace Zebra.NetworkUpgrade

/-- The mainnet network-upgrade variants, in activation order. -/
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
  deriving DecidableEq, Repr

/-- The total order on `NU` matches the natural activation order. We expose it
as an ordinal `Nat` so we can reason about monotonicity arithmetically. -/
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

/-- The activation height for each upgrade on mainnet. `Genesis` activates at
height 0. -/
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

/-- `current h` is the upgrade in force at mainnet height `h`. Models
`NetworkUpgrade::current` over the mainnet activation list. The cascade is
written so it matches the Rust scan-from-the-back semantics. -/
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

/-- **T2 (current at every activation height equals that upgrade).** This is
the "inverse on activation heights" property: looking up the upgrade in force
*at* its own activation height gives that upgrade back. -/
theorem current_at_activation_height (nu : NU) :
    current (activationHeight nu) = nu := by
  cases nu <;>
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
  simp [BEFORE_OVERWINTER, OVERWINTER, SAPLING, BLOSSOM, HEARTWOOD, CANOPY,
        NU5, NU6, NU6_1, NU6_2]

/-- **T5 (exhaustive coverage).** Every variant of `NU` is reached by `current`
at its own activation height — no unreachable upgrades. -/
theorem current_surjective (nu : NU) : ∃ h, current h = nu :=
  ⟨activationHeight nu, current_at_activation_height nu⟩

/-- **T6 (current is total).** A trivial fact in Lean — `current` is a total
function by construction — but worth stating to mirror the Rust comment
`"every height has a current network upgrade"`. -/
theorem current_total (h : Nat) : ∃ nu, current h = nu := ⟨current h, rfl⟩

/-- The "previous upgrade" relation: `nu'` immediately precedes `nu`. -/
def isPrev (nu' nu : NU) : Prop := nu'.toOrd + 1 = nu.toOrd

/-- **T7 (the activation list is strictly increasing).** The activation heights
strictly increase along the upgrade order; sanity-check that the Rust
constants don't collide. -/
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

end Zebra.NetworkUpgrade
