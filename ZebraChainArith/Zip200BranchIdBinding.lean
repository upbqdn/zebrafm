import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import ZebraChainArith.ConsensusBranchId

/-!
# ZIP-200: consensus branch-id binding for transactions

A transaction is only valid in a block at height `h` if its
`nConsensusBranchId` field equals the branch ID of the network upgrade
active at `h` on that network. This is the "transaction replay
protection" property of ZIP-200: every hard-fork upgrade rotates the
branch ID, so transactions signed under one epoch are unspendable in any
other.

We model:

* `currentBranchId : Nat → Option Nat` — the branch ID of the active
  mainnet upgrade at height `h`, or `none` for pre-Overwinter heights
  (Genesis and BeforeOverwinter have no branch ID).
* `Tx` — an opaque transaction carrying its declared
  `consensusBranchId`.
* `validInBlock tx h` — ZIP-200's binding predicate.

We prove that the binding is decidable, biconditional, that the famous
NU5 branch ID `0xc2d6d0b4` is only accepted inside the NU5/NU6/etc.
activation bands, that pre-Overwinter heights reject every transaction,
and that mismatched branch IDs are rejected.

Sources:
* `zebra-chain/src/parameters/network_upgrade.rs:225` — CONSENSUS_BRANCH_IDS table
* `zebra-chain/src/parameters/network_upgrade.rs:393` — `branch_id()`
* `zebra-chain/src/parameters/network_upgrade.rs:552` — `current()` over height
* `zebra-chain/src/transaction/serialize.rs:683` — `nConsensusBranchId`
  serialized into the V5 header
-/

namespace Zebra.Zip200BranchIdBinding

open Zebra.ConsensusBranchId (NU branchId fromBranchId)

/-! ## Mainnet activation heights

These are duplicated here (rather than imported from `NetworkUpgrade`)
because the `NU` inductive in `ConsensusBranchId` already excludes the
pre-Overwinter upgrades, so we don't want the larger `NU` from
`NetworkUpgrade`. The constants match
`zebra-chain/src/parameters/constants.rs` (mainnet section).
-/

def OVERWINTER : Nat := 347_500
def SAPLING : Nat := 419_200
def BLOSSOM : Nat := 653_600
def HEARTWOOD : Nat := 903_000
def CANOPY : Nat := 1_046_400
def NU5 : Nat := 1_687_104
def NU6 : Nat := 2_726_400
def NU6_1 : Nat := 3_146_400
def NU6_2 : Nat := 3_364_600

/-- The active mainnet upgrade with a branch ID at height `h`, or `none`
for heights below Overwinter (Genesis and BeforeOverwinter epochs have no
branch ID). Models `NetworkUpgrade::current(network, h).branch_id()`
collapsed onto the `NU` subset used in `ConsensusBranchId`.
Source: `zebra-chain/src/parameters/network_upgrade.rs:552` -/
def currentUpgrade (h : Nat) : Option NU :=
  if h ≥ NU6_2 then some .nu6_2
  else if h ≥ NU6_1 then some .nu6_1
  else if h ≥ NU6   then some .nu6
  else if h ≥ NU5   then some .nu5
  else if h ≥ CANOPY then some .canopy
  else if h ≥ HEARTWOOD then some .heartwood
  else if h ≥ BLOSSOM then some .blossom
  else if h ≥ SAPLING then some .sapling
  else if h ≥ OVERWINTER then some .overwinter
  else none

/-- The branch ID of the active mainnet upgrade at height `h`, or `none`
if the height is pre-Overwinter. -/
def currentBranchId (h : Nat) : Option Nat :=
  (currentUpgrade h).map branchId

/-- An opaque-ish model of a transaction: we only care about the
declared `nConsensusBranchId` field that V5+ transactions serialise into
their header.
Source: `zebra-chain/src/transaction/serialize.rs:683` -/
structure Tx where
  consensusBranchId : Nat

/-- ZIP-200 binding: a transaction is valid in a block at height `h`
iff its declared branch ID equals the branch ID of the upgrade in force
at `h`. If the height has no branch ID (pre-Overwinter), the transaction
is invalid regardless of its declared value. -/
def validInBlock (tx : Tx) (h : Nat) : Prop :=
  currentBranchId h = some tx.consensusBranchId

/-! ## Theorems -/

/-- **T1 (decidable binding).** The ZIP-200 validity check is decidable,
which is what makes it implementable as a node-side check. -/
instance validInBlock_decidable (tx : Tx) (h : Nat) :
    Decidable (validInBlock tx h) := by
  unfold validInBlock
  infer_instance

/-- **T2 (binding is biconditional).** `validInBlock tx h` exactly
characterises the height-side relation: there exists an active branch ID
at `h` equal to `tx.consensusBranchId`. -/
theorem validInBlock_iff (tx : Tx) (h : Nat) :
    validInBlock tx h ↔ currentBranchId h = some tx.consensusBranchId :=
  Iff.rfl

/-- **T3 (pre-Overwinter rejects all transactions).** For heights below
`OVERWINTER`, no transaction can satisfy the binding because the active
epoch has no branch ID. -/
theorem validInBlock_pre_overwinter (tx : Tx) (h : Nat) (hh : h < OVERWINTER) :
    ¬ validInBlock tx h := by
  unfold validInBlock currentBranchId currentUpgrade
  -- All `h ≥ X` are false because h < OVERWINTER ≤ X for every X in the cascade.
  have hLt_nu6_2 : ¬ h ≥ NU6_2 := by
    unfold OVERWINTER NU6_2 at *; omega
  have hLt_nu6_1 : ¬ h ≥ NU6_1 := by
    unfold OVERWINTER NU6_1 at *; omega
  have hLt_nu6   : ¬ h ≥ NU6 := by
    unfold OVERWINTER NU6 at *; omega
  have hLt_nu5   : ¬ h ≥ NU5 := by
    unfold OVERWINTER NU5 at *; omega
  have hLt_ca    : ¬ h ≥ CANOPY := by
    unfold OVERWINTER CANOPY at *; omega
  have hLt_he    : ¬ h ≥ HEARTWOOD := by
    unfold OVERWINTER HEARTWOOD at *; omega
  have hLt_bl    : ¬ h ≥ BLOSSOM := by
    unfold OVERWINTER BLOSSOM at *; omega
  have hLt_sa    : ¬ h ≥ SAPLING := by
    unfold OVERWINTER SAPLING at *; omega
  have hLt_ov    : ¬ h ≥ OVERWINTER := Nat.not_le.mpr hh
  simp [hLt_nu6_2, hLt_nu6_1, hLt_nu6, hLt_nu5, hLt_ca, hLt_he, hLt_bl, hLt_sa,
        hLt_ov]

/-! ### NU5 band lemmas (the active mainnet upgrade at writing) -/

/-- `currentUpgrade` is constantly `some .nu5` on the half-open band
`[NU5, NU6)`. -/
private theorem currentUpgrade_on_nu5_band
    (h : Nat) (h1 : NU5 ≤ h) (h2 : h < NU6) :
    currentUpgrade h = some .nu5 := by
  have hLt_nu6_2 : ¬ h ≥ NU6_2 := by
    unfold NU6 NU6_2 at *; omega
  have hLt_nu6_1 : ¬ h ≥ NU6_1 := by
    unfold NU6 NU6_1 at *; omega
  have hLt_nu6   : ¬ h ≥ NU6 := Nat.not_le.mpr h2
  have hGe_nu5   : h ≥ NU5 := h1
  unfold currentUpgrade
  simp [hLt_nu6_2, hLt_nu6_1, hLt_nu6, hGe_nu5]

/-- `currentBranchId` returns the NU5 branch ID on the NU5 band. -/
private theorem currentBranchId_on_nu5_band
    (h : Nat) (h1 : NU5 ≤ h) (h2 : h < NU6) :
    currentBranchId h = some 0xc2d6d0b4 := by
  unfold currentBranchId
  rw [currentUpgrade_on_nu5_band h h1 h2]
  rfl

/-- **T4 (NU5 branch ID valid only on the NU5 band).** A transaction
declaring the NU5 branch ID `0xc2d6d0b4` is valid at `h` iff `h` lies in
`[NU5, NU6)`. Outside that band the binding rejects, even for adjacent
heights one block before or after activation.

This is the load-bearing replay-protection property: NU5-signed
transactions cannot be replayed into NU6 blocks (and vice versa). -/
theorem nu5_tx_validity_band (tx : Tx)
    (hbid : tx.consensusBranchId = 0xc2d6d0b4) :
    validInBlock tx NU5 ∧
    validInBlock tx (NU6 - 1) ∧
    ¬ validInBlock tx (NU5 - 1) ∧
    ¬ validInBlock tx NU6 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- valid at NU5: NU5 ∈ [NU5, NU6)
    unfold validInBlock
    rw [currentBranchId_on_nu5_band NU5 (le_refl _)
        (by unfold NU5 NU6; decide), hbid]
  · -- valid at NU6 - 1: NU6 - 1 ∈ [NU5, NU6)
    unfold validInBlock
    rw [currentBranchId_on_nu5_band (NU6 - 1)
        (by unfold NU5 NU6; decide) (by unfold NU6; decide), hbid]
  · -- invalid at NU5 - 1: the upgrade is Canopy, not NU5
    intro hv
    unfold validInBlock currentBranchId currentUpgrade at hv
    have hLt_nu6_2 : ¬ NU5 - 1 ≥ NU6_2 := by unfold NU5 NU6_2; decide
    have hLt_nu6_1 : ¬ NU5 - 1 ≥ NU6_1 := by unfold NU5 NU6_1; decide
    have hLt_nu6   : ¬ NU5 - 1 ≥ NU6   := by unfold NU5 NU6; decide
    have hLt_nu5   : ¬ NU5 - 1 ≥ NU5   := by unfold NU5; decide
    have hGe_ca    : NU5 - 1 ≥ CANOPY  := by unfold NU5 CANOPY; decide
    simp only [hLt_nu6_2, hLt_nu6_1, hLt_nu6, hLt_nu5, hGe_ca,
               if_false, if_true, Option.map_some] at hv
    -- hv : branchId .canopy = some tx.consensusBranchId
    rw [hbid] at hv
    -- 0xe9ff75a6 ≠ 0xc2d6d0b4
    revert hv; unfold branchId; decide
  · -- invalid at NU6: the upgrade is NU6, not NU5
    intro hv
    unfold validInBlock currentBranchId currentUpgrade at hv
    have hLt_nu6_2 : ¬ NU6 ≥ NU6_2 := by unfold NU6 NU6_2; decide
    have hLt_nu6_1 : ¬ NU6 ≥ NU6_1 := by unfold NU6 NU6_1; decide
    have hGe_nu6   : (NU6 : Nat) ≥ NU6 := le_refl _
    simp only [hLt_nu6_2, hLt_nu6_1, hGe_nu6,
               if_false, if_true, Option.map_some] at hv
    rw [hbid] at hv
    revert hv; unfold branchId; decide

/-- **T5 (mismatched branch ID at NU5 height rejects).** Any
transaction whose declared branch ID is not `0xc2d6d0b4` is rejected at
height `NU5` (and indeed everywhere in `[NU5, NU6)`). The contrapositive
is exactly the binding-as-replay-protection property. -/
theorem mismatched_branch_id_rejects (tx : Tx) (h : Nat)
    (h1 : NU5 ≤ h) (h2 : h < NU6)
    (hne : tx.consensusBranchId ≠ 0xc2d6d0b4) :
    ¬ validInBlock tx h := by
  unfold validInBlock
  rw [currentBranchId_on_nu5_band h h1 h2]
  intro heq
  apply hne
  exact (Option.some.inj heq).symm

/-- **T6 (binding is unique per height).** For any fixed height, at most
one branch ID value satisfies the binding. The branch ID is a function
of height, not of the transaction. -/
theorem validInBlock_unique_branch_id (tx₁ tx₂ : Tx) (h : Nat)
    (h1 : validInBlock tx₁ h) (h2 : validInBlock tx₂ h) :
    tx₁.consensusBranchId = tx₂.consensusBranchId := by
  unfold validInBlock at h1 h2
  rw [h1] at h2
  exact Option.some.inj h2

/-- **T7 (binding constant within a band).** Validity is constant
across the NU5 band: if a transaction is valid at any one point in
`[NU5, NU6)`, it's valid everywhere in that band. -/
theorem validInBlock_constant_on_nu5_band
    (tx : Tx) (h h' : Nat)
    (h1 : NU5 ≤ h) (h2 : h < NU6)
    (h1' : NU5 ≤ h') (h2' : h' < NU6)
    (hv : validInBlock tx h) :
    validInBlock tx h' := by
  unfold validInBlock at hv ⊢
  rw [currentBranchId_on_nu5_band h h1 h2] at hv
  rw [currentBranchId_on_nu5_band h' h1' h2']
  exact hv

/-- **T8 (cross-band replay rejection).** If a transaction is valid at
some height in the NU5 band, it is rejected at every height in the NU6
band. This is the cryptoeconomic replay-protection property: NU5-bound
transactions cannot be mined into NU6 blocks. -/
theorem validInBlock_rejects_nu6_when_valid_at_nu5
    (tx : Tx) (h h' : Nat)
    (h1 : NU5 ≤ h) (h2 : h < NU6)
    (h1' : NU6 ≤ h') (h2' : h' < NU6_1)
    (hv : validInBlock tx h) :
    ¬ validInBlock tx h' := by
  -- The valid binding pins tx's branch ID to the NU5 one.
  unfold validInBlock at hv
  rw [currentBranchId_on_nu5_band h h1 h2] at hv
  have hbid : tx.consensusBranchId = 0xc2d6d0b4 :=
    (Option.some.inj hv).symm
  -- At height h' ∈ [NU6, NU6_1) the active branch ID is NU6's.
  intro hv'
  unfold validInBlock currentBranchId currentUpgrade at hv'
  have hLt_nu6_2 : ¬ h' ≥ NU6_2 := by
    unfold NU6_1 NU6_2 at *; omega
  have hLt_nu6_1 : ¬ h' ≥ NU6_1 := Nat.not_le.mpr h2'
  have hGe_nu6   : h' ≥ NU6     := h1'
  simp only [hLt_nu6_2, hLt_nu6_1, hGe_nu6,
             if_false, if_true, Option.map_some] at hv'
  rw [hbid] at hv'
  revert hv'; unfold branchId; decide

/-- **T9 (round-trip via the reverse-lookup table).** If `tx` is valid
in a block at height `h`, then its declared branch ID is a known value
in the `CONSENSUS_BRANCH_IDS` table, i.e. `fromBranchId` recognises
it. This is the property the production `try_from(branch_id)` impl
relies on (`network_upgrade.rs:76`). -/
theorem valid_tx_branch_id_known (tx : Tx) (h : Nat)
    (hv : validInBlock tx h) :
    ∃ nu : NU, fromBranchId tx.consensusBranchId = some nu := by
  unfold validInBlock currentBranchId at hv
  -- currentUpgrade h must be some nu
  cases hcu : currentUpgrade h with
  | none =>
    rw [hcu] at hv
    -- hv : Option.map branchId none = some _ — impossible
    simp only [Option.map_none] at hv
    cases hv
  | some nu =>
    rw [hcu] at hv
    simp only [Option.map_some, Option.some.injEq] at hv
    refine ⟨nu, ?_⟩
    rw [← hv]
    exact Zebra.ConsensusBranchId.roundtrip nu

/-- **T10 (concrete: zero branch ID never validates).** A transaction
declaring `nConsensusBranchId = 0` is rejected at every height. Zero
is `RPC_MISSING_ID` in production (`network_upgrade.rs:547`) — explicitly
not a valid consensus value. -/
theorem zero_branch_id_never_valid (h : Nat) :
    ¬ validInBlock { consensusBranchId := 0 } h := by
  intro hv
  obtain ⟨nu, hk⟩ := valid_tx_branch_id_known _ _ hv
  -- fromBranchId 0 = none, contradicting some nu
  rw [Zebra.ConsensusBranchId.fromBranchId_zero] at hk
  cases hk

end Zebra.Zip200BranchIdBinding
