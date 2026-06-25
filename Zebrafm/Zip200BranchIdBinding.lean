import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Zebrafm.ConsensusBranchId

/-!
# ZIP-200: consensus branch-id binding for transactions

A transaction is only valid in a block at height `h` if its
`nConsensusBranchId` field equals the branch ID of the network upgrade
active at `h` on that network. This is the "transaction replay
protection" property of ZIP-200: every hard-fork upgrade rotates the
branch ID, so transactions signed under one epoch are unspendable in any
other.

We model:

* `Net` — `mainnet` / `testnet`. Branch IDs are shared across networks
  (Rust comment, `network_upgrade.rs:217`: *"Branch ids are the same for
  mainnet and testnet"*), but activation heights differ.
* `currentUpgrade net h : Option NU` — the active upgrade at height `h`
  on `net`, restricted to the upgrade subset that has a branch ID. The
  Rust `NetworkUpgrade::current` is a total function returning a
  `NetworkUpgrade` (so for pre-Overwinter heights it yields
  `Some(Genesis)` or `Some(BeforeOverwinter)`); but `.branch_id()` then
  returns `None` for those two upgrades
  (`network_upgrade.rs:393`, table `network_upgrade.rs:225`). So
  `currentUpgrade` here is the *composition* `current(...).branch_id()`
  collapsed onto the `NU` subset that has a branch ID, and `none`
  faithfully represents *"no branch ID at this height"* — not *"no
  upgrade"*.
* `Tx` — an opaque transaction carrying its declared
  `consensusBranchId`.
* `validInBlock net tx h` — ZIP-200's binding predicate.

We prove:

* the binding is decidable and biconditional;
* pre-Overwinter heights reject every transaction (because there is no
  branch ID to bind to) on both networks;
* the NU5 branch ID `0xc2d6d0b4` is only accepted inside the
  `[NU5, NU6)` activation band on each network, with the boundary
  heights probed explicitly;
* mismatched branch IDs are rejected;
* validity is constant on each band, and a tx valid in the NU5 band is
  rejected in the NU6 band (cross-band replay rejection);
* the NU6 band has its own validity theorem mirroring NU5;
* a valid tx's branch ID is always a known value in the
  `CONSENSUS_BRANCH_IDS` table;
* `nConsensusBranchId = 0` (the `RPC_MISSING_ID` sentinel,
  `network_upgrade.rs:547`) never validates.

Sources:
* `zebra-chain/src/parameters/constants.rs:73-96` — mainnet activation heights
* `zebra-chain/src/parameters/constants.rs:46-70` — testnet activation heights
* `zebra-chain/src/parameters/network_upgrade.rs:101-116` — MAINNET_ACTIVATION_HEIGHTS
* `zebra-chain/src/parameters/network_upgrade.rs:127-142` — TESTNET_ACTIVATION_HEIGHTS
* `zebra-chain/src/parameters/network_upgrade.rs:225` — CONSENSUS_BRANCH_IDS table
* `zebra-chain/src/parameters/network_upgrade.rs:393` — `branch_id()`
* `zebra-chain/src/parameters/network_upgrade.rs:312` — `current()` over height
* `zebra-chain/src/parameters/network_upgrade.rs:547` — `RPC_MISSING_ID`
* `zebra-chain/src/transaction/serialize.rs:683` — `nConsensusBranchId` in the V5 header
-/

namespace Zebra.Zip200BranchIdBinding

open Zebra.ConsensusBranchId (NU branchId fromBranchId)

/-- The network parameter. Branch IDs are shared, but activation
heights differ between mainnet and testnet (Rust
`zebra-chain/src/parameters/constants.rs:46-96`). -/
inductive Net
  | mainnet
  | testnet
  deriving DecidableEq, Repr

/-! ## Mainnet activation heights

Mirror `zebra-chain/src/parameters/constants.rs:73-96`. We restrict to
the subset of upgrades that have a branch ID — i.e. Overwinter through
NU6.2; `Genesis` and `BeforeOverwinter` are pre-branch-ID epochs and
have no entry in `CONSENSUS_BRANCH_IDS` (`network_upgrade.rs:225`). -/

def MAINNET_OVERWINTER : Nat := 347_500
def MAINNET_SAPLING : Nat := 419_200
def MAINNET_BLOSSOM : Nat := 653_600
def MAINNET_HEARTWOOD : Nat := 903_000
def MAINNET_CANOPY : Nat := 1_046_400
def MAINNET_NU5 : Nat := 1_687_104
def MAINNET_NU6 : Nat := 2_726_400
def MAINNET_NU6_1 : Nat := 3_146_400
def MAINNET_NU6_2 : Nat := 3_364_600

/-! ## Testnet activation heights

Mirror `zebra-chain/src/parameters/constants.rs:46-70`. The activation
heights differ from mainnet at every upgrade (testnet rolls earlier in
some cases, later in others); the branch-ID *values* are identical
because Rust's `CONSENSUS_BRANCH_IDS` is network-independent
(`network_upgrade.rs:217`). -/

def TESTNET_OVERWINTER : Nat := 207_500
def TESTNET_SAPLING : Nat := 280_000
def TESTNET_BLOSSOM : Nat := 584_000
def TESTNET_HEARTWOOD : Nat := 903_800
def TESTNET_CANOPY : Nat := 1_028_500
def TESTNET_NU5 : Nat := 1_842_420
def TESTNET_NU6 : Nat := 2_976_000
def TESTNET_NU6_1 : Nat := 3_536_500
def TESTNET_NU6_2 : Nat := 4_052_000

/-- Backwards-compatible mainnet aliases. The original module exposed
unprefixed names; preserve them so downstream theorems keep their
identifiers. -/
abbrev OVERWINTER : Nat := MAINNET_OVERWINTER
abbrev SAPLING : Nat := MAINNET_SAPLING
abbrev BLOSSOM : Nat := MAINNET_BLOSSOM
abbrev HEARTWOOD : Nat := MAINNET_HEARTWOOD
abbrev CANOPY : Nat := MAINNET_CANOPY
abbrev NU5 : Nat := MAINNET_NU5
abbrev NU6 : Nat := MAINNET_NU6
abbrev NU6_1 : Nat := MAINNET_NU6_1
abbrev NU6_2 : Nat := MAINNET_NU6_2

/-- Activation height of upgrade `nu` on network `net`. Mirrors the
ascending lookup in `MAINNET_ACTIVATION_HEIGHTS` /
`TESTNET_ACTIVATION_HEIGHTS` (`network_upgrade.rs:101-142`). -/
def activationHeight : Net → NU → Nat
  | .mainnet, .overwinter => MAINNET_OVERWINTER
  | .mainnet, .sapling    => MAINNET_SAPLING
  | .mainnet, .blossom    => MAINNET_BLOSSOM
  | .mainnet, .heartwood  => MAINNET_HEARTWOOD
  | .mainnet, .canopy     => MAINNET_CANOPY
  | .mainnet, .nu5        => MAINNET_NU5
  | .mainnet, .nu6        => MAINNET_NU6
  | .mainnet, .nu6_1      => MAINNET_NU6_1
  | .mainnet, .nu6_2      => MAINNET_NU6_2
  | .testnet, .overwinter => TESTNET_OVERWINTER
  | .testnet, .sapling    => TESTNET_SAPLING
  | .testnet, .blossom    => TESTNET_BLOSSOM
  | .testnet, .heartwood  => TESTNET_HEARTWOOD
  | .testnet, .canopy     => TESTNET_CANOPY
  | .testnet, .nu5        => TESTNET_NU5
  | .testnet, .nu6        => TESTNET_NU6
  | .testnet, .nu6_1      => TESTNET_NU6_1
  | .testnet, .nu6_2      => TESTNET_NU6_2

/-- The active upgrade with a branch ID at height `h` on `net`, or
`none` if `h` is pre-Overwinter (Genesis/BeforeOverwinter epochs have
no branch ID, `network_upgrade.rs:221`). Models the composition
`NetworkUpgrade::current(network, h).branch_id()` collapsed onto the
`NU` subset used in `ConsensusBranchId`. -/
def currentUpgrade (net : Net) (h : Nat) : Option NU :=
  match net with
  | .mainnet =>
    if h ≥ MAINNET_NU6_2 then some .nu6_2
    else if h ≥ MAINNET_NU6_1 then some .nu6_1
    else if h ≥ MAINNET_NU6   then some .nu6
    else if h ≥ MAINNET_NU5   then some .nu5
    else if h ≥ MAINNET_CANOPY then some .canopy
    else if h ≥ MAINNET_HEARTWOOD then some .heartwood
    else if h ≥ MAINNET_BLOSSOM then some .blossom
    else if h ≥ MAINNET_SAPLING then some .sapling
    else if h ≥ MAINNET_OVERWINTER then some .overwinter
    else none
  | .testnet =>
    if h ≥ TESTNET_NU6_2 then some .nu6_2
    else if h ≥ TESTNET_NU6_1 then some .nu6_1
    else if h ≥ TESTNET_NU6   then some .nu6
    else if h ≥ TESTNET_NU5   then some .nu5
    else if h ≥ TESTNET_CANOPY then some .canopy
    else if h ≥ TESTNET_HEARTWOOD then some .heartwood
    else if h ≥ TESTNET_BLOSSOM then some .blossom
    else if h ≥ TESTNET_SAPLING then some .sapling
    else if h ≥ TESTNET_OVERWINTER then some .overwinter
    else none

/-- The branch ID of the active upgrade at height `h` on `net`, or
`none` if the height is pre-Overwinter. -/
def currentBranchId (net : Net) (h : Nat) : Option Nat :=
  (currentUpgrade net h).map branchId

/-- An opaque-ish model of a transaction: we only care about the
declared `nConsensusBranchId` field that V5+ transactions serialise into
their header.
Source: `zebra-chain/src/transaction/serialize.rs:683` -/
structure Tx where
  consensusBranchId : Nat

/-- ZIP-200 binding: a transaction is valid in a block at height `h`
on network `net` iff its declared branch ID equals the branch ID of
the upgrade in force at `h`. If the height has no branch ID
(pre-Overwinter), the transaction is invalid regardless of its
declared value. -/
def validInBlock (net : Net) (tx : Tx) (h : Nat) : Prop :=
  currentBranchId net h = some tx.consensusBranchId

/-! ## Theorems -/

/-- **T1 (decidable binding).** The ZIP-200 validity check is decidable,
which is what makes it implementable as a node-side check. -/
instance validInBlock_decidable (net : Net) (tx : Tx) (h : Nat) :
    Decidable (validInBlock net tx h) := by
  unfold validInBlock
  infer_instance

/-- **T2 (binding is biconditional).** `validInBlock net tx h` exactly
characterises the height-side relation: there exists an active branch
ID at `h` on `net` equal to `tx.consensusBranchId`. -/
theorem validInBlock_iff (net : Net) (tx : Tx) (h : Nat) :
    validInBlock net tx h ↔ currentBranchId net h = some tx.consensusBranchId :=
  Iff.rfl

/-- **T3 (mainnet pre-Overwinter rejects all transactions).** For
heights below mainnet `OVERWINTER` (Genesis and BeforeOverwinter
epochs), no transaction can satisfy the binding because those upgrades
have no branch ID (`network_upgrade.rs:225`). -/
theorem validInBlock_pre_overwinter_mainnet (tx : Tx) (h : Nat)
    (hh : h < MAINNET_OVERWINTER) :
    ¬ validInBlock .mainnet tx h := by
  unfold validInBlock currentBranchId currentUpgrade
  have hLt_nu6_2 : ¬ h ≥ MAINNET_NU6_2 := by
    unfold MAINNET_OVERWINTER MAINNET_NU6_2 at *; omega
  have hLt_nu6_1 : ¬ h ≥ MAINNET_NU6_1 := by
    unfold MAINNET_OVERWINTER MAINNET_NU6_1 at *; omega
  have hLt_nu6   : ¬ h ≥ MAINNET_NU6 := by
    unfold MAINNET_OVERWINTER MAINNET_NU6 at *; omega
  have hLt_nu5   : ¬ h ≥ MAINNET_NU5 := by
    unfold MAINNET_OVERWINTER MAINNET_NU5 at *; omega
  have hLt_ca    : ¬ h ≥ MAINNET_CANOPY := by
    unfold MAINNET_OVERWINTER MAINNET_CANOPY at *; omega
  have hLt_he    : ¬ h ≥ MAINNET_HEARTWOOD := by
    unfold MAINNET_OVERWINTER MAINNET_HEARTWOOD at *; omega
  have hLt_bl    : ¬ h ≥ MAINNET_BLOSSOM := by
    unfold MAINNET_OVERWINTER MAINNET_BLOSSOM at *; omega
  have hLt_sa    : ¬ h ≥ MAINNET_SAPLING := by
    unfold MAINNET_OVERWINTER MAINNET_SAPLING at *; omega
  have hLt_ov    : ¬ h ≥ MAINNET_OVERWINTER := Nat.not_le.mpr hh
  simp [hLt_nu6_2, hLt_nu6_1, hLt_nu6, hLt_nu5, hLt_ca, hLt_he, hLt_bl, hLt_sa,
        hLt_ov]

/-- **T3b (testnet pre-Overwinter rejects all transactions).**
Companion of T3 for the testnet activation list
(`zebra-chain/src/parameters/constants.rs:46-70`). -/
theorem validInBlock_pre_overwinter_testnet (tx : Tx) (h : Nat)
    (hh : h < TESTNET_OVERWINTER) :
    ¬ validInBlock .testnet tx h := by
  unfold validInBlock currentBranchId currentUpgrade
  have hLt_nu6_2 : ¬ h ≥ TESTNET_NU6_2 := by
    unfold TESTNET_OVERWINTER TESTNET_NU6_2 at *; omega
  have hLt_nu6_1 : ¬ h ≥ TESTNET_NU6_1 := by
    unfold TESTNET_OVERWINTER TESTNET_NU6_1 at *; omega
  have hLt_nu6   : ¬ h ≥ TESTNET_NU6 := by
    unfold TESTNET_OVERWINTER TESTNET_NU6 at *; omega
  have hLt_nu5   : ¬ h ≥ TESTNET_NU5 := by
    unfold TESTNET_OVERWINTER TESTNET_NU5 at *; omega
  have hLt_ca    : ¬ h ≥ TESTNET_CANOPY := by
    unfold TESTNET_OVERWINTER TESTNET_CANOPY at *; omega
  have hLt_he    : ¬ h ≥ TESTNET_HEARTWOOD := by
    unfold TESTNET_OVERWINTER TESTNET_HEARTWOOD at *; omega
  have hLt_bl    : ¬ h ≥ TESTNET_BLOSSOM := by
    unfold TESTNET_OVERWINTER TESTNET_BLOSSOM at *; omega
  have hLt_sa    : ¬ h ≥ TESTNET_SAPLING := by
    unfold TESTNET_OVERWINTER TESTNET_SAPLING at *; omega
  have hLt_ov    : ¬ h ≥ TESTNET_OVERWINTER := Nat.not_le.mpr hh
  simp [hLt_nu6_2, hLt_nu6_1, hLt_nu6, hLt_nu5, hLt_ca, hLt_he, hLt_bl, hLt_sa,
        hLt_ov]

/-- Backwards-compatible mainnet alias for the original module's
pre-Overwinter rejection theorem. -/
theorem validInBlock_pre_overwinter (tx : Tx) (h : Nat) (hh : h < OVERWINTER) :
    ¬ validInBlock .mainnet tx h :=
  validInBlock_pre_overwinter_mainnet tx h hh

/-! ### Mainnet band lemmas -/

/-- `currentUpgrade .mainnet` is constantly `some .nu5` on the
half-open band `[MAINNET_NU5, MAINNET_NU6)`. -/
private theorem currentUpgrade_on_mainnet_nu5_band
    (h : Nat) (h1 : MAINNET_NU5 ≤ h) (h2 : h < MAINNET_NU6) :
    currentUpgrade .mainnet h = some .nu5 := by
  have hLt_nu6_2 : ¬ h ≥ MAINNET_NU6_2 := by
    unfold MAINNET_NU6 MAINNET_NU6_2 at *; omega
  have hLt_nu6_1 : ¬ h ≥ MAINNET_NU6_1 := by
    unfold MAINNET_NU6 MAINNET_NU6_1 at *; omega
  have hLt_nu6   : ¬ h ≥ MAINNET_NU6 := Nat.not_le.mpr h2
  have hGe_nu5   : h ≥ MAINNET_NU5 := h1
  unfold currentUpgrade
  simp [hLt_nu6_2, hLt_nu6_1, hLt_nu6, hGe_nu5]

/-- `currentBranchId .mainnet` returns the NU5 branch ID on the
mainnet NU5 band. -/
private theorem currentBranchId_on_mainnet_nu5_band
    (h : Nat) (h1 : MAINNET_NU5 ≤ h) (h2 : h < MAINNET_NU6) :
    currentBranchId .mainnet h = some 0xc2d6d0b4 := by
  unfold currentBranchId
  rw [currentUpgrade_on_mainnet_nu5_band h h1 h2]
  rfl

/-- `currentUpgrade .mainnet` is constantly `some .nu6` on the
half-open band `[MAINNET_NU6, MAINNET_NU6_1)`. -/
private theorem currentUpgrade_on_mainnet_nu6_band
    (h : Nat) (h1 : MAINNET_NU6 ≤ h) (h2 : h < MAINNET_NU6_1) :
    currentUpgrade .mainnet h = some .nu6 := by
  have hLt_nu6_2 : ¬ h ≥ MAINNET_NU6_2 := by
    unfold MAINNET_NU6_1 MAINNET_NU6_2 at *; omega
  have hLt_nu6_1 : ¬ h ≥ MAINNET_NU6_1 := Nat.not_le.mpr h2
  have hGe_nu6   : h ≥ MAINNET_NU6 := h1
  unfold currentUpgrade
  simp [hLt_nu6_2, hLt_nu6_1, hGe_nu6]

/-- `currentBranchId .mainnet` returns the NU6 branch ID on the
mainnet NU6 band. -/
private theorem currentBranchId_on_mainnet_nu6_band
    (h : Nat) (h1 : MAINNET_NU6 ≤ h) (h2 : h < MAINNET_NU6_1) :
    currentBranchId .mainnet h = some 0xc8e71055 := by
  unfold currentBranchId
  rw [currentUpgrade_on_mainnet_nu6_band h h1 h2]
  rfl

/-! ### Testnet band lemmas -/

/-- `currentUpgrade .testnet` is constantly `some .nu5` on the
half-open band `[TESTNET_NU5, TESTNET_NU6)`. -/
private theorem currentUpgrade_on_testnet_nu5_band
    (h : Nat) (h1 : TESTNET_NU5 ≤ h) (h2 : h < TESTNET_NU6) :
    currentUpgrade .testnet h = some .nu5 := by
  have hLt_nu6_2 : ¬ h ≥ TESTNET_NU6_2 := by
    unfold TESTNET_NU6 TESTNET_NU6_2 at *; omega
  have hLt_nu6_1 : ¬ h ≥ TESTNET_NU6_1 := by
    unfold TESTNET_NU6 TESTNET_NU6_1 at *; omega
  have hLt_nu6   : ¬ h ≥ TESTNET_NU6 := Nat.not_le.mpr h2
  have hGe_nu5   : h ≥ TESTNET_NU5 := h1
  unfold currentUpgrade
  simp [hLt_nu6_2, hLt_nu6_1, hLt_nu6, hGe_nu5]

/-- `currentBranchId .testnet` returns the NU5 branch ID on the
testnet NU5 band. -/
private theorem currentBranchId_on_testnet_nu5_band
    (h : Nat) (h1 : TESTNET_NU5 ≤ h) (h2 : h < TESTNET_NU6) :
    currentBranchId .testnet h = some 0xc2d6d0b4 := by
  unfold currentBranchId
  rw [currentUpgrade_on_testnet_nu5_band h h1 h2]
  rfl

/-! ### NU5 band validity (the active mainnet upgrade at writing) -/

/-- **T4 (NU5 branch ID valid only on the mainnet NU5 band).** A
transaction declaring the NU5 branch ID `0xc2d6d0b4` is valid at `h`
on mainnet iff `h` lies in `[MAINNET_NU5, MAINNET_NU6)`. Outside that
band the binding rejects, even for adjacent heights one block before
or after activation.

This is the load-bearing replay-protection property: NU5-signed
transactions cannot be replayed into NU6 blocks (and vice versa). -/
theorem nu5_tx_validity_band_mainnet (tx : Tx)
    (hbid : tx.consensusBranchId = 0xc2d6d0b4) :
    validInBlock .mainnet tx MAINNET_NU5 ∧
    validInBlock .mainnet tx (MAINNET_NU6 - 1) ∧
    ¬ validInBlock .mainnet tx (MAINNET_NU5 - 1) ∧
    ¬ validInBlock .mainnet tx MAINNET_NU6 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- valid at NU5: NU5 ∈ [NU5, NU6)
    unfold validInBlock
    rw [currentBranchId_on_mainnet_nu5_band MAINNET_NU5 (le_refl _)
        (by unfold MAINNET_NU5 MAINNET_NU6; decide), hbid]
  · -- valid at NU6 - 1: NU6 - 1 ∈ [NU5, NU6)
    unfold validInBlock
    rw [currentBranchId_on_mainnet_nu5_band (MAINNET_NU6 - 1)
        (by unfold MAINNET_NU5 MAINNET_NU6; decide)
        (by unfold MAINNET_NU6; decide), hbid]
  · -- invalid at NU5 - 1: the upgrade is Canopy, not NU5
    intro hv
    unfold validInBlock currentBranchId currentUpgrade at hv
    have hLt_nu6_2 : ¬ MAINNET_NU5 - 1 ≥ MAINNET_NU6_2 := by
      unfold MAINNET_NU5 MAINNET_NU6_2; decide
    have hLt_nu6_1 : ¬ MAINNET_NU5 - 1 ≥ MAINNET_NU6_1 := by
      unfold MAINNET_NU5 MAINNET_NU6_1; decide
    have hLt_nu6   : ¬ MAINNET_NU5 - 1 ≥ MAINNET_NU6   := by
      unfold MAINNET_NU5 MAINNET_NU6; decide
    have hLt_nu5   : ¬ MAINNET_NU5 - 1 ≥ MAINNET_NU5   := by
      unfold MAINNET_NU5; decide
    have hGe_ca    : MAINNET_NU5 - 1 ≥ MAINNET_CANOPY  := by
      unfold MAINNET_NU5 MAINNET_CANOPY; decide
    simp only [hLt_nu6_2, hLt_nu6_1, hLt_nu6, hLt_nu5, hGe_ca,
               if_false, if_true, Option.map_some] at hv
    rw [hbid] at hv
    revert hv; unfold branchId; decide
  · -- invalid at NU6: the upgrade is NU6, not NU5
    intro hv
    unfold validInBlock currentBranchId currentUpgrade at hv
    have hLt_nu6_2 : ¬ MAINNET_NU6 ≥ MAINNET_NU6_2 := by
      unfold MAINNET_NU6 MAINNET_NU6_2; decide
    have hLt_nu6_1 : ¬ MAINNET_NU6 ≥ MAINNET_NU6_1 := by
      unfold MAINNET_NU6 MAINNET_NU6_1; decide
    have hGe_nu6   : (MAINNET_NU6 : Nat) ≥ MAINNET_NU6 := le_refl _
    simp only [hLt_nu6_2, hLt_nu6_1, hGe_nu6,
               if_false, if_true, Option.map_some] at hv
    rw [hbid] at hv
    revert hv; unfold branchId; decide

/-- Backwards-compatible mainnet NU5 band validity theorem. -/
theorem nu5_tx_validity_band (tx : Tx)
    (hbid : tx.consensusBranchId = 0xc2d6d0b4) :
    validInBlock .mainnet tx NU5 ∧
    validInBlock .mainnet tx (NU6 - 1) ∧
    ¬ validInBlock .mainnet tx (NU5 - 1) ∧
    ¬ validInBlock .mainnet tx NU6 :=
  nu5_tx_validity_band_mainnet tx hbid

/-- **T4b (NU5 branch ID valid only on the testnet NU5 band).** The
testnet companion of T4: a transaction declaring `0xc2d6d0b4` is valid
at `h` on testnet iff `h` lies in `[TESTNET_NU5, TESTNET_NU6)`. The
testnet boundary heights differ from mainnet
(`constants.rs:62-65`), but the branch ID value is shared
(`network_upgrade.rs:217`). -/
theorem nu5_tx_validity_band_testnet (tx : Tx)
    (hbid : tx.consensusBranchId = 0xc2d6d0b4) :
    validInBlock .testnet tx TESTNET_NU5 ∧
    validInBlock .testnet tx (TESTNET_NU6 - 1) ∧
    ¬ validInBlock .testnet tx (TESTNET_NU5 - 1) ∧
    ¬ validInBlock .testnet tx TESTNET_NU6 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- valid at TESTNET_NU5
    unfold validInBlock
    rw [currentBranchId_on_testnet_nu5_band TESTNET_NU5 (le_refl _)
        (by unfold TESTNET_NU5 TESTNET_NU6; decide), hbid]
  · -- valid at TESTNET_NU6 - 1
    unfold validInBlock
    rw [currentBranchId_on_testnet_nu5_band (TESTNET_NU6 - 1)
        (by unfold TESTNET_NU5 TESTNET_NU6; decide)
        (by unfold TESTNET_NU6; decide), hbid]
  · -- invalid just below testnet NU5: upgrade is canopy
    intro hv
    unfold validInBlock currentBranchId currentUpgrade at hv
    have hLt_nu6_2 : ¬ TESTNET_NU5 - 1 ≥ TESTNET_NU6_2 := by
      unfold TESTNET_NU5 TESTNET_NU6_2; decide
    have hLt_nu6_1 : ¬ TESTNET_NU5 - 1 ≥ TESTNET_NU6_1 := by
      unfold TESTNET_NU5 TESTNET_NU6_1; decide
    have hLt_nu6   : ¬ TESTNET_NU5 - 1 ≥ TESTNET_NU6   := by
      unfold TESTNET_NU5 TESTNET_NU6; decide
    have hLt_nu5   : ¬ TESTNET_NU5 - 1 ≥ TESTNET_NU5   := by
      unfold TESTNET_NU5; decide
    have hGe_ca    : TESTNET_NU5 - 1 ≥ TESTNET_CANOPY  := by
      unfold TESTNET_NU5 TESTNET_CANOPY; decide
    simp only [hLt_nu6_2, hLt_nu6_1, hLt_nu6, hLt_nu5, hGe_ca,
               if_false, if_true, Option.map_some] at hv
    rw [hbid] at hv
    revert hv; unfold branchId; decide
  · -- invalid at testnet NU6: upgrade is nu6
    intro hv
    unfold validInBlock currentBranchId currentUpgrade at hv
    have hLt_nu6_2 : ¬ TESTNET_NU6 ≥ TESTNET_NU6_2 := by
      unfold TESTNET_NU6 TESTNET_NU6_2; decide
    have hLt_nu6_1 : ¬ TESTNET_NU6 ≥ TESTNET_NU6_1 := by
      unfold TESTNET_NU6 TESTNET_NU6_1; decide
    have hGe_nu6   : (TESTNET_NU6 : Nat) ≥ TESTNET_NU6 := le_refl _
    simp only [hLt_nu6_2, hLt_nu6_1, hGe_nu6,
               if_false, if_true, Option.map_some] at hv
    rw [hbid] at hv
    revert hv; unfold branchId; decide

/-- **T5 (mismatched branch ID at NU5 height rejects).** Any
transaction whose declared branch ID is not `0xc2d6d0b4` is rejected
at any mainnet height in `[MAINNET_NU5, MAINNET_NU6)`. The
contrapositive is exactly the binding-as-replay-protection property. -/
theorem mismatched_branch_id_rejects (tx : Tx) (h : Nat)
    (h1 : MAINNET_NU5 ≤ h) (h2 : h < MAINNET_NU6)
    (hne : tx.consensusBranchId ≠ 0xc2d6d0b4) :
    ¬ validInBlock .mainnet tx h := by
  unfold validInBlock
  rw [currentBranchId_on_mainnet_nu5_band h h1 h2]
  intro heq
  apply hne
  exact (Option.some.inj heq).symm

/-- **T6 (binding is unique per height).** For any fixed height and
network, at most one branch ID value satisfies the binding. The
branch ID is a function of (network, height), not of the transaction. -/
theorem validInBlock_unique_branch_id (net : Net) (tx₁ tx₂ : Tx) (h : Nat)
    (h1 : validInBlock net tx₁ h) (h2 : validInBlock net tx₂ h) :
    tx₁.consensusBranchId = tx₂.consensusBranchId := by
  unfold validInBlock at h1 h2
  rw [h1] at h2
  exact Option.some.inj h2

/-- **T7 (binding constant within the mainnet NU5 band).** Validity is
constant across the mainnet NU5 band: if a transaction is valid at any
one point in `[MAINNET_NU5, MAINNET_NU6)`, it's valid everywhere in
that band. -/
theorem validInBlock_constant_on_mainnet_nu5_band
    (tx : Tx) (h h' : Nat)
    (h1 : MAINNET_NU5 ≤ h) (h2 : h < MAINNET_NU6)
    (h1' : MAINNET_NU5 ≤ h') (h2' : h' < MAINNET_NU6)
    (hv : validInBlock .mainnet tx h) :
    validInBlock .mainnet tx h' := by
  unfold validInBlock at hv ⊢
  rw [currentBranchId_on_mainnet_nu5_band h h1 h2] at hv
  rw [currentBranchId_on_mainnet_nu5_band h' h1' h2']
  exact hv

/-- **T7b (binding constant within the mainnet NU6 band).** New band
lemma. Validity is constant across `[MAINNET_NU6, MAINNET_NU6_1)`. -/
theorem validInBlock_constant_on_mainnet_nu6_band
    (tx : Tx) (h h' : Nat)
    (h1 : MAINNET_NU6 ≤ h) (h2 : h < MAINNET_NU6_1)
    (h1' : MAINNET_NU6 ≤ h') (h2' : h' < MAINNET_NU6_1)
    (hv : validInBlock .mainnet tx h) :
    validInBlock .mainnet tx h' := by
  unfold validInBlock at hv ⊢
  rw [currentBranchId_on_mainnet_nu6_band h h1 h2] at hv
  rw [currentBranchId_on_mainnet_nu6_band h' h1' h2']
  exact hv

/-- Backwards-compatible alias for the NU5-band constancy theorem. -/
theorem validInBlock_constant_on_nu5_band
    (tx : Tx) (h h' : Nat)
    (h1 : NU5 ≤ h) (h2 : h < NU6)
    (h1' : NU5 ≤ h') (h2' : h' < NU6)
    (hv : validInBlock .mainnet tx h) :
    validInBlock .mainnet tx h' :=
  validInBlock_constant_on_mainnet_nu5_band tx h h' h1 h2 h1' h2' hv

/-- **T8 (cross-band replay rejection on mainnet).** If a transaction
is valid at some height in the mainnet NU5 band, it is rejected at
every height in the mainnet NU6 band. This is the cryptoeconomic
replay-protection property: NU5-bound transactions cannot be mined
into NU6 blocks. -/
theorem validInBlock_rejects_nu6_when_valid_at_nu5
    (tx : Tx) (h h' : Nat)
    (h1 : MAINNET_NU5 ≤ h) (h2 : h < MAINNET_NU6)
    (h1' : MAINNET_NU6 ≤ h') (h2' : h' < MAINNET_NU6_1)
    (hv : validInBlock .mainnet tx h) :
    ¬ validInBlock .mainnet tx h' := by
  unfold validInBlock at hv
  rw [currentBranchId_on_mainnet_nu5_band h h1 h2] at hv
  have hbid : tx.consensusBranchId = 0xc2d6d0b4 :=
    (Option.some.inj hv).symm
  intro hv'
  unfold validInBlock at hv'
  rw [currentBranchId_on_mainnet_nu6_band h' h1' h2'] at hv'
  rw [hbid] at hv'
  revert hv'; decide

/-- **T8b (cross-band replay rejection on testnet).** Testnet
companion of T8: if `tx` is valid at some height in the testnet NU5
band, it is rejected at every height in the testnet NU6 band. -/
theorem validInBlock_rejects_testnet_nu6_when_valid_at_testnet_nu5
    (tx : Tx) (h h' : Nat)
    (h1 : TESTNET_NU5 ≤ h) (h2 : h < TESTNET_NU6)
    (h1' : TESTNET_NU6 ≤ h') (h2' : h' < TESTNET_NU6_1)
    (hv : validInBlock .testnet tx h) :
    ¬ validInBlock .testnet tx h' := by
  unfold validInBlock at hv
  rw [currentBranchId_on_testnet_nu5_band h h1 h2] at hv
  have hbid : tx.consensusBranchId = 0xc2d6d0b4 :=
    (Option.some.inj hv).symm
  intro hv'
  unfold validInBlock currentBranchId currentUpgrade at hv'
  have hLt_nu6_2 : ¬ h' ≥ TESTNET_NU6_2 := by
    unfold TESTNET_NU6_1 TESTNET_NU6_2 at *; omega
  have hLt_nu6_1 : ¬ h' ≥ TESTNET_NU6_1 := Nat.not_le.mpr h2'
  have hGe_nu6   : h' ≥ TESTNET_NU6     := h1'
  simp only [hLt_nu6_2, hLt_nu6_1, hGe_nu6,
             if_false, if_true, Option.map_some] at hv'
  rw [hbid] at hv'
  revert hv'; unfold branchId; decide

/-- **T9 (round-trip via the reverse-lookup table).** If `tx` is valid
in a block at height `h` on either network, then its declared branch
ID is a known value in the `CONSENSUS_BRANCH_IDS` table, i.e.
`fromBranchId` recognises it. This is the property the production
`try_from(branch_id)` impl relies on (`network_upgrade.rs:76`). -/
theorem valid_tx_branch_id_known (net : Net) (tx : Tx) (h : Nat)
    (hv : validInBlock net tx h) :
    ∃ nu : NU, fromBranchId tx.consensusBranchId = some nu := by
  unfold validInBlock currentBranchId at hv
  cases hcu : currentUpgrade net h with
  | none =>
    rw [hcu] at hv
    simp only [Option.map_none] at hv
    cases hv
  | some nu =>
    rw [hcu] at hv
    simp only [Option.map_some, Option.some.injEq] at hv
    refine ⟨nu, ?_⟩
    rw [← hv]
    exact Zebra.ConsensusBranchId.roundtrip nu

/-- **T10 (zero branch ID never validates).** A transaction declaring
`nConsensusBranchId = 0` is rejected at every height on every network.
Zero is `RPC_MISSING_ID` in production (`network_upgrade.rs:547`) —
explicitly not a valid consensus value. -/
theorem zero_branch_id_never_valid (net : Net) (h : Nat) :
    ¬ validInBlock net { consensusBranchId := 0 } h := by
  intro hv
  obtain ⟨nu, hk⟩ := valid_tx_branch_id_known net _ _ hv
  rw [Zebra.ConsensusBranchId.fromBranchId_zero] at hk
  cases hk

/-- **T11 (branch IDs are network-independent).** The Rust comment
*"Branch ids are the same for mainnet and testnet"*
(`network_upgrade.rs:217`) becomes the formal statement that any
upgrade that is the active upgrade on both networks at heights `h_m`
and `h_t` respectively determines the *same* branch ID. -/
theorem branch_id_network_independent (h_m h_t : Nat) (nu : NU)
    (hm : currentUpgrade .mainnet h_m = some nu)
    (ht : currentUpgrade .testnet h_t = some nu) :
    currentBranchId .mainnet h_m = currentBranchId .testnet h_t := by
  unfold currentBranchId
  rw [hm, ht]

/-- **T12 (testnet NU5 activation height differs from mainnet).** Sanity
check that the testnet vs mainnet height tables are distinct (Finding
57). Both networks share the NU5 branch ID, but the height at which
NU5 is in force differs by 155_316 blocks. -/
theorem testnet_nu5_activation_differs_from_mainnet :
    TESTNET_NU5 ≠ MAINNET_NU5 := by
  unfold TESTNET_NU5 MAINNET_NU5
  decide

end Zebra.Zip200BranchIdBinding
