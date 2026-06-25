import Mathlib.Tactic.Common

/-!
# Consensus branch IDs

Models the `CONSENSUS_BRANCH_IDS` table from
`zebra-chain/src/parameters/network_upgrade.rs:225`. Each `NetworkUpgrade`
from Overwinter onward has a 32-bit branch ID that binds transactions and
block headers to a specific consensus epoch (ZIP-200).

We prove that the table is *injective* (no two upgrades share a branch ID,
which would be a consensus crisis) and that the lookup function inverts the
inverse direction correctly.
-/

namespace Zebra.ConsensusBranchId

/-- A subset of `NetworkUpgrade` that has a branch ID. Genesis,
BeforeOverwinter, and the in-flight Nu7/ZFuture are out of scope. -/
inductive NU
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

/-- The branch ID table, as `Nat` (production uses `u32`). All values are
documented in `zebra-chain/src/parameters/network_upgrade.rs:225`. -/
def branchId : NU → Nat
  | .overwinter => 0x5ba81b19
  | .sapling    => 0x76b809bb
  | .blossom    => 0x2bb40e60
  | .heartwood  => 0xf5b9230b
  | .canopy     => 0xe9ff75a6
  | .nu5        => 0xc2d6d0b4
  | .nu6        => 0xc8e71055
  | .nu6_1      => 0x4dec4df0
  | .nu6_2      => 0x5437f330

/-- Reverse lookup: branch ID → `NU` if it's a known value. -/
def fromBranchId (id : Nat) : Option NU :=
  if      id = 0x5ba81b19 then some .overwinter
  else if id = 0x76b809bb then some .sapling
  else if id = 0x2bb40e60 then some .blossom
  else if id = 0xf5b9230b then some .heartwood
  else if id = 0xe9ff75a6 then some .canopy
  else if id = 0xc2d6d0b4 then some .nu5
  else if id = 0xc8e71055 then some .nu6
  else if id = 0x4dec4df0 then some .nu6_1
  else if id = 0x5437f330 then some .nu6_2
  else none

/-! ## Theorems -/

/-- **T1 (round-trip).** Looking up an upgrade by its branch ID recovers
the upgrade. -/
theorem roundtrip (nu : NU) : fromBranchId (branchId nu) = some nu := by
  cases nu <;> decide

/-- **T2 (injective table).** No two distinct upgrades share a branch ID. -/
theorem branchId_injective (nu₁ nu₂ : NU) (h : branchId nu₁ = branchId nu₂) :
    nu₁ = nu₂ := by
  cases nu₁ <;> cases nu₂ <;> (first | rfl | (exfalso; revert h; decide))

/-- **T3 (all branch IDs are `u32`).** Every value in the table fits in 32
bits. This is a consensus invariant — a branch ID is encoded in the
transaction header as `u32`. -/
theorem branchId_lt_u32max (nu : NU) : branchId nu < 2 ^ 32 := by
  cases nu <;> decide

/-- **T4 (fromBranchId rejects unknown values).** `fromBranchId 0`
returns `none` because `0` is not a valid branch ID. -/
theorem fromBranchId_zero : fromBranchId 0 = none := by decide

/-- **T5 (concrete: NU5 has the expected branch ID).** Pin the NU5 branch
ID, which is the active mainnet upgrade as of writing. -/
theorem nu5_branchId : branchId .nu5 = 0xc2d6d0b4 := rfl

end Zebra.ConsensusBranchId
