import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# ZIP-317 conventional fee

Models the conventional fee formula from
`zebra-chain/src/transaction/unmined/zip317.rs`:

  `conventional_fee = MARGINAL_FEE * max(logical_actions, GRACE_ACTIONS)`

with `MARGINAL_FEE = 5_000` zatoshis and `GRACE_ACTIONS = 2`.

We model `logical_actions` as an opaque `Nat` parameter (the underlying
calculation is a sum of `div_ceil` over transaction inputs/outputs and a
mix of pool actions; this is a separate verification task) and prove the
arithmetic properties of the fee formula itself.

[ZIP-317]: <https://zips.z.cash/zip-0317#fee-calculation>
-/

namespace Zebra.Zip317

/-- `MARGINAL_FEE` in zatoshis.
Source: `zebra-chain/src/transaction/unmined/zip317.rs:23` -/
def MARGINAL_FEE : Nat := 5_000

/-- `GRACE_ACTIONS`.
Source: `zebra-chain/src/transaction/unmined/zip317.rs:26` -/
def GRACE_ACTIONS : Nat := 2

/-- `conventional_actions = max(logical_actions, GRACE_ACTIONS)`.
Source: `zebra-chain/src/transaction/unmined/zip317.rs:169` -/
def conventionalActions (logicalActions : Nat) : Nat :=
  max logicalActions GRACE_ACTIONS

/-- `conventional_fee = MARGINAL_FEE * conventional_actions`.
Source: `zebra-chain/src/transaction/unmined/zip317.rs:72` -/
def conventionalFee (logicalActions : Nat) : Nat :=
  MARGINAL_FEE * conventionalActions logicalActions

/-! ## Theorems -/

/-- **T1 (minimum fee floor).** The conventional fee is at least
`MARGINAL_FEE * GRACE_ACTIONS = 10_000` zatoshis. -/
theorem conventionalFee_ge_floor (n : Nat) :
    MARGINAL_FEE * GRACE_ACTIONS ≤ conventionalFee n := by
  unfold conventionalFee conventionalActions
  exact Nat.mul_le_mul_left _ (Nat.le_max_right _ _)

/-- **T2 (grace floor).** For transactions with `logicalActions ≤ GRACE_ACTIONS`,
the conventional fee is exactly `MARGINAL_FEE * GRACE_ACTIONS`. -/
theorem conventionalFee_at_grace (n : Nat) (h : n ≤ GRACE_ACTIONS) :
    conventionalFee n = MARGINAL_FEE * GRACE_ACTIONS := by
  unfold conventionalFee conventionalActions
  rw [Nat.max_eq_right h]

/-- **T3 (linear regime).** For `logicalActions ≥ GRACE_ACTIONS`, the
conventional fee is exactly `MARGINAL_FEE * logicalActions`. -/
theorem conventionalFee_linear (n : Nat) (h : GRACE_ACTIONS ≤ n) :
    conventionalFee n = MARGINAL_FEE * n := by
  unfold conventionalFee conventionalActions
  rw [Nat.max_eq_left h]

/-- **T4 (monotone).** Adding actions never decreases the conventional fee. -/
theorem conventionalFee_monotone (n₁ n₂ : Nat) (hle : n₁ ≤ n₂) :
    conventionalFee n₁ ≤ conventionalFee n₂ := by
  unfold conventionalFee conventionalActions
  exact Nat.mul_le_mul_left _ (max_le_max hle (le_refl _))

/-- **T5 (concrete: 10_000 zatoshi floor).** The minimum conventional fee is
exactly 10_000 zatoshis (the famously cited ZIP-317 minimum). -/
theorem conventionalFee_floor : MARGINAL_FEE * GRACE_ACTIONS = 10_000 := by
  unfold MARGINAL_FEE GRACE_ACTIONS; rfl

/-- **T6 (concrete: zero-action fee).** A transaction with 0 logical actions
still pays the grace floor. -/
theorem conventionalFee_zero_actions : conventionalFee 0 = 10_000 := by
  unfold conventionalFee conventionalActions MARGINAL_FEE GRACE_ACTIONS; rfl

end Zebra.Zip317
