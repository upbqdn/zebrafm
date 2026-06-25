import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# ZIP-317 mempool admission

Models the "unpaid actions" check for mempool admission from
`zebra-chain/src/transaction/unmined/zip317.rs`.

A transaction is admitted iff its `unpaid_actions` does not exceed
`BLOCK_UNPAID_ACTION_LIMIT`. In current Zebra, that limit is `0`, so a
transaction is admitted iff `unpaid_actions = 0`, equivalently iff the
miner fee pays for the full set of conventional actions:

  `floor(miner_fee / MARGINAL_FEE) ≥ conventional_actions`.

Reference:
- `BLOCK_UNPAID_ACTION_LIMIT` at `zip317.rs:50`
- `unpaid_actions` at `zip317.rs:90`
- `mempool_checks` at `zip317.rs:173`

[ZIP-317]: <https://zips.z.cash/zip-0317#transaction-relaying>
-/

namespace Zebra.MempoolAdmission

/-- `MARGINAL_FEE` in zatoshis per logical action.
Source: `zebra-chain/src/transaction/unmined/zip317.rs:23` -/
def MARGINAL_FEE : Nat := 5_000

/-- `BLOCK_UNPAID_ACTION_LIMIT`.
Source: `zebra-chain/src/transaction/unmined/zip317.rs:50` -/
def BLOCK_UNPAID_ACTION_LIMIT : Nat := 0

/-- `unpaid_actions = max(0, conventional_actions - floor(miner_fee / MARGINAL_FEE))`.

In Rust, this is computed as `i64::from(conv) - (fee / MARGINAL_FEE) as i64`
and then `try_into().unwrap_or_default()` saturates negatives to `0`. We
model this directly on `Nat` using truncating subtraction, which agrees
with the Rust `i64`-then-`u32` clipping path.

Source: `zebra-chain/src/transaction/unmined/zip317.rs:90` -/
def unpaidActions (conventionalActions minerFee : Nat) : Nat :=
  conventionalActions - (minerFee / MARGINAL_FEE)

/-- `mempool_checks` admission predicate restricted to the unpaid-actions
rule: a transaction is admitted iff `unpaid_actions ≤ BLOCK_UNPAID_ACTION_LIMIT`.

Source: `zebra-chain/src/transaction/unmined/zip317.rs:185` -/
def admitted (conventionalActions minerFee : Nat) : Bool :=
  unpaidActions conventionalActions minerFee ≤ BLOCK_UNPAID_ACTION_LIMIT

/-! ## Theorems -/

/-- **T1 (admission iff fee pays full conventional actions).**
A transaction is admitted iff `floor(miner_fee / MARGINAL_FEE) ≥
conventional_actions`. -/
theorem admitted_iff (c f : Nat) :
    admitted c f = true ↔ c ≤ f / MARGINAL_FEE := by
  unfold admitted unpaidActions BLOCK_UNPAID_ACTION_LIMIT
  simp [Nat.sub_eq_zero_iff_le, decide_eq_true_eq]

/-- **T2 (unpaid actions bounded by conventional actions).**
The number of unpaid actions never exceeds the number of conventional
actions. -/
theorem unpaidActions_le_conventional (c f : Nat) :
    unpaidActions c f ≤ c := by
  unfold unpaidActions
  exact Nat.sub_le _ _

/-- **T3 (no unpaid actions when fee is sufficient).**
If the miner fee is at least `MARGINAL_FEE * conventional_actions`, then
`unpaid_actions = 0`. -/
theorem unpaidActions_zero_of_fee_ge (c f : Nat)
    (hf : MARGINAL_FEE * c ≤ f) : unpaidActions c f = 0 := by
  unfold unpaidActions
  apply Nat.sub_eq_zero_of_le
  -- need: c ≤ f / MARGINAL_FEE
  have hM : 0 < MARGINAL_FEE := by unfold MARGINAL_FEE; decide
  exact (Nat.le_div_iff_mul_le hM).mpr (by linarith [Nat.mul_comm c MARGINAL_FEE])

/-- **T4 (admission monotone in fee).** Raising the miner fee never
turns an admitted transaction into a rejected one. -/
theorem admitted_monotone_fee (c f₁ f₂ : Nat)
    (hle : f₁ ≤ f₂) (h₁ : admitted c f₁ = true) :
    admitted c f₂ = true := by
  rw [admitted_iff] at h₁ ⊢
  exact h₁.trans (Nat.div_le_div_right hle)

/-- **T5 (admission antitone in conventional actions).** Lowering the
number of conventional actions never turns an admitted transaction into
a rejected one. -/
theorem admitted_antitone_actions (c₁ c₂ f : Nat)
    (hle : c₁ ≤ c₂) (h₂ : admitted c₂ f = true) :
    admitted c₁ f = true := by
  rw [admitted_iff] at h₂ ⊢
  exact hle.trans h₂

/-- **T6 (sufficient fee admits).** Paying at least `MARGINAL_FEE *
conventional_actions` zatoshis admits the transaction. -/
theorem admitted_of_fee_ge (c f : Nat) (hf : MARGINAL_FEE * c ≤ f) :
    admitted c f = true := by
  rw [admitted_iff]
  have hM : 0 < MARGINAL_FEE := by unfold MARGINAL_FEE; decide
  exact (Nat.le_div_iff_mul_le hM).mpr (by linarith [Nat.mul_comm c MARGINAL_FEE])

/-- **T7 (zero-action tx always admitted).** A transaction with zero
conventional actions is always admitted, regardless of fee. -/
theorem admitted_zero_actions (f : Nat) : admitted 0 f = true := by
  rw [admitted_iff]; exact Nat.zero_le _

/-- **T8 (insufficient fee, concrete).** A transaction with 3
conventional actions and a fee of `2 * MARGINAL_FEE - 1 = 9999`
zatoshis is NOT admitted. -/
theorem admitted_insufficient_concrete :
    admitted 3 9_999 = false := by
  unfold admitted unpaidActions MARGINAL_FEE BLOCK_UNPAID_ACTION_LIMIT
  decide

/-- **T9 (boundary fee, concrete).** A transaction with 3 conventional
actions and a fee of exactly `3 * MARGINAL_FEE = 15_000` zatoshis is
admitted. -/
theorem admitted_boundary_concrete :
    admitted 3 15_000 = true := by
  unfold admitted unpaidActions MARGINAL_FEE BLOCK_UNPAID_ACTION_LIMIT
  decide

end Zebra.MempoolAdmission
