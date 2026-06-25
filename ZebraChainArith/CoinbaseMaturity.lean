import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Coinbase maturity from `zebra-chain/src/transparent.rs`

A transparent coinbase output created at height `created_height` may only be
spent at `spend_height ≥ created_height + MIN_TRANSPARENT_COINBASE_MATURITY`
(see ZIP/protocol §7.1, quoted in the Rust source).

We model heights as `Nat`, matching `Height(u32)` in
`zebra-chain/src/block/height.rs`. The maturity constant comes from
`zebra-chain/src/transparent.rs:54`.
-/

namespace Zebra.CoinbaseMaturity

/-- The maturity threshold for transparent coinbase outputs (in blocks).
Source: `zebra-chain/src/transparent.rs:54`
(`pub const MIN_TRANSPARENT_COINBASE_MATURITY: u32 = 100;`) -/
def MIN_TRANSPARENT_COINBASE_MATURITY : Nat := 100

/-- Predicate: a coinbase output created at `created_height` may be spent at
`spend_height`. The rule is `spend_height ≥ created_height + 100`.
Source: `zebra-chain/src/transparent.rs:45` (doc + constant). -/
def canSpend (createdHeight spendHeight : Nat) : Prop :=
  spendHeight ≥ createdHeight + MIN_TRANSPARENT_COINBASE_MATURITY

instance (c s : Nat) : Decidable (canSpend c s) :=
  inferInstanceAs (Decidable (s ≥ c + MIN_TRANSPARENT_COINBASE_MATURITY))

/-- The smallest spend height at which a coinbase from `createdHeight` matures. -/
def minSpendHeight (createdHeight : Nat) : Nat :=
  createdHeight + MIN_TRANSPARENT_COINBASE_MATURITY

/-! ## Theorems -/

/-- **T1.** `canSpend` holds iff the spend height is at least
`createdHeight + 100`. -/
theorem canSpend_iff (c s : Nat) :
    canSpend c s ↔ s ≥ c + MIN_TRANSPARENT_COINBASE_MATURITY := Iff.rfl

/-- **T2.** Immature: any spend strictly within the 100-block window is
rejected. -/
theorem cannot_spend_before_maturity (c s : Nat)
    (h : s < c + MIN_TRANSPARENT_COINBASE_MATURITY) : ¬ canSpend c s := by
  unfold canSpend; omega

/-- **T3.** Mature: the spend is allowed exactly at `c + 100`. -/
theorem can_spend_at_maturity (c : Nat) :
    canSpend c (c + MIN_TRANSPARENT_COINBASE_MATURITY) := by
  unfold canSpend; omega

/-- **T4.** Monotonicity in the spend height: a permitted spend remains
permitted at any later height. -/
theorem canSpend_mono_spend (c s s' : Nat)
    (hOk : canSpend c s) (hLe : s ≤ s') : canSpend c s' := by
  unfold canSpend at *; omega

/-- **T5.** Antitone in the creation height: lowering the creation height
preserves permission. -/
theorem canSpend_antitone_created (c c' s : Nat)
    (hOk : canSpend c s) (hLe : c' ≤ c) : canSpend c' s := by
  unfold canSpend at *; omega

/-- **T6.** `minSpendHeight` is the threshold: `canSpend c s ↔ minSpendHeight c ≤ s`. -/
theorem canSpend_iff_min (c s : Nat) :
    canSpend c s ↔ minSpendHeight c ≤ s := by
  unfold canSpend minSpendHeight; constructor <;> intro h <;> omega

/-- **T7.** The constant is exactly `100`. -/
theorem maturity_value : MIN_TRANSPARENT_COINBASE_MATURITY = 100 := rfl

/-- **T8.** Genesis case: a coinbase created at height 0 is spendable at
height 100, but not at height 99. -/
theorem genesis_maturity :
    canSpend 0 100 ∧ ¬ canSpend 0 99 := by
  refine ⟨?_, ?_⟩
  · unfold canSpend; decide
  · unfold canSpend; decide

/-- **T9.** Difference characterization: when the spend is allowed, the gap
`s - c` is at least 100 (over `Nat`). -/
theorem canSpend_diff_ge (c s : Nat) (h : canSpend c s) :
    s - c ≥ MIN_TRANSPARENT_COINBASE_MATURITY := by
  unfold canSpend at h; omega

/-- **T10.** Converse of T9: if the natural-number gap is at least 100, the
spend is allowed. -/
theorem diff_ge_canSpend (c s : Nat)
    (h : s - c ≥ MIN_TRANSPARENT_COINBASE_MATURITY) (hle : c ≤ s) :
    canSpend c s := by
  unfold canSpend; omega

end Zebra.CoinbaseMaturity
