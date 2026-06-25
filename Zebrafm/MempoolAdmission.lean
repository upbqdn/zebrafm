import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# ZIP-317 mempool admission

Models the mempool admission checks from
`zebra-chain/src/transaction/unmined/zip317.rs` (`mempool_checks` at
`zip317.rs:173-232`). Two checks must pass:

1. **Unpaid-actions check**: a transaction's `unpaid_actions` must not
   exceed `BLOCK_UNPAID_ACTION_LIMIT` (currently `0`).
2. **Legacy fee check**: the miner fee must be at least the minimum
   relay fee `min_fee(transaction_size)`, where
   `min_fee = clamp(MIN_MEMPOOL_TX_FEE_RATE * size / 1000,
                    MIN_MEMPOOL_TX_FEE_RATE, MEMPOOL_TX_FEE_REQUIREMENT_CAP)`.

`unpaid_actions` is computed from `conventional_actions(transaction)` and
the miner fee. In Rust, `conventional_actions = max(logical_actions,
GRACE_ACTIONS = 2)`, so it is always at least `2`. We model this lower
bound explicitly via the `ConventionalActions` subtype so a Lean caller
cannot pass `0` or `1`.

The Rust source has an in-code note about redundancy:
> If the check above for the maximum number of unpaid actions passes with
> `BLOCK_UNPAID_ACTION_LIMIT` set to zero, then there is no way for the
> legacy check below to fail. This renders the legacy check redundant in
> that case.

We prove this redundancy claim (T_redundancy) under the deployed value
`BLOCK_UNPAID_ACTION_LIMIT = 0`.

References:
- `MARGINAL_FEE` at `zip317.rs:23`
- `GRACE_ACTIONS` at `zip317.rs:26`
- `BLOCK_UNPAID_ACTION_LIMIT` at `zip317.rs:50`
- `MIN_MEMPOOL_TX_FEE_RATE` at `zip317.rs:59`
- `MEMPOOL_TX_FEE_REQUIREMENT_CAP` at `zip317.rs:67`
- `unpaid_actions` at `zip317.rs:90`
- `conventional_actions` at `zip317.rs:140`
- `mempool_checks` at `zip317.rs:173`

[ZIP-317]: <https://zips.z.cash/zip-0317#transaction-relaying>
-/

namespace Zebra.MempoolAdmission

/-! ## Constants -/

/-- `MARGINAL_FEE` in zatoshis per logical action.
Source: `zebra-chain/src/transaction/unmined/zip317.rs:23` -/
def MARGINAL_FEE : Nat := 5_000

/-- `GRACE_ACTIONS`: the floor on `conventional_actions`.
Source: `zebra-chain/src/transaction/unmined/zip317.rs:26` -/
def GRACE_ACTIONS : Nat := 2

/-- `BLOCK_UNPAID_ACTION_LIMIT`.
Source: `zebra-chain/src/transaction/unmined/zip317.rs:50` -/
def BLOCK_UNPAID_ACTION_LIMIT : Nat := 0

/-- `MIN_MEMPOOL_TX_FEE_RATE` in zatoshis per kilobyte.
Source: `zebra-chain/src/transaction/unmined/zip317.rs:59` -/
def MIN_MEMPOOL_TX_FEE_RATE : Nat := 100

/-- `MEMPOOL_TX_FEE_REQUIREMENT_CAP` in zatoshis.
Source: `zebra-chain/src/transaction/unmined/zip317.rs:67` -/
def MEMPOOL_TX_FEE_REQUIREMENT_CAP : Nat := 1_000

/-- One kilobyte, used in the legacy fee-rate calculation.
Source: `zebra-chain/src/transaction/unmined/zip317.rs:212` (`KILOBYTE`) -/
def KILOBYTE : Nat := 1_000

/-- `MAX_BLOCK_BYTES`: 2 MB. Transactions are bounded by the block size.
Source: `zebra-chain/src/block/serialize.rs:24` -/
def MAX_BLOCK_BYTES : Nat := 2_000_000

/-! ## Conventional actions -/

/-- A `ConventionalActions` is the output of Rust's `conventional_actions`
function, which always returns `max(logical_actions, GRACE_ACTIONS)`. We
encode the `≥ GRACE_ACTIONS` invariant via a subtype so a caller cannot
construct a value of `0` or `1`.

Source: `zebra-chain/src/transaction/unmined/zip317.rs:140-170`
(`conventional_actions`, ending in `max(GRACE_ACTIONS, logical_actions)`). -/
def ConventionalActions : Type := { n : Nat // GRACE_ACTIONS ≤ n }

/-- Smart constructor: take any natural and clamp it from below at
`GRACE_ACTIONS`, mirroring `max(GRACE_ACTIONS, logical_actions)`. -/
def mkConventional (logicalActions : Nat) : ConventionalActions :=
  ⟨max GRACE_ACTIONS logicalActions, Nat.le_max_left _ _⟩

/-- The underlying `Nat` of a `ConventionalActions`. -/
@[reducible] def ConventionalActions.toNat (c : ConventionalActions) : Nat := c.val

/-! ## Unpaid actions and admission -/

/-- `unpaid_actions = max(0, conventional_actions - floor(miner_fee /
MARGINAL_FEE))`.

In Rust, this is computed as `i64::from(conv) - (fee / MARGINAL_FEE) as i64`
and then `try_into().unwrap_or_default()` saturates negatives to `0`. We
model this directly on `Nat` using truncating subtraction, which agrees
with the Rust `i64`-then-`u32` clipping path. The first argument is a
`ConventionalActions`, encoding the Rust invariant `conv ≥ GRACE_ACTIONS`.

Source: `zebra-chain/src/transaction/unmined/zip317.rs:90-106` -/
def unpaidActions (c : ConventionalActions) (minerFee : Nat) : Nat :=
  c.toNat - (minerFee / MARGINAL_FEE)

/-- The unpaid-actions check: `unpaid_actions ≤ BLOCK_UNPAID_ACTION_LIMIT`.
Source: `zebra-chain/src/transaction/unmined/zip317.rs:185-187` -/
def unpaidActionsCheck (c : ConventionalActions) (minerFee : Nat) : Bool :=
  unpaidActions c minerFee ≤ BLOCK_UNPAID_ACTION_LIMIT

/-- The legacy minimum mempool fee for a transaction of `transaction_size`
bytes: `clamp(MIN_MEMPOOL_TX_FEE_RATE * size / KILOBYTE,
              MIN_MEMPOOL_TX_FEE_RATE, MEMPOOL_TX_FEE_REQUIREMENT_CAP)`.

Source: `zebra-chain/src/transaction/unmined/zip317.rs:220-223` -/
def minFee (transactionSize : Nat) : Nat :=
  let raw := MIN_MEMPOOL_TX_FEE_RATE * transactionSize / KILOBYTE
  min MEMPOOL_TX_FEE_REQUIREMENT_CAP (max MIN_MEMPOOL_TX_FEE_RATE raw)

/-- The legacy fee check: `miner_fee ≥ min_fee(transaction_size)`.
Source: `zebra-chain/src/transaction/unmined/zip317.rs:227-229` -/
def legacyFeeCheck (minerFee transactionSize : Nat) : Bool :=
  minFee transactionSize ≤ minerFee

/-- The full `mempool_checks` admission predicate: both the unpaid-actions
check and the legacy fee check must pass.

Source: `zebra-chain/src/transaction/unmined/zip317.rs:173-232` -/
def admitted (c : ConventionalActions) (minerFee transactionSize : Nat) : Bool :=
  unpaidActionsCheck c minerFee && legacyFeeCheck minerFee transactionSize

/-! ## Theorems -/

/-- **T1 (unpaid-actions check iff fee pays full conventional actions).**
The unpaid-actions check (with `BLOCK_UNPAID_ACTION_LIMIT = 0`) holds iff
`floor(miner_fee / MARGINAL_FEE) ≥ conventional_actions`. -/
theorem unpaidActionsCheck_iff (c : ConventionalActions) (f : Nat) :
    unpaidActionsCheck c f = true ↔ c.toNat ≤ f / MARGINAL_FEE := by
  unfold unpaidActionsCheck unpaidActions BLOCK_UNPAID_ACTION_LIMIT
  simp [Nat.sub_eq_zero_iff_le, decide_eq_true_eq]

/-- **T2 (unpaid actions bounded by conventional actions).** The number of
unpaid actions never exceeds the number of conventional actions. -/
theorem unpaidActions_le_conventional (c : ConventionalActions) (f : Nat) :
    unpaidActions c f ≤ c.toNat := by
  unfold unpaidActions
  exact Nat.sub_le _ _

/-- **T3 (no unpaid actions when fee is sufficient).** If the miner fee is
at least `MARGINAL_FEE * conventional_actions`, then `unpaid_actions = 0`. -/
theorem unpaidActions_zero_of_fee_ge (c : ConventionalActions) (f : Nat)
    (hf : MARGINAL_FEE * c.toNat ≤ f) : unpaidActions c f = 0 := by
  unfold unpaidActions
  apply Nat.sub_eq_zero_of_le
  have hM : 0 < MARGINAL_FEE := by unfold MARGINAL_FEE; decide
  exact (Nat.le_div_iff_mul_le hM).mpr (by linarith [Nat.mul_comm c.toNat MARGINAL_FEE])

/-- **T4 (unpaid-actions check monotone in fee).** Raising the miner fee
never turns a passing unpaid-actions check into a failing one. -/
theorem unpaidActionsCheck_monotone_fee (c : ConventionalActions) (f₁ f₂ : Nat)
    (hle : f₁ ≤ f₂) (h₁ : unpaidActionsCheck c f₁ = true) :
    unpaidActionsCheck c f₂ = true := by
  rw [unpaidActionsCheck_iff] at h₁ ⊢
  exact h₁.trans (Nat.div_le_div_right hle)

/-- **T5 (unpaid-actions check antitone in conventional actions).** Reducing
`conventional_actions` (while staying above `GRACE_ACTIONS`) never turns a
passing unpaid-actions check into a failing one. -/
theorem unpaidActionsCheck_antitone_actions (c₁ c₂ : ConventionalActions) (f : Nat)
    (hle : c₁.toNat ≤ c₂.toNat) (h₂ : unpaidActionsCheck c₂ f = true) :
    unpaidActionsCheck c₁ f = true := by
  rw [unpaidActionsCheck_iff] at h₂ ⊢
  exact hle.trans h₂

/-- **T6 (sufficient fee passes unpaid-actions check).** Paying at least
`MARGINAL_FEE * conventional_actions` zatoshis passes the unpaid-actions
check. -/
theorem unpaidActionsCheck_of_fee_ge (c : ConventionalActions) (f : Nat)
    (hf : MARGINAL_FEE * c.toNat ≤ f) : unpaidActionsCheck c f = true := by
  rw [unpaidActionsCheck_iff]
  have hM : 0 < MARGINAL_FEE := by unfold MARGINAL_FEE; decide
  exact (Nat.le_div_iff_mul_le hM).mpr (by linarith [Nat.mul_comm c.toNat MARGINAL_FEE])

/-- **T7 (conventional actions are at least `GRACE_ACTIONS`).** The
`ConventionalActions` subtype enforces the Rust invariant
`conventional_actions ≥ GRACE_ACTIONS = 2`. -/
theorem conventional_ge_grace (c : ConventionalActions) :
    GRACE_ACTIONS ≤ c.toNat := c.property

/-- **T8 (smart constructor reaches floor at zero logical actions).**
`mkConventional 0 = GRACE_ACTIONS`, matching Rust's
`max(GRACE_ACTIONS, 0) = GRACE_ACTIONS`. -/
theorem mkConventional_zero :
    (mkConventional 0).toNat = GRACE_ACTIONS := by
  unfold mkConventional ConventionalActions.toNat GRACE_ACTIONS
  decide

/-- **T9 (smart constructor preserves large logical actions).** When
`logical_actions ≥ GRACE_ACTIONS`, `mkConventional` is the identity. -/
theorem mkConventional_of_ge (n : Nat) (h : GRACE_ACTIONS ≤ n) :
    (mkConventional n).toNat = n := by
  unfold mkConventional ConventionalActions.toNat
  exact max_eq_right h

/-- **T10 (`minFee` lower-bounded by `MIN_MEMPOOL_TX_FEE_RATE`).** Because
the inner `max` floors at `MIN_MEMPOOL_TX_FEE_RATE` and the outer cap
exceeds that floor, the legacy minimum fee is always at least
`MIN_MEMPOOL_TX_FEE_RATE`. -/
theorem minFee_ge_floor (size : Nat) :
    MIN_MEMPOOL_TX_FEE_RATE ≤ minFee size := by
  unfold minFee MIN_MEMPOOL_TX_FEE_RATE MEMPOOL_TX_FEE_REQUIREMENT_CAP
  -- `min 1000 (max 100 raw) ≥ 100` since `max 100 raw ≥ 100` and `1000 ≥ 100`.
  refine Nat.le_min.mpr ⟨?_, ?_⟩
  · decide
  · exact Nat.le_max_left _ _

/-- **T11 (`minFee` upper-bounded by `MEMPOOL_TX_FEE_REQUIREMENT_CAP`).** -/
theorem minFee_le_cap (size : Nat) :
    minFee size ≤ MEMPOOL_TX_FEE_REQUIREMENT_CAP := by
  unfold minFee
  exact Nat.min_le_left _ _

/-- **T12 (legacy check monotone in fee).** Raising the miner fee never
turns a passing legacy check into a failing one. -/
theorem legacyFeeCheck_monotone_fee (f₁ f₂ size : Nat)
    (hle : f₁ ≤ f₂) (h₁ : legacyFeeCheck f₁ size = true) :
    legacyFeeCheck f₂ size = true := by
  unfold legacyFeeCheck at *
  simp only [decide_eq_true_eq] at *
  exact h₁.trans hle

/-- **T13 (admitted is monotone in fee).** Raising the miner fee never
turns an admitted transaction into a rejected one. -/
theorem admitted_monotone_fee (c : ConventionalActions) (f₁ f₂ size : Nat)
    (hle : f₁ ≤ f₂) (h₁ : admitted c f₁ size = true) :
    admitted c f₂ size = true := by
  unfold admitted at *
  rw [Bool.and_eq_true] at *
  exact ⟨unpaidActionsCheck_monotone_fee c f₁ f₂ hle h₁.1,
         legacyFeeCheck_monotone_fee f₁ f₂ size hle h₁.2⟩

/-- **T14 (admission redundancy claim, headline theorem).**

This formalises the Rust source comment at `zip317.rs:208-210`:

> If the check above for the maximum number of unpaid actions passes with
> `BLOCK_UNPAID_ACTION_LIMIT` set to zero, then there is no way for the
> legacy check below to fail.

Under `BLOCK_UNPAID_ACTION_LIMIT = 0` (the deployed value), and given the
Rust invariants `conventional_actions ≥ GRACE_ACTIONS = 2` and
`transaction_size ≤ MAX_BLOCK_BYTES = 2_000_000`, the unpaid-actions
check passing implies the legacy fee check also passes. Hence the legacy
check is redundant, matching the Rust comment.

Proof sketch: if the unpaid-actions check passes, then
`miner_fee / MARGINAL_FEE ≥ conventional_actions ≥ GRACE_ACTIONS = 2`, so
`miner_fee ≥ 2 * MARGINAL_FEE = 10_000`. The legacy minimum fee is capped
above by `MEMPOOL_TX_FEE_REQUIREMENT_CAP = 1_000`, so `miner_fee ≥ 10_000
> 1_000 ≥ min_fee(size)`. -/
theorem unpaidActions_implies_legacy
    (c : ConventionalActions) (minerFee transactionSize : Nat)
    (hu : unpaidActionsCheck c minerFee = true) :
    legacyFeeCheck minerFee transactionSize = true := by
  -- Convert the passing unpaid-actions check to the fee-vs-actions inequality.
  rw [unpaidActionsCheck_iff] at hu
  -- `conventional_actions ≥ GRACE_ACTIONS = 2`.
  have hge : GRACE_ACTIONS ≤ c.toNat := c.property
  -- So `miner_fee / MARGINAL_FEE ≥ GRACE_ACTIONS`.
  have hdiv : GRACE_ACTIONS ≤ minerFee / MARGINAL_FEE := hge.trans hu
  -- Therefore `MARGINAL_FEE * GRACE_ACTIONS ≤ minerFee`.
  have hM : 0 < MARGINAL_FEE := by unfold MARGINAL_FEE; decide
  have hfee_ge : MARGINAL_FEE * GRACE_ACTIONS ≤ minerFee :=
    (Nat.le_div_iff_mul_le hM).mp hdiv
  -- `MARGINAL_FEE * GRACE_ACTIONS = 10_000 ≥ MEMPOOL_TX_FEE_REQUIREMENT_CAP = 1_000`.
  have hcap : MEMPOOL_TX_FEE_REQUIREMENT_CAP ≤ MARGINAL_FEE * GRACE_ACTIONS := by
    unfold MEMPOOL_TX_FEE_REQUIREMENT_CAP MARGINAL_FEE GRACE_ACTIONS; decide
  -- And `min_fee size ≤ MEMPOOL_TX_FEE_REQUIREMENT_CAP`.
  have hmin : minFee transactionSize ≤ MEMPOOL_TX_FEE_REQUIREMENT_CAP :=
    minFee_le_cap transactionSize
  unfold legacyFeeCheck
  simp only [decide_eq_true_eq]
  exact (hmin.trans hcap).trans hfee_ge

/-- **T15 (admission iff unpaid-actions check, under deployed limits).**
A direct consequence of T14: under `BLOCK_UNPAID_ACTION_LIMIT = 0`, the
full `mempool_checks` predicate is logically equivalent to the
unpaid-actions check alone. -/
theorem admitted_iff_unpaidActionsCheck
    (c : ConventionalActions) (minerFee transactionSize : Nat) :
    admitted c minerFee transactionSize = true ↔
    unpaidActionsCheck c minerFee = true := by
  unfold admitted
  rw [Bool.and_eq_true]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  exact unpaidActions_implies_legacy c minerFee transactionSize h

/-- **T16 (zero-action floor: minimal-conventional tx admitted with
2 * MARGINAL_FEE = 10_000 zatoshi fee).** A transaction at the
`GRACE_ACTIONS = 2` floor is admitted by paying `2 * MARGINAL_FEE` zatoshi
or more (any non-negative size), since the legacy check is automatically
satisfied by T14. -/
theorem admitted_minimal_concrete (size : Nat) :
    admitted (mkConventional 0) 10_000 size = true := by
  rw [admitted_iff_unpaidActionsCheck, unpaidActionsCheck_iff,
      mkConventional_zero]
  unfold GRACE_ACTIONS MARGINAL_FEE
  decide

/-- **T17 (insufficient fee, concrete).** A transaction with 3
conventional actions and a fee of `2 * MARGINAL_FEE - 1 = 9_999` zatoshi
is NOT admitted (the unpaid-actions check fails: `9_999 / 5_000 = 1 < 3`). -/
theorem admitted_insufficient_concrete :
    admitted (mkConventional 3) 9_999 1_000 = false := by
  -- The unpaid-actions check alone fails.
  apply Bool.and_eq_false_iff.mpr
  left
  unfold unpaidActionsCheck unpaidActions BLOCK_UNPAID_ACTION_LIMIT
    mkConventional ConventionalActions.toNat MARGINAL_FEE GRACE_ACTIONS
  decide

/-- **T18 (boundary fee, concrete).** A transaction with 3 conventional
actions and a fee of exactly `3 * MARGINAL_FEE = 15_000` zatoshi is
admitted, for any in-range transaction size. -/
theorem admitted_boundary_concrete :
    admitted (mkConventional 3) 15_000 1_000 = true := by
  rw [admitted_iff_unpaidActionsCheck, unpaidActionsCheck_iff,
      mkConventional_of_ge 3 (by unfold GRACE_ACTIONS; decide)]
  unfold MARGINAL_FEE
  decide

end Zebra.MempoolAdmission
