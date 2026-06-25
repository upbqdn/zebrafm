import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Coinbase spend restrictions from `zebra-chain` / `zebra-state`

A transparent coinbase output is governed by two restrictions, encoded by the
Rust enum `CoinbaseSpendRestriction` in
`zebra-chain/src/transparent/utxo.rs:117-140`:

* `CheckCoinbaseMaturity { spend_height }` — the output may only be spent at
  `spend_height ≥ created_height + MIN_TRANSPARENT_COINBASE_MATURITY`, where
  `MIN_TRANSPARENT_COINBASE_MATURITY = 100` (`zebra-chain/src/transparent.rs:54`,
  re-exported via `zebra-state/src/constants.rs`).
* `DisallowCoinbaseSpend` — the spend is rejected outright because the
  spending transaction has transparent outputs on a network that requires
  shielded-only coinbase spends (the historical zcashd "shielded coinbase"
  policy, retained as a per-network gate after Heartwood).

Which variant applies is chosen by
`Transaction::coinbase_spend_restriction` in
`zebra-chain/src/transaction.rs:360-372`, based on whether the spending
transaction has any transparent outputs and the network's
`should_allow_unshielded_coinbase_spends` flag. The actual check is performed
by `transparent_coinbase_spend` in
`zebra-state/src/service/check/utxo.rs:190-217`.

We model heights as `Nat`, matching `Height(u32)` in
`zebra-chain/src/block/height.rs`.
-/

namespace Zebra.CoinbaseMaturity

/-- The maturity threshold for transparent coinbase outputs (in blocks).
Source: `zebra-chain/src/transparent.rs:54`
(`pub const MIN_TRANSPARENT_COINBASE_MATURITY: u32 = 100;`) -/
def MIN_TRANSPARENT_COINBASE_MATURITY : Nat := 100

/-- The `CoinbaseSpendRestriction` enum, mirroring
`zebra-chain/src/transparent/utxo.rs:127-140`. -/
inductive SpendRestriction
  /-- Maturity-only check: spend is rejected before
  `spend_height ≥ created_height + 100`. -/
  | checkCoinbaseMaturity (spendHeight : Nat)
  /-- Spend is rejected outright (transparent-output spend on a network that
  requires shielded coinbase spends). -/
  | disallowCoinbaseSpend
  deriving DecidableEq, Repr

/-- The two Zcash networks plus Regtest, abstracted to a Boolean: `true` iff
the network allows unshielded coinbase spends (i.e. coinbase outputs may be
spent by transactions that themselves have transparent outputs).

* Mainnet: `false` (shielded coinbase mandatory).
* Default Testnet: `false`.
* Default Regtest: `true`.

A user-configured Testnet/Regtest may override this. Mirrors
`Network::should_allow_unshielded_coinbase_spends` in
`zebra-chain/src/parameters/network/testnet.rs:1252-1261`. -/
abbrev ShouldAllowUnshielded := Bool

/-- The output side of `Transaction::coinbase_spend_restriction`:
mirrors the boolean `outputs().is_empty()`. `true` iff the spending
transaction has *no* transparent outputs (so the spend is shielded). -/
abbrev NoTransparentOutputs := Bool

/-- The variant chooser from `Transaction::coinbase_spend_restriction` at
`zebra-chain/src/transaction.rs:365-371`:

```rust
if self.outputs().is_empty() || network.should_allow_unshielded_coinbase_spends() {
    CheckCoinbaseMaturity { spend_height }
} else {
    DisallowCoinbaseSpend
}
```

Note that an output-empty spending transaction is *always* checked for
maturity only, even on networks where unshielded spends are disallowed —
because if there are no transparent outputs, the spend is shielded by
construction. -/
def coinbaseSpendRestriction
    (noTransparentOutputs : NoTransparentOutputs)
    (allowUnshielded : ShouldAllowUnshielded)
    (spendHeight : Nat) : SpendRestriction :=
  if noTransparentOutputs || allowUnshielded then
    .checkCoinbaseMaturity spendHeight
  else
    .disallowCoinbaseSpend

/-- The maturity predicate (the body of the `CheckCoinbaseMaturity` branch in
`transparent_coinbase_spend`,
`zebra-state/src/service/check/utxo.rs:200-213`). -/
def canSpend (createdHeight spendHeight : Nat) : Prop :=
  spendHeight ≥ createdHeight + MIN_TRANSPARENT_COINBASE_MATURITY

instance (c s : Nat) : Decidable (canSpend c s) :=
  inferInstanceAs (Decidable (s ≥ c + MIN_TRANSPARENT_COINBASE_MATURITY))

/-- The smallest spend height at which a coinbase from `createdHeight` matures. -/
def minSpendHeight (createdHeight : Nat) : Nat :=
  createdHeight + MIN_TRANSPARENT_COINBASE_MATURITY

/-- The outcome of `transparent_coinbase_spend` for a coinbase UTXO,
mirroring `Result<(), ValidateContextError>` in
`zebra-state/src/service/check/utxo.rs:190-217`. We only distinguish the
three relevant outcomes: success, immature, and unshielded. -/
inductive SpendOutcome
  /-- The spend is permitted. -/
  | ok
  /-- `ImmatureTransparentCoinbaseSpend`. -/
  | immature
  /-- `UnshieldedTransparentCoinbaseSpend`. -/
  | unshielded
  deriving DecidableEq, Repr

/-- The full `transparent_coinbase_spend` decision restricted to coinbase
UTXOs (the early-return `if !utxo.from_coinbase { return Ok(()); }` is hoisted
out at the call site). Mirrors
`zebra-state/src/service/check/utxo.rs:199-216`. -/
def transparentCoinbaseSpend
    (createdHeight : Nat) (r : SpendRestriction) : SpendOutcome :=
  match r with
  | .checkCoinbaseMaturity s =>
      if canSpend createdHeight s then .ok else .immature
  | .disallowCoinbaseSpend => .unshielded

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

/-! ## Theorems for the spend-restriction chooser -/

/-- **T11.** Shielded spends (transactions with no transparent outputs) are
*always* routed to the maturity-only check, regardless of network. This is
the `outputs().is_empty()` clause in
`zebra-chain/src/transaction.rs:365-368`. -/
theorem shielded_always_check_maturity (allow : ShouldAllowUnshielded) (h : Nat) :
    coinbaseSpendRestriction true allow h = .checkCoinbaseMaturity h := by
  unfold coinbaseSpendRestriction; rfl

/-- **T12.** On a network that permits unshielded coinbase spends, *every*
spending transaction (shielded or not) is routed to the maturity-only check.
This is the `should_allow_unshielded_coinbase_spends()` clause in
`zebra-chain/src/transaction.rs:365-368`. -/
theorem allow_unshielded_always_check_maturity
    (noTrans : NoTransparentOutputs) (h : Nat) :
    coinbaseSpendRestriction noTrans true h = .checkCoinbaseMaturity h := by
  unfold coinbaseSpendRestriction
  cases noTrans <;> rfl

/-- **T13.** A spending transaction with transparent outputs on a
shielded-coinbase-mandatory network is rejected outright with
`DisallowCoinbaseSpend`. This is the `else` branch at
`zebra-chain/src/transaction.rs:369-371`. -/
theorem unshielded_on_strict_network (h : Nat) :
    coinbaseSpendRestriction false false h = .disallowCoinbaseSpend := by
  unfold coinbaseSpendRestriction; rfl

/-- **T14.** Case-completeness: every choice of inputs falls into one of the
two variants — there is no third outcome. -/
theorem spendRestriction_dichotomy
    (noTrans : NoTransparentOutputs) (allow : ShouldAllowUnshielded) (h : Nat) :
    coinbaseSpendRestriction noTrans allow h = .checkCoinbaseMaturity h ∨
    coinbaseSpendRestriction noTrans allow h = .disallowCoinbaseSpend := by
  unfold coinbaseSpendRestriction
  cases noTrans <;> cases allow <;> simp

/-! ## Theorems for the full validation outcome -/

/-- **T15.** Maturity success path: a `CheckCoinbaseMaturity` restriction at
a mature spend height produces `ok`. -/
theorem coinbase_mature_ok (c s : Nat) (h : canSpend c s) :
    transparentCoinbaseSpend c (.checkCoinbaseMaturity s) = .ok := by
  unfold transparentCoinbaseSpend
  simp [h]

/-- **T16.** Maturity failure path: a `CheckCoinbaseMaturity` restriction
within the 100-block window produces `immature`. -/
theorem coinbase_immature (c s : Nat) (h : ¬ canSpend c s) :
    transparentCoinbaseSpend c (.checkCoinbaseMaturity s) = .immature := by
  unfold transparentCoinbaseSpend
  simp [h]

/-- **T17.** `DisallowCoinbaseSpend` always yields `unshielded`, regardless of
the creation height. This is the `_` => `Err(UnshieldedTransparentCoinbaseSpend …)`
arm at `zebra-state/src/service/check/utxo.rs:215`. -/
theorem disallow_is_unshielded (c : Nat) :
    transparentCoinbaseSpend c .disallowCoinbaseSpend = .unshielded := by
  rfl

/-- **T18.** End-to-end maturity success: a shielded transaction (or one on a
permissive network) at a mature height passes. -/
theorem end_to_end_mature
    (noTrans : NoTransparentOutputs) (allow : ShouldAllowUnshielded)
    (c s : Nat) (hShielded : noTrans = true ∨ allow = true)
    (hMature : canSpend c s) :
    transparentCoinbaseSpend c (coinbaseSpendRestriction noTrans allow s) = .ok := by
  rcases hShielded with h | h <;>
    simp [coinbaseSpendRestriction, transparentCoinbaseSpend, h, hMature]

/-- **T19.** End-to-end immature: even a shielded spend is rejected if the
output has not yet matured. -/
theorem end_to_end_immature
    (noTrans : NoTransparentOutputs) (allow : ShouldAllowUnshielded)
    (c s : Nat) (hShielded : noTrans = true ∨ allow = true)
    (hImm : ¬ canSpend c s) :
    transparentCoinbaseSpend c (coinbaseSpendRestriction noTrans allow s) =
      .immature := by
  rcases hShielded with h | h <;>
    simp [coinbaseSpendRestriction, transparentCoinbaseSpend, h, hImm]

/-- **T20.** End-to-end unshielded rejection: an unshielded spend on a strict
network is rejected with `unshielded`, *regardless* of maturity. This is the
crucial coverage gap noted in Finding 36 — maturity alone does not make an
unshielded spend valid. -/
theorem end_to_end_unshielded (c s : Nat) :
    transparentCoinbaseSpend c (coinbaseSpendRestriction false false s) =
      .unshielded := by
  unfold coinbaseSpendRestriction
  rfl

/-- **T21.** Strict-network rejection trumps maturity: even at a fully mature
height, an unshielded spend on a strict network is rejected. -/
theorem strict_network_rejects_mature_unshielded (c : Nat) :
    transparentCoinbaseSpend c
        (coinbaseSpendRestriction false false (c + MIN_TRANSPARENT_COINBASE_MATURITY)) =
      .unshielded := by
  unfold coinbaseSpendRestriction
  rfl

end Zebra.CoinbaseMaturity
