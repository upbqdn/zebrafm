import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# ZIP-211: Disable addition of new value to the Sprout chain value pool

ZIP-211 deactivates the Sprout shielded pool's input direction (the transparent
→ Sprout flow) at the Canopy network upgrade. Post-Canopy, every JoinSplit
description in every transaction must have `vpub_old = 0`: the Sprout pool can
still be drained (via `vpub_new`) but it can no longer be replenished.

In Zebra terminology (see `zebra-chain/src/transaction/joinsplit.rs:100-112`
and the per-`JoinSplit` `value_balance` at `zebra-chain/src/sprout/joinsplit.rs:178-189`):

  * `vpub_old` is the amount removed from the *transparent* pool and added to
    the *Sprout* pool — i.e. a "shielding" of transparent value into Sprout.
  * `vpub_new` is the amount removed from the *Sprout* pool and added to the
    *transparent* pool — i.e. an "unshielding" of Sprout value out.
  * The **per-JoinSplit transparent-pool value balance** is
    `value_balance = vpub_new − vpub_old`
    (the transparent-pool change due to the JoinSplit;
    `zebra-chain/src/sprout/joinsplit.rs:178`).
  * The corresponding **per-JoinSplit Sprout-pool value balance** is the
    negation:  `sprout_balance_change = vpub_old − vpub_new`.

The ZIP-211 consensus rule, as enforced in
`zebra-consensus/src/transaction/check.rs:218-246` (`disabled_add_to_sprout_pool`)
and quoted from <https://zips.z.cash/protocol/protocol.pdf#joinsplitdesc>, is:

> [Canopy onward]: `vpub_old` MUST be zero.

In this module we model a single JoinSplit's contribution to the two pools as
two `Nat`-valued amounts `vpubOld` (≥ 0) and `vpubNew` (≥ 0), with the Sprout
pool change as the `Int` `(vpubOld : Int) − (vpubNew : Int)`. We prove:

  * **T1 (literal per-JoinSplit rule).** At any height `h ≥ Canopy`, a
    `validTx`-admissible transaction has, **for every JoinSplit**, `vpub_old = 0`.
    This is the literal Rust check (`disabled_add_to_sprout_pool`,
    `zebra-consensus/src/transaction/check.rs:238-242`): the loop rejects on the
    first JoinSplit with non-zero `vpub_old`.
  * **T2 (pre-Canopy vacuity).** At any height `h < Canopy`, the ZIP-211
    rule is vacuous: no constraint is placed on the Sprout-pool change.
  * **T3 (drain-only is allowed).** A transaction with
    `sproutBalanceChange ≤ 0` is allowed at every height (pre- and
    post-Canopy alike).
  * **T4 (zero is trivially OK).** A transaction with
    `sproutBalanceChange = 0` satisfies the ZIP-211 rule at every height.

Plus a handful of supporting facts (sum-form corollary "Sprout pool can only
shrink", equivalence of the `vpub_old = 0` byte-level rule and the
`sproutBalanceChange ≤ 0` arithmetic rule, monotonicity-in-height, and concrete
witnesses).

Source: <https://zips.z.cash/zip-0211>
Source: `zebra-consensus/src/transaction/check.rs:215-246`
(`disabled_add_to_sprout_pool`)
Source: `zebra-chain/src/sprout/joinsplit.rs:169-190`
(`JoinSplit::value_balance`)
Source: `zebra-chain/src/parameters/constants.rs:60,87`
(mainnet/testnet Canopy activation heights)
-/

namespace Zebra.Zip211SproutClosed

/-! ## Canopy activation heights -/

/-- Mainnet Canopy activation height.
Source: `zebra-chain/src/parameters/constants.rs:87`
(`pub const CANOPY: Height = Height(1_046_400);`). -/
def CANOPY_MAINNET : Nat := 1_046_400

/-- Testnet Canopy activation height.
Source: `zebra-chain/src/parameters/constants.rs:61`
(`pub const CANOPY: Height = Height(1_028_500);`). -/
def CANOPY_TESTNET : Nat := 1_028_500

/-! ## Per-JoinSplit model

We model a single Sprout `JoinSplit` description by its two `NonNegative`
amounts. Following Rust's `Amount<NonNegative>` (always ≥ 0) we use `Nat`
for the on-the-wire fields and lift to `Int` for the signed Sprout-pool
balance change. -/

/-- A single Sprout `JoinSplit`. The two fields mirror
`zebra-chain/src/sprout/joinsplit.rs:66-69`:
  * `vpubOld` corresponds to `vpub_old : Amount<NonNegative>`;
  * `vpubNew` corresponds to `vpub_new : Amount<NonNegative>`.
The values are `Nat` because the Rust type is `NonNegative`-constrained. -/
structure JoinSplit where
  vpubOld : Nat
  vpubNew : Nat
  deriving DecidableEq, Repr

/-- The **transparent-pool value balance** contributed by a single JoinSplit,
as `vpub_new − vpub_old`.
Source: `zebra-chain/src/sprout/joinsplit.rs:178-189`
(`JoinSplit::value_balance`). -/
def JoinSplit.valueBalance (js : JoinSplit) : Int :=
  (js.vpubNew : Int) - (js.vpubOld : Int)

/-- The **Sprout-pool value balance** contributed by a single JoinSplit. This
is the negation of the transparent-pool balance: `vpub_old − vpub_new`.
The Sprout pool grows by `vpub_old` (transparent → Sprout) and shrinks by
`vpub_new` (Sprout → transparent). -/
def JoinSplit.sproutBalanceChange (js : JoinSplit) : Int :=
  (js.vpubOld : Int) - (js.vpubNew : Int)

/-! ## Transaction-level model

A transaction is just a list of JoinSplits (the only field that affects the
Sprout pool). The transaction-level Sprout-pool balance change is the sum
over all JoinSplits. -/

/-- A transaction, modelled as a list of JoinSplits. -/
structure Tx where
  joinSplits : List JoinSplit
  deriving Repr

/-- Per-transaction net change to the Sprout pool. -/
def Tx.sproutBalanceChange (tx : Tx) : Int :=
  (tx.joinSplits.map JoinSplit.sproutBalanceChange).sum

/-! ## ZIP-211 byte-level rule

`disabled_add_to_sprout_pool` (`zebra-consensus/src/transaction/check.rs:220`)
iterates over `tx.output_values_to_sprout()` (the `vpub_old` field of every
JoinSplit) and rejects any non-zero value at heights `≥ canopy_activation_height`.
-/

/-- The ZIP-211 byte-level predicate on a single JoinSplit, **after Canopy**.
Source: `zebra-consensus/src/transaction/check.rs:233-242`. -/
def JoinSplit.satisfiesZip211 (js : JoinSplit) : Prop :=
  js.vpubOld = 0

/-- The ZIP-211 byte-level predicate on a transaction, **after Canopy**:
every JoinSplit must have `vpub_old = 0`. -/
def Tx.satisfiesZip211 (tx : Tx) : Prop :=
  ∀ js ∈ tx.joinSplits, js.satisfiesZip211

/-! ## Height-conditional validity

The conditional rule: ZIP-211 only applies at heights `≥ Canopy`. -/

/-- The full height-conditional ZIP-211 rule, parameterised over a network's
Canopy activation height: at heights `≥ canopyHeight`, the transaction must
satisfy the byte-level ZIP-211 predicate; below `canopyHeight`, no constraint.
This is the literal `if height >= canopy_activation_height { ... }` shape of
`zebra-consensus/src/transaction/check.rs:233`. -/
def validTx (canopyHeight height : Nat) (tx : Tx) : Prop :=
  height ≥ canopyHeight → tx.satisfiesZip211

/-! ## Lemmas -/

/-- The Sprout-pool change is the negation of the transparent-pool change. -/
theorem JoinSplit.sproutBalanceChange_eq_neg_valueBalance (js : JoinSplit) :
    js.sproutBalanceChange = - js.valueBalance := by
  unfold JoinSplit.sproutBalanceChange JoinSplit.valueBalance
  ring

/-- The byte-level rule `vpub_old = 0` is *equivalent* to "Sprout pool can
only shrink": for a non-negative `vpub_new`, having `vpub_old = 0` gives
`sproutBalanceChange = - (vpub_new : Int) ≤ 0`. The converse also holds for
`Nat`-valued amounts. -/
theorem JoinSplit.satisfiesZip211_iff (js : JoinSplit) :
    js.satisfiesZip211 ↔ js.sproutBalanceChange ≤ -(js.vpubNew : Int) := by
  unfold JoinSplit.satisfiesZip211 JoinSplit.sproutBalanceChange
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    -- `(vpubOld : Int) - (vpubNew : Int) ≤ -(vpubNew : Int)`
    -- ⇒ `(vpubOld : Int) ≤ 0` ⇒ `vpubOld = 0` (since `vpubOld : Nat`).
    have h' : (js.vpubOld : Int) ≤ 0 := by linarith
    have : js.vpubOld ≤ 0 := by exact_mod_cast h'
    omega

/-! ## Helper lemmas (list-level, used by both T1 and T3′) -/

/-- List-level helper: if every JoinSplit in a list satisfies the byte rule,
the sum of their Sprout-balance changes is ≤ 0. -/
theorem list_satisfiesZip211_sum_nonpos (jss : List JoinSplit)
    (hAll : ∀ js ∈ jss, js.satisfiesZip211) :
    (jss.map JoinSplit.sproutBalanceChange).sum ≤ 0 := by
  induction jss with
  | nil => simp
  | cons js rest ih =>
    have hJs : js.satisfiesZip211 := hAll js List.mem_cons_self
    have hRestSat : ∀ js' ∈ rest, js'.satisfiesZip211 :=
      fun js' hMem => hAll js' (List.mem_cons_of_mem _ hMem)
    have hRest : (rest.map JoinSplit.sproutBalanceChange).sum ≤ 0 := ih hRestSat
    have hHead : js.sproutBalanceChange ≤ 0 := by
      unfold JoinSplit.sproutBalanceChange JoinSplit.satisfiesZip211 at *
      rw [hJs]
      simp
    simp only [List.map_cons, List.sum_cons]
    linarith

/-- List-level helper: under the byte rule, the sum of Sprout-balance changes
equals the negation of the sum of `vpub_new` values. -/
theorem list_satisfiesZip211_sum_eq_neg (jss : List JoinSplit)
    (hAll : ∀ js ∈ jss, js.satisfiesZip211) :
    (jss.map JoinSplit.sproutBalanceChange).sum =
      - ((jss.map (fun js => (js.vpubNew : Int))).sum) := by
  induction jss with
  | nil => simp
  | cons js rest ih =>
    have hJs : js.satisfiesZip211 := hAll js List.mem_cons_self
    have hRestSat : ∀ js' ∈ rest, js'.satisfiesZip211 :=
      fun js' hMem => hAll js' (List.mem_cons_of_mem _ hMem)
    have hRestEq := ih hRestSat
    have hHeadEq : js.sproutBalanceChange = - (js.vpubNew : Int) := by
      unfold JoinSplit.sproutBalanceChange JoinSplit.satisfiesZip211 at *
      rw [hJs]; simp
    simp only [List.map_cons, List.sum_cons]
    rw [hHeadEq, hRestEq]
    ring

/-! ## Main theorems -/

/-- **T1 (headline — literal per-JoinSplit rule).**
At any height `h ≥ Canopy` (for a given network's `canopyHeight`), every
JoinSplit in a `validTx`-admissible transaction has `vpub_old = 0`. This is
the *exact* shape of the Rust check (`zebra-consensus/src/transaction/
check.rs:238-242`): the consensus loop iterates over every JoinSplit and
rejects on the first one with non-zero `vpub_old`. The sum-form
"Sprout pool cannot grow" property is a downstream corollary
(see `T1_corollary_sprout_pool_nonpositive`). -/
theorem T1_post_canopy_every_vpub_old_zero
    (canopyHeight height : Nat) (tx : Tx)
    (hValid : validTx canopyHeight height tx)
    (hHeight : height ≥ canopyHeight) :
    ∀ js ∈ tx.joinSplits, js.vpubOld = 0 := by
  intro js hMem
  have hSat : tx.satisfiesZip211 := hValid hHeight
  exact hSat js hMem

/-- **T1 corollary (Sprout pool cannot grow post-Canopy).**
A direct arithmetic consequence of T1: the literal per-JoinSplit `vpub_old = 0`
implies (per JoinSplit, then summed) that the transaction's Sprout-pool change
is ≤ 0. Note this is *strictly weaker* than T1 itself (many transactions have
`sproutBalanceChange ≤ 0` without satisfying the byte rule), so it is the
*corollary*, not the rule. -/
theorem T1_corollary_sprout_pool_nonpositive
    (canopyHeight height : Nat) (tx : Tx)
    (hValid : validTx canopyHeight height tx)
    (hHeight : height ≥ canopyHeight) :
    tx.sproutBalanceChange ≤ 0 := by
  have hSat : tx.satisfiesZip211 := hValid hHeight
  exact list_satisfiesZip211_sum_nonpos tx.joinSplits hSat

/-- **T2 (pre-Canopy: rule is vacuous).** At any height `h < canopyHeight`,
the `validTx` predicate places no constraint on the transaction: every
transaction is `validTx`-admissible regardless of its `sproutBalanceChange`.
This says ZIP-211 imposes nothing prior to Canopy activation. -/
theorem T2_pre_canopy_vacuous
    (canopyHeight height : Nat) (tx : Tx)
    (hPre : height < canopyHeight) :
    validTx canopyHeight height tx := by
  unfold validTx
  intro hContra
  -- `height ≥ canopyHeight` together with `height < canopyHeight` is impossible.
  omega

/-- **T2′ (every transaction is valid pre-Canopy).** A stronger restatement
of T2 saying that pre-Canopy, *every* transaction shape — including one that
adds value to the Sprout pool — is `validTx`-admissible. -/
theorem T2_pre_canopy_all_admissible
    (canopyHeight height : Nat) (tx : Tx)
    (hPre : height < canopyHeight) (b : Int)
    (_hSprout : tx.sproutBalanceChange = b) :
    validTx canopyHeight height tx :=
  T2_pre_canopy_vacuous canopyHeight height tx hPre

/-- **T3 (drain-only is always allowed).** Specifically: a transaction
whose every JoinSplit has `vpub_old = 0` is always `validTx`-admissible,
at *any* height, both pre- and post-Canopy. This is the canonical
"transparent-to-Sprout disabled, Sprout-to-transparent OK" shape. -/
theorem T3_drain_only_always_valid
    (canopyHeight height : Nat) (tx : Tx)
    (hDrain : tx.satisfiesZip211) :
    validTx canopyHeight height tx := by
  intro _
  exact hDrain

/-- **T3′ (every JoinSplit drain-only ⇒ Sprout pool change ≤ 0).** The
arithmetic content of T3: `tx.satisfiesZip211` ⇒ `sproutBalanceChange ≤ 0`,
independent of height. -/
theorem T3_drain_only_nonpositive (tx : Tx)
    (hDrain : tx.satisfiesZip211) :
    tx.sproutBalanceChange ≤ 0 :=
  list_satisfiesZip211_sum_nonpos tx.joinSplits hDrain

/-- **T4 (zero balance trivially satisfies the rule, post-Canopy).** A
transaction with no JoinSplits has `sproutBalanceChange = 0` and trivially
satisfies the ZIP-211 byte-level rule. This handles the "vanilla transparent
transaction" case at every height. -/
theorem T4_zero_balance_satisfies
    (canopyHeight height : Nat) :
    validTx canopyHeight height ⟨[]⟩ := by
  intro _ js hMem
  exact (List.not_mem_nil hMem).elim

/-- **T4′ (zero balance is also zero arithmetically).** -/
theorem T4_empty_tx_balance : Tx.sproutBalanceChange ⟨[]⟩ = 0 := by
  unfold Tx.sproutBalanceChange
  simp

/-! ## Supporting / corollary theorems -/

/-- **T5 (per-JoinSplit: post-Canopy ⇒ change ≤ 0).** The single-JoinSplit
analogue of T1: a JoinSplit satisfying the ZIP-211 byte rule has
`sproutBalanceChange ≤ 0`. -/
theorem T5_js_post_canopy_nonpositive (js : JoinSplit)
    (hSat : js.satisfiesZip211) :
    js.sproutBalanceChange ≤ 0 := by
  unfold JoinSplit.sproutBalanceChange JoinSplit.satisfiesZip211 at *
  rw [hSat]
  simp

/-- **T6 (per-JoinSplit: post-Canopy ⇒ change = `-vpubNew`).** Tightens
T5: not just `≤ 0` but exactly `-vpub_new`. This makes the
"Sprout-only-shrinks" property quantitative — the magnitude of the shrink
equals the unshielded amount. -/
theorem T6_js_post_canopy_exact (js : JoinSplit)
    (hSat : js.satisfiesZip211) :
    js.sproutBalanceChange = - (js.vpubNew : Int) := by
  unfold JoinSplit.sproutBalanceChange JoinSplit.satisfiesZip211 at *
  rw [hSat]
  simp

/-- **T7 (the Canopy threshold is exact and inclusive: at `h = canopyHeight`
admissibility ⇔ the byte rule).** This pins the `≥` boundary of the rule. The
Rust check is `if height >= canopy_activation_height`
(`zebra-consensus/src/transaction/check.rs:234`), so at the activation height
itself the rule fires (the `≥` is inclusive, not strict). The biconditional
form rules out an off-by-one to a strict `>`: a model using `height > canopy`
would falsify the reverse direction at the boundary point. -/
theorem T7_canopy_threshold_inclusive_iff
    (canopyHeight : Nat) (tx : Tx) :
    validTx canopyHeight canopyHeight tx ↔ tx.satisfiesZip211 := by
  constructor
  · intro hValid
    exact hValid (Nat.le_refl _)
  · intro hSat _
    exact hSat

/-- **T8 (one-below-canopy: rule does NOT apply).** At
`h = canopyHeight - 1` (assuming `canopyHeight ≥ 1`), the rule does not
apply, so any transaction is valid. -/
theorem T8_one_below_canopy_vacuous
    (canopyHeight : Nat) (hPos : canopyHeight ≥ 1) (tx : Tx) :
    validTx canopyHeight (canopyHeight - 1) tx :=
  T2_pre_canopy_vacuous canopyHeight (canopyHeight - 1) tx (by omega)

/-- **T9 (monotonicity in height — once valid at one post-Canopy height, valid
at every post-Canopy height).** If the byte-level ZIP-211 rule holds for a
transaction, it implies validity at every height (not just at the one
queried). -/
theorem T9_height_invariance
    (canopyHeight h₁ h₂ : Nat) (tx : Tx)
    (hSat : tx.satisfiesZip211) :
    validTx canopyHeight h₁ tx ∧ validTx canopyHeight h₂ tx := by
  refine ⟨?_, ?_⟩ <;> · intro _; exact hSat

/-- **T10 (concrete: a JoinSplit with `vpub_old = 0, vpub_new = 5` is
admissible post-Canopy).** Sanity check that the model permits the
intended drain shape. -/
theorem T10_concrete_drain :
    validTx CANOPY_MAINNET CANOPY_MAINNET
      ⟨[{ vpubOld := 0, vpubNew := 5 }]⟩ := by
  intro _ js hMem
  rcases List.mem_singleton.mp hMem with rfl
  rfl

/-- **T11 (concrete: a JoinSplit with `vpub_old = 1, vpub_new = 0` is
NOT admissible at the Canopy activation height).** This is the ZIP-211
rejection case: adding to Sprout post-Canopy fails the byte rule. -/
theorem T11_concrete_add_rejected :
    ¬ validTx CANOPY_MAINNET CANOPY_MAINNET
        ⟨[{ vpubOld := 1, vpubNew := 0 }]⟩ := by
  intro hValid
  have hSat : Tx.satisfiesZip211 ⟨[{ vpubOld := 1, vpubNew := 0 }]⟩ :=
    hValid (Nat.le_refl _)
  have hJs : ({ vpubOld := 1, vpubNew := 0 } : JoinSplit).satisfiesZip211 :=
    hSat _ (List.mem_singleton.mpr rfl)
  unfold JoinSplit.satisfiesZip211 at hJs
  -- `vpubOld = 0` but the witness has `vpubOld = 1`.
  exact absurd hJs (by decide)

/-- **T12 (concrete: the same "add to Sprout" transaction IS admissible
*before* Canopy).** Showcases T2: at height `0` (genesis), the rule is
vacuous, so even adding to Sprout is allowed. -/
theorem T12_concrete_add_pre_canopy :
    validTx CANOPY_MAINNET 0
      ⟨[{ vpubOld := 1, vpubNew := 0 }]⟩ := by
  apply T2_pre_canopy_vacuous
  unfold CANOPY_MAINNET; decide

/-- **T13 (concrete: a JoinSplit with `vpub_old = 0, vpub_new = 0` is
admissible at every height — both pre- and post-Canopy).** The empty/trivial
JoinSplit (often present as a placeholder in early Sprout transactions). -/
theorem T13_concrete_zero_zero (h : Nat) :
    validTx CANOPY_MAINNET h
      ⟨[{ vpubOld := 0, vpubNew := 0 }]⟩ := by
  intro _ js hMem
  rcases List.mem_singleton.mp hMem with rfl
  rfl

/-- **T14 (zero JoinSplit has zero Sprout change).** Restates the
quantitative observation that a `(vpub_old = 0, vpub_new = 0)` JoinSplit
contributes nothing to the Sprout pool. -/
theorem T14_zero_js_zero_change :
    ({ vpubOld := 0, vpubNew := 0 } : JoinSplit).sproutBalanceChange = 0 := by
  unfold JoinSplit.sproutBalanceChange; simp

/-- **T15 (mainnet ≠ testnet Canopy heights).** The mainnet and testnet
Canopy activation heights differ; the model carries both, and the
`validTx` predicate is parameterised over which network we're checking. -/
theorem T15_mainnet_neq_testnet : CANOPY_MAINNET ≠ CANOPY_TESTNET := by
  unfold CANOPY_MAINNET CANOPY_TESTNET; decide

/-- **T16 (post-Canopy + per-JoinSplit characterisation).** Combines T1
and T6: at post-Canopy heights, the transaction's Sprout-pool change
equals `- (sum of vpub_new)`, i.e. the total amount unshielded. -/
theorem T16_post_canopy_change_eq_neg_unshielded
    (canopyHeight height : Nat) (tx : Tx)
    (hValid : validTx canopyHeight height tx)
    (hHeight : height ≥ canopyHeight) :
    tx.sproutBalanceChange = - ((tx.joinSplits.map (fun js => (js.vpubNew : Int))).sum) := by
  have hSat : tx.satisfiesZip211 := hValid hHeight
  exact list_satisfiesZip211_sum_eq_neg tx.joinSplits hSat

/-- **T17 (decidability of the byte rule on a single JoinSplit).** The
`satisfiesZip211` predicate on a single JoinSplit is decidable, so the
per-JoinSplit check is mechanically executable — mirroring the runtime
check in `disabled_add_to_sprout_pool`. -/
instance instJoinSplitSatisfiesZip211 (js : JoinSplit) :
    Decidable js.satisfiesZip211 := by
  unfold JoinSplit.satisfiesZip211
  exact Nat.decEq _ _

/-- **T18 (decidability of the byte rule on a transaction).** -/
instance instTxSatisfiesZip211 (tx : Tx) :
    Decidable tx.satisfiesZip211 := by
  unfold Tx.satisfiesZip211
  exact List.decidableBAll _ _

/-- **T19 (single-JoinSplit witness — strict rejection by the literal Rust loop
shape).** A transaction whose **first** JoinSplit has `vpub_old = 1` is
rejected post-Canopy. This pins down that Rust's loop fails on the first
non-zero JoinSplit, not (e.g.) on a sum threshold: the rule is a per-element
check, not a global one. -/
theorem T19_first_js_nonzero_rejected_post_canopy
    (canopyHeight height : Nat)
    (hHeight : height ≥ canopyHeight)
    (rest : List JoinSplit) :
    ¬ validTx canopyHeight height
        ⟨{ vpubOld := 1, vpubNew := 0 } :: rest⟩ := by
  intro hValid
  have hSat : Tx.satisfiesZip211
      ⟨{ vpubOld := 1, vpubNew := 0 } :: rest⟩ := hValid hHeight
  have hJs : ({ vpubOld := 1, vpubNew := 0 } : JoinSplit).satisfiesZip211 :=
    hSat _ List.mem_cons_self
  exact absurd hJs (by decide)

/-- **T20 (counterexample showing why T1 is the literal headline, not the
corollary).** The Sprout-pool sum can be ≤ 0 without satisfying the byte rule:
a transaction with `vpub_old = 3, vpub_new = 5` has `sproutBalanceChange = -2`
(≤ 0), yet violates the post-Canopy ZIP-211 rule because `vpub_old ≠ 0`. This
demonstrates that a `sproutBalanceChange ≤ 0` headline is *strictly weaker*
than the Rust check, and justifies keeping the literal per-JoinSplit rule as
the headline (T1) rather than the sum-form corollary
(`T1_corollary_sprout_pool_nonpositive`). -/
theorem T20_sum_nonpos_does_not_imply_rule :
    let tx : Tx := ⟨[{ vpubOld := 3, vpubNew := 5 }]⟩
    tx.sproutBalanceChange ≤ 0 ∧ ¬ tx.satisfiesZip211 := by
  refine ⟨?_, ?_⟩
  · unfold Tx.sproutBalanceChange JoinSplit.sproutBalanceChange
    simp
  · intro hSat
    have hJs : ({ vpubOld := 3, vpubNew := 5 } : JoinSplit).satisfiesZip211 :=
      hSat _ List.mem_cons_self
    exact absurd hJs (by decide)

/-- **T21 (Rust-loop characterisation: the byte rule is *literally* "every
`vpub_old` in `tx.output_values_to_sprout()` equals zero").** This pins the
defining equivalence used by the Rust check: the predicate iterating
`tx.output_values_to_sprout()` over JoinSplits equals our `satisfiesZip211`
predicate, with no hidden quantifiers or sum reduction. -/
theorem T21_satisfiesZip211_iff_all_vpubOld_zero (tx : Tx) :
    tx.satisfiesZip211 ↔ ∀ js ∈ tx.joinSplits, js.vpubOld = 0 := by
  unfold Tx.satisfiesZip211 JoinSplit.satisfiesZip211
  exact Iff.rfl

end Zebra.Zip211SproutClosed
