import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# ZIP-213: shielded coinbase outputs decryptable with the all-zero OVK

> [Heartwood onward] All Sapling and Orchard outputs in coinbase transactions
> MUST decrypt to a note plaintext, i.e. the procedure in
> § 4.20.3 'Decryption using a Full Viewing Key (Sapling and Orchard)' does not
> return ⊥, using a sequence of 32 zero bytes as the outgoing viewing key.

Source: `zebra-consensus/src/transaction/check.rs:307-366`
(`coinbase_outputs_are_decryptable`), enforced from `zebra-consensus/src/block.rs:259`.

The Zcash protocol enforces ZIP-213 by checking that every Sapling output
description and every Orchard action's output half in a coinbase transaction
decrypts successfully under the all-zero outgoing viewing key (OVK). The
operational consequence — used by miners and verifiers alike — is that the
sender of a shielded coinbase output must encrypt the `out_ciphertext` to the
all-zero OVK, so any party recomputing the wrapped note key with that OVK can
recover the note plaintext.

The Rust source defines the Sapling `Output` description
(`zebra-chain/src/sapling/output.rs:27`) and the Orchard `Action`
(`zebra-chain/src/orchard/action.rs:23`) with separate `out_ciphertext`
fields; the *encryption-side* key used to produce that field is the OVK, which
the protocol requires to be 32 zero bytes for coinbase outputs.

We do not model elliptic-curve encryption itself. We model:

  * `OVK`: a 32-byte `List Nat`.
  * `ZERO_OVK`: the all-zero OVK (`List.replicate 32 0`), the only one allowed
    by ZIP-213 on coinbase shielded outputs.
  * `ShieldedOutput`: an output description carrying its OVK (Sapling and
    Orchard share the same predicate at this granularity — the rule is
    pool-uniform).
  * `Coinbase`: a structure with a list of Sapling outputs and a list of
    Orchard outputs.
  * `Zip213Compliant`: the consensus predicate "every shielded output's OVK
    is the all-zero OVK".

We then prove:

  1. The all-zero OVK has length 32 (it is a concrete witness of the OVK
     invariant).
  2. The rule is *uniform* across both pools — Sapling and Orchard use the
     same OVK requirement, with no per-pool exemption.
  3. Pre-Heartwood, the rule is *vacuous* — any coinbase satisfies ZIP-213
     trivially when the height is below Heartwood activation.
  4. A coinbase with no shielded outputs always satisfies ZIP-213.
  5. A coinbase with the all-zero OVK on every shielded output satisfies
     ZIP-213 at any height (concrete witness of a compliant coinbase).
  6. The predicate is monotone with respect to coinbase extension (adding an
     all-zero-OVK output to a compliant coinbase preserves compliance).
  7. A coinbase with any non-zero OVK on a shielded output fails the rule at
     Heartwood-onward heights.

These are the load-bearing arithmetic/structural facts under the consensus
check — the cryptographic decryption itself is not modelled here.

[ZIP-213]: <https://zips.z.cash/zip-0213>
-/

namespace Zebra.Zip213ShieldedCoinbase

/-! ## Constants and core types -/

/-- The byte-width of an outgoing viewing key (`ovk` in the spec; `[u8; 32]`
in `zebra-chain/src/sapling/keys.rs:6` and the Orchard equivalent). -/
def OVK_BYTES : Nat := 32

/-- Mainnet Heartwood activation height. ZIP-213 turns on at this height.
Source: `zebra-chain/src/parameters/constants.rs:84`. -/
def HEARTWOOD_HEIGHT : Nat := 903_000

/-- An OVK is a 32-byte list. The length invariant tracks the Rust `[u8; 32]`
type at our model granularity. -/
def IsOvk (bs : List Nat) : Prop := bs.length = OVK_BYTES

/-- The all-zero outgoing viewing key (`[0u8; 32]`), used by ZIP-213 for
shielded coinbase outputs.
Source: `zebra-consensus/src/transaction/check.rs:319` ("using a sequence of
32 zero bytes as the outgoing viewing key"). -/
def ZERO_OVK : List Nat := List.replicate OVK_BYTES 0

/-- A shielded output description, modelled as the output's OVK. Sapling
`Output` (`zebra-chain/src/sapling/output.rs:27`) and Orchard `Action`'s
output half (`zebra-chain/src/orchard/action.rs:23`) both carry an
`out_ciphertext` produced from this OVK, and ZIP-213 constrains only the
encryption-side OVK at this layer. -/
structure ShieldedOutput where
  ovk : List Nat

/-- A coinbase transaction's shielded portions: a (possibly empty) list of
Sapling outputs and a (possibly empty) list of Orchard outputs.

The transparent portion is irrelevant to ZIP-213, so we omit it from the
model — `coinbase_outputs_are_decryptable` short-circuits to `Ok` when
`!has_shielded_outputs()` (`zebra-consensus/src/transaction/check.rs:343`). -/
structure Coinbase where
  saplingOutputs : List ShieldedOutput
  orchardOutputs : List ShieldedOutput

/-- A coinbase has shielded outputs iff at least one of its pool lists is
non-empty. Models `has_shielded_outputs`. -/
def Coinbase.hasShielded (cb : Coinbase) : Prop :=
  cb.saplingOutputs ≠ [] ∨ cb.orchardOutputs ≠ []

/-- Decidability for `hasShielded`. -/
instance (cb : Coinbase) : Decidable cb.hasShielded :=
  inferInstanceAs (Decidable (_ ∨ _))

/-! ## The ZIP-213 consensus rule -/

/-- A shielded output has the ZIP-213-required OVK iff its OVK equals
`ZERO_OVK`. -/
def ShieldedOutput.isZip213Ok (o : ShieldedOutput) : Prop :=
  o.ovk = ZERO_OVK

/-- The pool-uniform encryption-side rule, written as a predicate over the
whole shielded portion: every Sapling output and every Orchard output has the
all-zero OVK. -/
def Coinbase.allOutputsZeroOvk (cb : Coinbase) : Prop :=
  (∀ o ∈ cb.saplingOutputs, o.isZip213Ok) ∧
  (∀ o ∈ cb.orchardOutputs, o.isZip213Ok)

/-- The complete ZIP-213 consensus rule at a given height: pre-Heartwood the
rule is vacuous; from Heartwood onward the rule applies. Mirrors the early
returns in `coinbase_outputs_are_decryptable`
(`zebra-consensus/src/transaction/check.rs:343-354`). -/
def Coinbase.zip213Compliant (cb : Coinbase) (height : Nat) : Prop :=
  height < HEARTWOOD_HEIGHT ∨ cb.allOutputsZeroOvk

/-! ## Theorems -/

/-- **T1 (all-zero OVK is a valid OVK).** `ZERO_OVK` has length exactly
`OVK_BYTES = 32`. This is the concrete-witness lemma: the spec calls for "a
sequence of 32 zero bytes", and our model satisfies that length invariant. -/
theorem zero_ovk_isOvk : IsOvk ZERO_OVK := by
  unfold IsOvk ZERO_OVK OVK_BYTES
  exact List.length_replicate

/-- **T2 (all-zero OVK length is 32 concretely).** A purely decidable
restatement of T1 against the concrete byte width. -/
theorem zero_ovk_length : ZERO_OVK.length = 32 := by
  unfold ZERO_OVK OVK_BYTES
  decide

/-- **T3 (pool uniformity).** `allOutputsZeroOvk` enforces the same predicate
on Sapling outputs and on Orchard outputs — i.e., if you swap the two pool
lists, compliance is preserved. This is the formal counterpart to "no per-pool
exemption": Sapling and Orchard outputs are constrained identically by
ZIP-213. -/
theorem allOutputsZeroOvk_pool_uniform (sap orc : List ShieldedOutput) :
    Coinbase.allOutputsZeroOvk { saplingOutputs := sap, orchardOutputs := orc } ↔
    Coinbase.allOutputsZeroOvk { saplingOutputs := orc, orchardOutputs := sap } := by
  unfold Coinbase.allOutputsZeroOvk
  exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩

/-- **T4 (pre-Heartwood vacuity).** For any coinbase, ZIP-213 compliance at a
sub-Heartwood height holds unconditionally. Mirrors the
`height < Heartwood => Ok` short-circuit in
`coinbase_outputs_are_decryptable` (`zebra-consensus/src/transaction/check.rs:348-354`). -/
theorem pre_heartwood_vacuous (cb : Coinbase) (h : Nat)
    (hh : h < HEARTWOOD_HEIGHT) : cb.zip213Compliant h := by
  unfold Coinbase.zip213Compliant
  exact Or.inl hh

/-- **T5 (no shielded outputs => trivially compliant).** A coinbase with no
shielded outputs at all satisfies `allOutputsZeroOvk` for vacuous-quantifier
reasons. Mirrors the `!has_shielded_outputs() => Ok` short-circuit at
`zebra-consensus/src/transaction/check.rs:343`. -/
theorem unshielded_compliant (h : Nat) :
    Coinbase.zip213Compliant
      { saplingOutputs := [], orchardOutputs := [] } h := by
  unfold Coinbase.zip213Compliant Coinbase.allOutputsZeroOvk
  refine Or.inr ⟨?_, ?_⟩
  · intro o ho; cases ho
  · intro o ho; cases ho

/-- **T6 (concrete compliant witness).** A coinbase with shielded outputs all
using `ZERO_OVK` is ZIP-213-compliant at every height, post-Heartwood
included. This witnesses that the consensus rule is satisfiable (not just
vacuous). -/
theorem concrete_compliant_coinbase (h : Nat) :
    Coinbase.zip213Compliant
      { saplingOutputs := [{ ovk := ZERO_OVK }, { ovk := ZERO_OVK }],
        orchardOutputs := [{ ovk := ZERO_OVK }] } h := by
  unfold Coinbase.zip213Compliant Coinbase.allOutputsZeroOvk
    ShieldedOutput.isZip213Ok
  refine Or.inr ⟨?_, ?_⟩
  · intro o ho
    rw [List.mem_cons, List.mem_cons, List.mem_nil_iff] at ho
    rcases ho with heq | heq | heq
    · subst heq; rfl
    · subst heq; rfl
    · exact absurd heq (fun h => h.elim)
  · intro o ho
    rw [List.mem_cons, List.mem_nil_iff] at ho
    rcases ho with heq | heq
    · subst heq; rfl
    · exact absurd heq (fun h => h.elim)

/-- **T7 (compliance is preserved under output extension with `ZERO_OVK`).**
Adding an all-zero-OVK output to either pool of an already-compliant coinbase
keeps it compliant. The result is height-independent — the structural
witness alone suffices, so no `height` parameter is required. -/
theorem compliant_cons_zero (cb : Coinbase) (hcb : cb.allOutputsZeroOvk) :
    Coinbase.allOutputsZeroOvk
      { saplingOutputs := { ovk := ZERO_OVK } :: cb.saplingOutputs,
        orchardOutputs := cb.orchardOutputs } ∧
    Coinbase.allOutputsZeroOvk
      { saplingOutputs := cb.saplingOutputs,
        orchardOutputs := { ovk := ZERO_OVK } :: cb.orchardOutputs } := by
  unfold Coinbase.allOutputsZeroOvk ShieldedOutput.isZip213Ok at *
  obtain ⟨hs, ho⟩ := hcb
  refine ⟨⟨?_, ho⟩, ⟨hs, ?_⟩⟩
  · intro o hmem
    rw [List.mem_cons] at hmem
    rcases hmem with heq | hmem
    · subst heq; rfl
    · exact hs o hmem
  · intro o hmem
    rw [List.mem_cons] at hmem
    rcases hmem with heq | hmem
    · subst heq; rfl
    · exact ho o hmem

/-- **T8 (non-zero OVK forces non-compliance post-Heartwood).** If a coinbase
has a Sapling output whose OVK is *not* the all-zero OVK, then it fails
ZIP-213 at any Heartwood-onward height. This is the contrapositive of the
rule. -/
theorem non_zero_ovk_fails_post_heartwood
    (badOvk : List Nat) (rest : List ShieldedOutput)
    (orc : List ShieldedOutput) (h : Nat)
    (hh : HEARTWOOD_HEIGHT ≤ h) (hne : badOvk ≠ ZERO_OVK) :
    ¬ Coinbase.zip213Compliant
        { saplingOutputs := { ovk := badOvk } :: rest,
          orchardOutputs := orc } h := by
  unfold Coinbase.zip213Compliant Coinbase.allOutputsZeroOvk
    ShieldedOutput.isZip213Ok
  intro hcomp
  rcases hcomp with hpre | ⟨hs, _⟩
  · -- pre-Heartwood branch contradicts `hh`
    exact (Nat.not_lt.mpr hh) hpre
  · -- post-Heartwood branch: the head Sapling output must have ZERO_OVK,
    -- contradicting `hne`
    have hmem : ({ ovk := badOvk } : ShieldedOutput) ∈
        ({ ovk := badOvk } : ShieldedOutput) :: rest := by
      simp
    have : ({ ovk := badOvk } : ShieldedOutput).ovk = ZERO_OVK :=
      hs { ovk := badOvk } hmem
    exact hne this

/-- **T9 (Heartwood is the activation threshold).** At exactly
`HEARTWOOD_HEIGHT`, the pre-Heartwood vacuity branch no longer applies —
compliance reduces to `allOutputsZeroOvk`. -/
theorem at_heartwood_requires_zero_ovk (cb : Coinbase) :
    cb.zip213Compliant HEARTWOOD_HEIGHT ↔ cb.allOutputsZeroOvk := by
  unfold Coinbase.zip213Compliant
  constructor
  · intro hc
    rcases hc with hpre | hok
    · exact absurd hpre (Nat.lt_irrefl _)
    · exact hok
  · exact Or.inr

/-- **T10 (post-Heartwood monotonicity in compliance).** If a coinbase is
ZIP-213-compliant at some Heartwood-onward height `h₁`, it is compliant at any
`h₂ ≥ h₁` (the post-Heartwood requirement is height-independent: once the
rule is in force, it stays in force, and the coinbase's structural witness
does not depend on height). -/
theorem zip213_monotone_post_heartwood (cb : Coinbase) (h₁ h₂ : Nat)
    (hh : HEARTWOOD_HEIGHT ≤ h₁) (_hle : h₁ ≤ h₂)
    (hc : cb.zip213Compliant h₁) : cb.zip213Compliant h₂ := by
  unfold Coinbase.zip213Compliant at *
  rcases hc with hpre | hok
  · -- impossible: `hpre : h₁ < HEARTWOOD_HEIGHT` vs `hh : HEARTWOOD_HEIGHT ≤ h₁`
    exact absurd hpre (Nat.not_lt.mpr hh)
  · exact Or.inr hok

end Zebra.Zip213ShieldedCoinbase
