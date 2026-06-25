import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# ZIP-213: shielded coinbase outputs decryptable with the all-zero OVK

> [Heartwood onward] All Sapling and Orchard outputs in coinbase transactions
> MUST decrypt to a note plaintext, i.e. the procedure in
> § 4.20.3 'Decryption using a Full Viewing Key (Sapling and Orchard)' does not
> return ⊥, using a sequence of 32 zero bytes as the outgoing viewing key.

> [Canopy onward] Any Sapling or Orchard output of a coinbase transaction
> decrypted to a note plaintext according to the preceding rule MUST have note
> plaintext lead byte equal to 0x02.

Source: `zebra-consensus/src/transaction/check.rs:307-366`
(`coinbase_outputs_are_decryptable`), enforced from `zebra-consensus/src/block.rs:259`.

## Modelling strategy

ZIP-213 is fundamentally a *cryptographic* check: the verifier attempts to
decrypt each shielded output's ciphertext under a 32-zero OVK and checks that
the result is not `⊥`. We cannot encode elliptic-curve trial-decryption in
Lean, so we model the check *abstractly* via opaque per-output predicates:

  * `ShieldedOutput.decryptsZeroOvk`: "this output decrypts successfully under
    the all-zero OVK" — an uninterpreted Boolean that stands in for the
    cryptographic procedure in § 4.20.3.
  * `ShieldedOutput.notePlaintextLeadByte`: the lead byte of the note
    plaintext recovered by the above decryption (only meaningful when
    `decryptsZeroOvk = true`). Heartwood requires `0x01` or `0x02`; Canopy
    onward requires `0x02`.

Previously this module modelled a fictional `ovk` field equality
(`o.ovk = ZERO_OVK`), which was a hidden triviality — Output descriptions do
not carry an OVK on the wire; the OVK is the *key the sender used to encrypt*,
and the consensus check is the verifier's *decryption attempt* with the
zero OVK. The replacement abstract predicate keeps the model honest.

The Rust check structure is (in order):

  1. `!has_shielded_outputs()` ⇒ `Ok`
  2. `height < Heartwood` ⇒ `Ok`
  3. `!is_coinbase()` ⇒ `Err(NotCoinbase)`
  4. `!decrypts_successfully(...)` ⇒ `Err(CoinbaseOutputsNotDecryptable)`

We model all four branches; `is_coinbase()` is exposed as a boolean field on
our `Coinbase` structure (the Rust function name is misleading — the helper
takes a `Transaction` and checks its shape, so the "is-coinbase" flag is a
genuine runtime check, not a static type-system property).

Sapling output: `zebra-chain/src/sapling/output.rs:27`.
Orchard action (output half): `zebra-chain/src/orchard/action.rs:23`.
Sapling key bytes: `zebra-chain/src/sapling/keys.rs` (the `[u8; 32]` OVK type).
Activation heights: `zebra-chain/src/parameters/constants.rs:84-87`.

[ZIP-213]: <https://zips.z.cash/zip-0213>
-/

namespace Zebra.Zip213ShieldedCoinbase

/-! ## Constants and core types -/

/-- The byte-width of an outgoing viewing key (`ovk` in the spec; `[u8; 32]`
in `zebra-chain/src/sapling/keys.rs`). Not directly used in the consensus
predicate — the OVK lives in the cryptographic decryption procedure, which we
abstract over — but pinned here for documentation. -/
def OVK_BYTES : Nat := 32

/-- Mainnet Heartwood activation height. The ZIP-213 decryption rule turns on
at this height.
Source: `zebra-chain/src/parameters/constants.rs:84`. -/
def HEARTWOOD_HEIGHT : Nat := 903_000

/-- Mainnet Canopy activation height. The ZIP-213 lead-byte rule
(`noteLeadByte = 0x02`) turns on at this height.
Source: `zebra-chain/src/parameters/constants.rs:86`. -/
def CANOPY_HEIGHT : Nat := 1_046_400

/-- Note plaintext lead byte for ZIP-212 v1 notes (allowed pre-Canopy, denied
post-Canopy). -/
def LEAD_BYTE_V1 : Nat := 0x01

/-- Note plaintext lead byte for ZIP-212 v2 notes (always allowed when the
decryption rule applies). -/
def LEAD_BYTE_V2 : Nat := 0x02

/-- The all-zero outgoing viewing key (`[0u8; 32]`), used by ZIP-213 for
shielded coinbase outputs.
Source: `zebra-consensus/src/transaction/check.rs:319` ("using a sequence of
32 zero bytes as the outgoing viewing key"). -/
def ZERO_OVK : List Nat := List.replicate OVK_BYTES 0

/-- A shielded output description. The two booleans abstract over the
cryptographic decryption procedure — the verifier cannot reconstruct the
plaintext without performing trial-decryption, so we model the *result* of
that procedure as an oracle.

* `decryptsZeroOvk`: true iff the procedure in § 4.20.3 with the all-zero
  outgoing viewing key returns a note plaintext (rather than ⊥) for this
  output. Sapling: `zebra-chain/src/sapling/output.rs:27`. Orchard:
  `zebra-chain/src/orchard/action.rs:23`. The pool kind is irrelevant to the
  predicate — Sapling outputs and Orchard actions are constrained
  identically.
* `notePlaintextLeadByte`: the lead byte of the recovered note plaintext
  (well-defined only when `decryptsZeroOvk = true`; the value is don't-care
  otherwise). ZIP-212/ZIP-213 specify `0x01` for v1 notes and `0x02` for v2
  notes. -/
structure ShieldedOutput where
  decryptsZeroOvk : Bool
  notePlaintextLeadByte : Nat

/-- A coinbase transaction's shielded portions plus the runtime "is this
actually a coinbase?" flag. The transparent body is omitted — ZIP-213 only
peeks at the shielded outputs and the coinbase-ness flag.

* `isCoinbase`: mirrors the Rust `transaction.is_coinbase()` runtime check
  (`zebra-consensus/src/transaction/check.rs:357`). If false at Heartwood
  onward with shielded outputs, the check returns `Err(NotCoinbase)`. The
  caller in `zebra-consensus/src/block.rs:259` only invokes the check on a
  transaction it already identified as coinbase, but the helper still
  re-validates defensively.
* `saplingOutputs` / `orchardOutputs`: Sapling output descriptions and
  Orchard action output halves. `has_shielded_outputs` is true iff at least
  one of these is non-empty. -/
structure Coinbase where
  isCoinbase : Bool
  saplingOutputs : List ShieldedOutput
  orchardOutputs : List ShieldedOutput

/-- A coinbase has shielded outputs iff at least one of its pool lists is
non-empty. Models the `has_shielded_outputs` short-circuit. -/
def Coinbase.hasShielded (cb : Coinbase) : Prop :=
  cb.saplingOutputs ≠ [] ∨ cb.orchardOutputs ≠ []

/-- Decidability for `hasShielded`. -/
instance (cb : Coinbase) : Decidable cb.hasShielded :=
  inferInstanceAs (Decidable (_ ∨ _))

/-! ## The ZIP-213 consensus rule -/

/-- The lead-byte constraint at a given height: pre-Canopy, both `0x01` and
`0x02` are permitted; Canopy onward, only `0x02`.
Source: `zebra-consensus/src/transaction/check.rs:323-325` (Canopy clause). -/
def leadByteOk (height : Nat) (b : Nat) : Prop :=
  if height < CANOPY_HEIGHT then b = LEAD_BYTE_V1 ∨ b = LEAD_BYTE_V2
  else b = LEAD_BYTE_V2

/-- A shielded output passes the Heartwood-onward decryption check iff the
abstract decryption returns a plaintext *and* (Canopy-onward) the lead byte
is `0x02`. -/
def ShieldedOutput.passesDecryption (o : ShieldedOutput) (height : Nat) : Prop :=
  o.decryptsZeroOvk = true ∧ leadByteOk height o.notePlaintextLeadByte

/-- Every Sapling and Orchard output passes the decryption check. The
predicate is *pool-uniform* — same condition on both lists. -/
def Coinbase.allOutputsDecrypt (cb : Coinbase) (height : Nat) : Prop :=
  (∀ o ∈ cb.saplingOutputs, o.passesDecryption height) ∧
  (∀ o ∈ cb.orchardOutputs, o.passesDecryption height)

/-- The complete ZIP-213 consensus rule at a given height, mirroring the
four-branch structure of `coinbase_outputs_are_decryptable`
(`zebra-consensus/src/transaction/check.rs:343-365`):

  1. No shielded outputs ⇒ Ok.
  2. Pre-Heartwood ⇒ Ok.
  3. Otherwise, the transaction must in fact be a coinbase (`isCoinbase`).
  4. And every shielded output must pass the abstract decryption check at
     that height (with the lead-byte clause applied from Canopy onward).

The result type encodes the three failure modes the Rust returns:
* `ok` ↔ check returns `Ok(())`
* `notCoinbase` ↔ `Err(NotCoinbase)` (a shielded coinbase-claimed tx that
  isn't actually a coinbase)
* `outputsNotDecryptable` ↔ `Err(CoinbaseOutputsNotDecryptable)`. -/
inductive Zip213Result
  | ok
  | notCoinbase
  | outputsNotDecryptable
  deriving DecidableEq

/-- The ZIP-213 check as a `Prop`-valued classifier, matching the four-branch
early-return structure of the Rust implementation
(`zebra-consensus/src/transaction/check.rs:343-365`):

```
if !has_shielded_outputs() { return Ok; }
if height < Heartwood       { return Ok; }
if !is_coinbase()           { return Err(NotCoinbase); }
if !decrypts_successfully() { return Err(CoinbaseOutputsNotDecryptable); }
return Ok;
```

We use a `Prop`-level cascade rather than `if-then-else` because
`allOutputsDecrypt` quantifies over `List ShieldedOutput` with a `Prop`-valued
predicate, which is not propositionally `Decidable` without classical
choice. -/
def Coinbase.zip213Outcome (cb : Coinbase) (height : Nat) : Zip213Result → Prop
  | Zip213Result.ok =>
      ¬ cb.hasShielded ∨
      height < HEARTWOOD_HEIGHT ∨
      (cb.isCoinbase = true ∧ cb.allOutputsDecrypt height)
  | Zip213Result.notCoinbase =>
      cb.hasShielded ∧ HEARTWOOD_HEIGHT ≤ height ∧ cb.isCoinbase = false
  | Zip213Result.outputsNotDecryptable =>
      cb.hasShielded ∧ HEARTWOOD_HEIGHT ≤ height ∧ cb.isCoinbase = true ∧
      ¬ cb.allOutputsDecrypt height

/-- The ZIP-213 consensus rule, written as a `Prop`: "the check returns
`Ok`". Equivalent to the disjunction of the four early-Ok branches in the
Rust. -/
def Coinbase.zip213Compliant (cb : Coinbase) (height : Nat) : Prop :=
  ¬ cb.hasShielded ∨
  height < HEARTWOOD_HEIGHT ∨
  (cb.isCoinbase = true ∧ cb.allOutputsDecrypt height)

/-! ## Theorems -/

/-- **T1 (all-zero OVK is the spec-mandated 32-byte sequence).** `ZERO_OVK`
has length exactly `OVK_BYTES = 32`. Concrete witness of the spec phrase "a
sequence of 32 zero bytes". -/
theorem zero_ovk_length : ZERO_OVK.length = OVK_BYTES := by
  unfold ZERO_OVK
  exact List.length_replicate

/-- **T2 (pre-Heartwood vacuity).** For any coinbase, ZIP-213 compliance at a
sub-Heartwood height holds unconditionally. Mirrors the
`height < Heartwood => Ok` short-circuit at
`zebra-consensus/src/transaction/check.rs:348-354`. -/
theorem pre_heartwood_vacuous (cb : Coinbase) (h : Nat)
    (hh : h < HEARTWOOD_HEIGHT) : cb.zip213Compliant h := by
  unfold Coinbase.zip213Compliant
  exact Or.inr (Or.inl hh)

/-- **T3 (no shielded outputs ⇒ trivially compliant).** A coinbase with no
shielded outputs at all satisfies ZIP-213 at every height. Mirrors the
`!has_shielded_outputs() => Ok` short-circuit at
`zebra-consensus/src/transaction/check.rs:343`. -/
theorem unshielded_compliant (isCb : Bool) (h : Nat) :
    Coinbase.zip213Compliant
      { isCoinbase := isCb, saplingOutputs := [], orchardOutputs := [] } h := by
  refine Or.inl ?_
  intro hc
  rcases hc with h1 | h2 <;> simp_all [Coinbase.hasShielded]

/-- **T4 (pool uniformity of the all-decrypt predicate).** Swapping the
Sapling and Orchard output lists preserves the all-decrypt check — the rule
treats both pools identically. This is the formal counterpart to "no
per-pool exemption". -/
theorem allOutputsDecrypt_pool_uniform
    (isCb : Bool) (sap orc : List ShieldedOutput) (h : Nat) :
    Coinbase.allOutputsDecrypt
      { isCoinbase := isCb, saplingOutputs := sap, orchardOutputs := orc } h ↔
    Coinbase.allOutputsDecrypt
      { isCoinbase := isCb, saplingOutputs := orc, orchardOutputs := sap } h := by
  unfold Coinbase.allOutputsDecrypt
  exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩

/-- **T5 (non-coinbase shielded tx fails at Heartwood onward).** If a tx
claims `isCoinbase = false` but has shielded outputs and the height is at or
past Heartwood, the check is *not* `Ok` — it fails with `NotCoinbase`.
Mirrors the `!is_coinbase() => Err(NotCoinbase)` branch
(`zebra-consensus/src/transaction/check.rs:357-359`).

This is the third branch of the Rust early-return ladder, previously absent
from the model. -/
theorem non_coinbase_with_shielded_fails
    (sap orc : List ShieldedOutput) (h : Nat)
    (hh : HEARTWOOD_HEIGHT ≤ h)
    (hshielded : sap ≠ [] ∨ orc ≠ []) :
    ¬ Coinbase.zip213Compliant
        { isCoinbase := false, saplingOutputs := sap, orchardOutputs := orc } h := by
  intro hcomp
  rcases hcomp with hns | hpre | ⟨hcb, _⟩
  · exact hns hshielded
  · exact (Nat.not_lt.mpr hh) hpre
  · exact Bool.noConfusion hcb

/-- **T6 (Heartwood is the activation threshold).** At exactly
`HEARTWOOD_HEIGHT`, the pre-Heartwood vacuity branch no longer applies. If
the coinbase has shielded outputs and `isCoinbase = true`, compliance
reduces to `allOutputsDecrypt`. -/
theorem at_heartwood_requires_decryption
    (sap orc : List ShieldedOutput)
    (hshielded : sap ≠ [] ∨ orc ≠ []) :
    Coinbase.zip213Compliant
        { isCoinbase := true, saplingOutputs := sap, orchardOutputs := orc }
        HEARTWOOD_HEIGHT ↔
    Coinbase.allOutputsDecrypt
        { isCoinbase := true, saplingOutputs := sap, orchardOutputs := orc }
        HEARTWOOD_HEIGHT := by
  constructor
  · intro hc
    rcases hc with hns | hpre | ⟨_, hok⟩
    · exact absurd hshielded hns
    · exact absurd hpre (Nat.lt_irrefl _)
    · exact hok
  · intro hok
    refine Or.inr (Or.inr ⟨?_, hok⟩)
    rfl

/-- **T7 (concrete compliant witness, post-Canopy).** A coinbase with two
Sapling and one Orchard output, all marked as decrypting under the zero OVK
and with the v2 lead byte (`0x02`), is ZIP-213-compliant at any
Canopy-onward height. Witnesses that the predicate is satisfiable (not just
vacuous) and that the v2 lead byte is universally accepted. -/
theorem concrete_compliant_post_canopy (h : Nat) (hh : CANOPY_HEIGHT ≤ h) :
    Coinbase.zip213Compliant
      { isCoinbase := true,
        saplingOutputs :=
          [ { decryptsZeroOvk := true, notePlaintextLeadByte := LEAD_BYTE_V2 }
          , { decryptsZeroOvk := true, notePlaintextLeadByte := LEAD_BYTE_V2 } ],
        orchardOutputs :=
          [ { decryptsZeroOvk := true, notePlaintextLeadByte := LEAD_BYTE_V2 } ] }
      h := by
  have hnotlt : ¬ h < CANOPY_HEIGHT := Nat.not_lt.mpr hh
  have hpass : ShieldedOutput.passesDecryption
      { decryptsZeroOvk := true, notePlaintextLeadByte := LEAD_BYTE_V2 } h := by
    refine ⟨rfl, ?_⟩
    unfold leadByteOk
    simp [hnotlt]
  refine Or.inr (Or.inr ⟨rfl, ?_, ?_⟩)
  · intro o ho
    rw [List.mem_cons, List.mem_cons, List.mem_nil_iff] at ho
    rcases ho with rfl | rfl | hbad
    · exact hpass
    · exact hpass
    · exact absurd hbad (fun h => h.elim)
  · intro o ho
    rw [List.mem_cons, List.mem_nil_iff] at ho
    rcases ho with rfl | hbad
    · exact hpass
    · exact absurd hbad (fun h => h.elim)

/-- **T8 (post-Canopy `0x01` lead byte is rejected).** Even when an output
decrypts successfully under the zero OVK, a v1 (`0x01`) lead byte is
rejected at Canopy-onward heights. Mirrors the Canopy clause
("decrypted...MUST have note plaintext lead byte equal to 0x02"). -/
theorem post_canopy_rejects_lead_v1 (h : Nat) (hh : CANOPY_HEIGHT ≤ h) :
    ¬ Coinbase.zip213Compliant
        { isCoinbase := true,
          saplingOutputs :=
            [ { decryptsZeroOvk := true, notePlaintextLeadByte := LEAD_BYTE_V1 } ],
          orchardOutputs := [] }
        h := by
  intro hcomp
  -- Cannot be the "no shielded" branch
  rcases hcomp with hns | hpre | ⟨_, hsap, _⟩
  · exact hns (Or.inl (by simp))
  · -- height ≥ Canopy ≥ Heartwood, so cannot be pre-Heartwood
    have : HEARTWOOD_HEIGHT < CANOPY_HEIGHT := by
      unfold HEARTWOOD_HEIGHT CANOPY_HEIGHT; decide
    exact (Nat.not_lt.mpr (Nat.le_trans (Nat.le_of_lt this) hh)) hpre
  · -- post-Canopy: the head output's lead byte must satisfy `leadByteOk`
    have hmem :
        ({ decryptsZeroOvk := true, notePlaintextLeadByte := LEAD_BYTE_V1 } :
          ShieldedOutput) ∈
        [ ({ decryptsZeroOvk := true, notePlaintextLeadByte := LEAD_BYTE_V1 } :
            ShieldedOutput) ] := by simp
    have hpass := hsap _ hmem
    obtain ⟨_, hlead⟩ := hpass
    unfold leadByteOk at hlead
    have hnotlt : ¬ h < CANOPY_HEIGHT := Nat.not_lt.mpr hh
    simp [hnotlt, LEAD_BYTE_V1, LEAD_BYTE_V2] at hlead

/-- **T9 (pre-Canopy `0x01` lead byte is accepted on Heartwood-onward
heights).** Between Heartwood and Canopy, both lead-byte values are
permitted. Witnesses that the Canopy clause is a genuine *narrowing*. -/
theorem pre_canopy_accepts_lead_v1
    (h : Nat) (hh1 : HEARTWOOD_HEIGHT ≤ h) (hh2 : h < CANOPY_HEIGHT) :
    Coinbase.zip213Compliant
      { isCoinbase := true,
        saplingOutputs :=
          [ { decryptsZeroOvk := true, notePlaintextLeadByte := LEAD_BYTE_V1 } ],
        orchardOutputs := [] }
      h := by
  refine Or.inr (Or.inr ⟨rfl, ?_, ?_⟩)
  · intro o ho
    rw [List.mem_cons, List.mem_nil_iff] at ho
    rcases ho with rfl | hbad
    · refine ⟨rfl, ?_⟩
      unfold leadByteOk
      simp [hh2, LEAD_BYTE_V1]
    · exact absurd hbad (fun h => h.elim)
  · intro o ho; cases ho

/-- **T10 (decryption failure forces non-compliance post-Heartwood).** If a
coinbase has a Sapling output with `decryptsZeroOvk = false`, the check
fails at any Heartwood-onward height — regardless of `isCoinbase`. This is
the contrapositive of the core ZIP-213 rule. -/
theorem decryption_failure_fails_post_heartwood
    (rest : List ShieldedOutput) (orc : List ShieldedOutput)
    (leadByte : Nat) (h : Nat)
    (hh : HEARTWOOD_HEIGHT ≤ h) :
    ¬ Coinbase.zip213Compliant
        { isCoinbase := true,
          saplingOutputs :=
            { decryptsZeroOvk := false, notePlaintextLeadByte := leadByte } :: rest,
          orchardOutputs := orc }
        h := by
  intro hcomp
  rcases hcomp with hns | hpre | ⟨_, hsap, _⟩
  · -- has shielded outputs by construction
    exact hns (Or.inl (by simp))
  · exact (Nat.not_lt.mpr hh) hpre
  · have hmem :
        ({ decryptsZeroOvk := false, notePlaintextLeadByte := leadByte } :
          ShieldedOutput) ∈
        ({ decryptsZeroOvk := false, notePlaintextLeadByte := leadByte } :
          ShieldedOutput) :: rest := by simp
    have hpass := hsap _ hmem
    obtain ⟨hdec, _⟩ := hpass
    exact Bool.noConfusion hdec

/-- **T11 (post-Heartwood structural monotonicity).** If a coinbase is
ZIP-213-compliant at some Heartwood-onward height `h₁`, *and* the height
window `[h₁, h₂]` doesn't cross the Canopy boundary, then it is compliant at
`h₂` too. The Canopy-crossing case is *not* monotone — a `0x01` lead byte
that was acceptable at `h₁ < CANOPY_HEIGHT` becomes unacceptable at
`h₂ ≥ CANOPY_HEIGHT`, exhibited by T8 + T9. -/
theorem zip213_monotone_no_canopy_crossing (cb : Coinbase) (h₁ h₂ : Nat)
    (hh : HEARTWOOD_HEIGHT ≤ h₁) (_hle : h₁ ≤ h₂)
    (hnocross : h₁ < CANOPY_HEIGHT → h₂ < CANOPY_HEIGHT)
    (hc : cb.zip213Compliant h₁) : cb.zip213Compliant h₂ := by
  rcases hc with hns | hpre | ⟨hcb, hsap, horc⟩
  · exact Or.inl hns
  · exact absurd hpre (Nat.not_lt.mpr hh)
  · refine Or.inr (Or.inr ⟨hcb, ?_, ?_⟩)
    · intro o ho
      obtain ⟨hdec, hlead⟩ := hsap o ho
      refine ⟨hdec, ?_⟩
      by_cases hb1 : h₁ < CANOPY_HEIGHT
      · -- h₁ pre-Canopy ⇒ h₂ pre-Canopy by `hnocross`
        have hb2 := hnocross hb1
        unfold leadByteOk at *
        simp [hb1] at hlead
        simp [hb2]; exact hlead
      · -- h₁ post-Canopy ⇒ h₂ post-Canopy by `_hle`
        have hb2 : ¬ h₂ < CANOPY_HEIGHT :=
          fun h => hb1 (Nat.lt_of_le_of_lt _hle h)
        unfold leadByteOk at *
        simp [hb1] at hlead
        simp [hb2]; exact hlead
    · intro o ho
      obtain ⟨hdec, hlead⟩ := horc o ho
      refine ⟨hdec, ?_⟩
      by_cases hb1 : h₁ < CANOPY_HEIGHT
      · have hb2 := hnocross hb1
        unfold leadByteOk at *
        simp [hb1] at hlead
        simp [hb2]; exact hlead
      · have hb2 : ¬ h₂ < CANOPY_HEIGHT :=
          fun h => hb1 (Nat.lt_of_le_of_lt _hle h)
        unfold leadByteOk at *
        simp [hb1] at hlead
        simp [hb2]; exact hlead

/-- **T12 (Heartwood-onward, `isCoinbase = true`, all-decrypt-v2 is
sufficient).** Compliance at any Heartwood-onward height is implied by:
`isCoinbase = true` and every shielded output decrypts under the zero OVK
with lead byte `0x02`. The v2 lead byte is uniformly accepted across the
post-Heartwood window. -/
theorem all_v2_implies_compliance (cb : Coinbase) (h : Nat)
    (hcb : cb.isCoinbase = true)
    (hsap : ∀ o ∈ cb.saplingOutputs,
              o.decryptsZeroOvk = true ∧ o.notePlaintextLeadByte = LEAD_BYTE_V2)
    (horc : ∀ o ∈ cb.orchardOutputs,
              o.decryptsZeroOvk = true ∧ o.notePlaintextLeadByte = LEAD_BYTE_V2) :
    cb.zip213Compliant h := by
  refine Or.inr (Or.inr ⟨hcb, ?_, ?_⟩)
  · intro o ho
    obtain ⟨hdec, hlead⟩ := hsap o ho
    refine ⟨hdec, ?_⟩
    unfold leadByteOk
    by_cases hc : h < CANOPY_HEIGHT
    · simp [hc, hlead, LEAD_BYTE_V2]
    · simp [hc, hlead, LEAD_BYTE_V2]
  · intro o ho
    obtain ⟨hdec, hlead⟩ := horc o ho
    refine ⟨hdec, ?_⟩
    unfold leadByteOk
    by_cases hc : h < CANOPY_HEIGHT
    · simp [hc, hlead, LEAD_BYTE_V2]
    · simp [hc, hlead, LEAD_BYTE_V2]

/-- **T13 (activation height ordering).**
`HEARTWOOD_HEIGHT < CANOPY_HEIGHT`. Required for several theorems to be
non-vacuous (e.g. T9's `[HEARTWOOD_HEIGHT, CANOPY_HEIGHT)` band is
non-empty). Pinned against `zebra-chain/src/parameters/constants.rs:84-87`
(`HEARTWOOD = 903_000`, `CANOPY = 1_046_400`). -/
theorem heartwood_lt_canopy : HEARTWOOD_HEIGHT < CANOPY_HEIGHT := by
  unfold HEARTWOOD_HEIGHT CANOPY_HEIGHT; decide

end Zebra.Zip213ShieldedCoinbase
