import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Group.Basic

/-!
# Abstract algebraic properties of the Sapling Pedersen value commitment

Models the algebraic *interface* used by the Zcash Sapling value commitment
from `zebra-chain/src/sapling/commitment.rs`. Concretely, the Rust wrapper
`ValueCommitment(sapling_crypto::value::ValueCommitment)` holds a Jubjub
point of the form

```text
    cv = [v] · cv_g + [r] · cv_h
```

where `cv_g`, `cv_h` are two fixed Jubjub generators, `v : Int` is the note
value (signed: positive on outputs, negative on inputs of the value-balance
sum) and `r : Int` is the commitment-randomness `rcv`.

We don't model the Jubjub elliptic curve — that lives in
`sapling-crypto` — but we *do* model the algebraic facts a verifier relies on:

  * commitment of zero with zero randomness is the group identity
    (so the balance check `Σ cv_in − Σ cv_out = [v_balance] · cv_g` is a
    pure homomorphism statement);
  * commitment is *additively homomorphic* in `(v, r)`, which is the property
    Sapling exploits to fold every input/output commitment into a single
    Pedersen balance commitment;
  * subtraction in the (v, r) component subtracts in the group, so
    `cv(v, r) − cv(v, r) = 0` and more generally
    `cv(v₁, r₁) − cv(v₂, r₂) = cv(v₁ − v₂, r₁ − r₂)`;
  * commitment is *binding* in the value component: if two openings
    `(v₁, r)` and `(v₂, r)` of the same commitment share their randomness,
    then `v₁ = v₂`, provided the base point `g` is non-torsion (the discrete-log
    style hypothesis is bundled into a hypothesis on the family).

The DL hypothesis is taken as an *abstract* property: rather than postulating
"discrete log is hard" (which is a complexity statement, not an algebraic
fact), we state the matching algebraic consequence — `[v₁ − v₂] · g = 0`
implies `v₁ = v₂` — as an explicit hypothesis. This matches what a real
proof of binding extracts from a successful DL adversary: a non-trivial
integer that kills the base point.
-/

namespace Zebra.PedersenAbstract

variable {G : Type*} [AddCommGroup G]

/-! ## The abstract commitment family -/

/-- `commit g h v r := v • g + r • h`, the abstract Pedersen commitment to
value `v` with randomness `r` using bases `g` and `h`.

Source: `zebra-chain/src/sapling/commitment.rs:23-25` —
`sapling_crypto::value::ValueCommitment` is the Jubjub instantiation of this
two-base Pedersen commitment, with `g = cv_g`, `h = cv_h`, `v` the note value
(signed), and `r` the per-note randomness `rcv`. -/
def commit (g h : G) (v r : Int) : G := v • g + r • h

/-! ## Theorems

The proofs only use additive-commutative-group axioms plus the `zsmul`
distributive lemmas; nothing curve-specific. They therefore lift directly to
*every* `AddCommGroup` instantiation, in particular Jubjub. -/

/-- **T1 (commitment of `(0, 0)` is the identity).** Pinning the empty
opening to the group identity is what lets the Sapling value-balance check
collapse to a single homomorphism equation. -/
theorem commit_zero_zero (g h : G) : commit g h 0 0 = 0 := by
  unfold commit
  simp

/-- **T2 (additive homomorphism in the joint opening).** Adding commitments
adds their openings componentwise: `c(v₁, r₁) + c(v₂, r₂) = c(v₁ + v₂, r₁ + r₂)`.
This is the property the Sapling balance check relies on to fold a transaction's
input/output commitments into a single Pedersen commitment to the value
balance.

Source: `zebra-chain/src/sapling/commitment.rs:23-25` plus
ZIP-216 / Sapling protocol spec §5.4.8.3 (Homomorphic Pedersen commitments). -/
theorem commit_add (g h : G) (v₁ v₂ r₁ r₂ : Int) :
    commit g h v₁ r₁ + commit g h v₂ r₂ = commit g h (v₁ + v₂) (r₁ + r₂) := by
  unfold commit
  rw [add_zsmul, add_zsmul]
  abel

/-- **T3 (self-subtraction is the identity).** Subtracting any commitment
from itself gives the group identity — the degenerate case of T4. Useful
as a sanity check that the Sapling balance check treats `cv − cv` as a
non-witness on its own. -/
theorem commit_sub_self (g h : G) (v r : Int) :
    commit g h v r - commit g h v r = 0 := by
  simp

/-- **T4 (additive homomorphism on subtraction).** Subtracting commitments
subtracts their openings componentwise:
`c(v₁, r₁) − c(v₂, r₂) = c(v₁ − v₂, r₁ − r₂)`. This is the "signed" form of
T2, and is the version actually used in the Sapling balance equation, where
input commitments contribute negatively. -/
theorem commit_sub (g h : G) (v₁ v₂ r₁ r₂ : Int) :
    commit g h v₁ r₁ - commit g h v₂ r₂ = commit g h (v₁ - v₂) (r₁ - r₂) := by
  unfold commit
  rw [sub_zsmul, sub_zsmul]
  abel

/-- **T5 (negation flips the opening).** `−c(v, r) = c(−v, −r)`. A direct
consequence of T4 with `(v₁, r₁) = (0, 0)`. -/
theorem commit_neg (g h : G) (v r : Int) :
    -commit g h v r = commit g h (-v) (-r) := by
  unfold commit
  rw [neg_zsmul, neg_zsmul]
  abel

/-- **T6 (additive homomorphism on `n`-fold sums).** `n · c(v, r) = c(n · v, n · r)`
for any integer multiplier `n`. The repeated-self-application form of T2, which
the spec uses to argue that Pedersen commitments scale linearly with the
opening. -/
theorem commit_zsmul (g h : G) (n v r : Int) :
    n • commit g h v r = commit g h (n * v) (n * r) := by
  unfold commit
  rw [zsmul_add, ← mul_zsmul, ← mul_zsmul]

/-! ## Binding under an abstract DL-style hypothesis -/

/-- The "abstract discrete-log" hypothesis on a base point `g : G`. We don't
encode the *complexity* statement "DL is hard" — that's not an algebraic
fact — but its algebraic consequence: the only integer that kills `g` is
zero. Equivalently, `g` has infinite order in `G`.

This is exactly what an honest verifier extracts from a successful DL
adversary: a non-trivial integer `n ≠ 0` with `[n] · g = 0`. The contrapositive
of `IsTorsionFree`. -/
def IsNonTrivial (g : G) : Prop := ∀ n : Int, n • g = 0 → n = 0

/-- **T7 (binding in the value component).** If two openings `(v₁, r)` and
`(v₂, r)` of the same commitment share their randomness, and the base point
`g` is non-trivial (in the algebraic sense of `IsNonTrivial`, the consequence
of the DL hypothesis), then `v₁ = v₂`.

This is the binding property of Pedersen commitments in its "shared
randomness" form. The full binding theorem — where both `v` *and* `r` differ
— reduces to recovering the DL of `h` w.r.t. `g`, and is what a real binding
adversary outputs. -/
theorem commit_binding_value
    (g h : G) (v₁ v₂ r : Int) (hg : IsNonTrivial g)
    (heq : commit g h v₁ r = commit g h v₂ r) :
    v₁ = v₂ := by
  -- Subtracting the two commitments: 0 = (v₁ − v₂) • g + 0 • h = (v₁ − v₂) • g.
  have hsub : commit g h v₁ r - commit g h v₂ r = 0 := by
    rw [heq, sub_self]
  rw [commit_sub] at hsub
  -- `commit g h (v₁ − v₂) (r − r) = (v₁ − v₂) • g + 0 • h = (v₁ − v₂) • g`.
  unfold commit at hsub
  have hr : (r - r : Int) = 0 := sub_self r
  rw [hr, zero_zsmul, add_zero] at hsub
  -- Apply the DL hypothesis to (v₁ − v₂).
  have : v₁ - v₂ = 0 := hg _ hsub
  linarith

/-- **T8 (binding in the value component, contrapositive).** If `v₁ ≠ v₂`
and the base point `g` is non-trivial, then the two commitments
`c(v₁, r)` and `c(v₂, r)` are distinct. This is the form actually invoked
when arguing "different note values give distinct value commitments under
matching randomness". -/
theorem commit_distinct_of_value_distinct
    (g h : G) (v₁ v₂ r : Int) (hg : IsNonTrivial g)
    (hv : v₁ ≠ v₂) :
    commit g h v₁ r ≠ commit g h v₂ r := by
  intro heq
  exact hv (commit_binding_value g h v₁ v₂ r hg heq)

/-- **T9 (`IsNonTrivial` is preserved by negation).** A trivial sanity check
on the DL hypothesis: if `g` has no non-zero annihilator, then neither does
`−g`. Justifies the symmetry "either base point can play the role of the
binding base". -/
theorem isNonTrivial_neg (g : G) (hg : IsNonTrivial g) : IsNonTrivial (-g) := by
  intro n hn
  have : n • g = 0 := by
    have h1 : n • (-g) = -(n • g) := by simp
    rw [h1] at hn
    exact neg_eq_zero.mp hn
  exact hg n this

/-- **T10 (binding base is non-zero).** A non-trivial base point is itself
non-zero: `1 • g = g`, so if `g = 0` then the DL hypothesis would force
`1 = 0`. A sanity check that the algebraic form of the DL hypothesis is not
vacuously true. -/
theorem isNonTrivial_ne_zero (g : G) (hg : IsNonTrivial g) : g ≠ 0 := by
  intro h0
  have h1 : (1 : Int) • g = 0 := by rw [h0]; simp
  have : (1 : Int) = 0 := hg 1 h1
  exact one_ne_zero this

end Zebra.PedersenAbstract
