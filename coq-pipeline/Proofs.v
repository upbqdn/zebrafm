(** Proofs against the Aeneas-extracted Coq definitions.

    This file demonstrates that the same Rust source emitted as Coq is
    provable in Coq. We discharge a representative example; the full
    re-proof of every Lean theorem against the Coq extract is left as
    future work.

    The parent Lean project carries the full kernel-checked theorem set.
    This Coq backend serves as a foundational diversification: a Lean
    kernel bug does not invalidate the Coq proof.
*)

Require Import Primitives.
Require Import ZebraChainArith.

Import Result.
Import Notations.

(** Lemma: [try_from_u32] of 0 succeeds with 0. *)
Lemma try_from_u32_zero :
  height_try_from_u32 0%u32 = Ok (Some 0%u32).
Proof.
  unfold height_try_from_u32, height_MAX_AS_U32.
  reflexivity.
Qed.
