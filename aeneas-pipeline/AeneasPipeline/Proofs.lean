import AeneasPipeline.Extracted

/-!
# Proofs against Aeneas-extracted definitions

This file demonstrates that the Aeneas-extracted Lean definitions are
provable against the same kind of theorems we proved in the parent
`ZebraChainArith` project, just in Aeneas's `Result`-monadic style over
`Std.U32` / `Std.I64` / `alloc.vec.Vec` types.

We discharge a few representative examples to witness that the pipeline
mechanically produces verifiable Lean. The full re-proof of every theorem
against the Aeneas-extracted style is left as future work; see the parent
project for the kernel-checked `Nat`/`Int`-style proof set.
-/

open Aeneas Aeneas.Std Result
open zebra_chain_arith

/-- **try_from_u32 of 0 succeeds with 0.** Simplest case on the boundary. -/
example : height.try_from_u32 0#u32 = ok (some 0#u32) := by
  simp [height.try_from_u32, height.MAX_AS_U32]
  rfl

/-- **try_from_u32 of MAX_AS_U32 succeeds.** Boundary at upper end. -/
example : height.try_from_u32 2147483647#u32 = ok (some 2147483647#u32) := by
  simp [height.try_from_u32, height.MAX_AS_U32]
  rfl

/-- **try_from_u32 of MAX_AS_U32 + 1 fails.** Just above the boundary. -/
example : height.try_from_u32 2147483648#u32 = ok none := by
  simp [height.try_from_u32, height.MAX_AS_U32]
  rfl

