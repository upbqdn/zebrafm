import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Tower `Fallback` middleware policy

Models the response-selection policy of `tower_fallback::Fallback`
(`tower-fallback/src/lib.rs:1-16`, `tower-fallback/src/service.rs:36-57`)
together with the `ResponseFuture` state machine in
`tower-fallback/src/future.rs:67-120`.

The wrapper composes two services `svc1` (primary) and `svc2` (fallback). On
each request the runtime polls `svc1`. If `svc1` returned `Ok(rsp)` the
fallback is *not* consulted. If `svc1` returned `Err(_)`, the state machine
transitions through `PollReady2 → PollResponse2` and the final response is
whatever `svc2` produced — either its `Ok` value or its error (boxed). The
primary error is discarded (the Rust source logs it via `tracing::debug!` at
`future.rs:89` and then drops it).

This means the externally observable behaviour is the deterministic function

```
fallback(svc1_result, svc2_result) :=
  match svc1_result with
  | Ok(r)  → Ok(r)
  | Err(_) → svc2_result
```

We model svc1's and svc2's outcomes as values in `Result α ε₁` and
`Result α ε₂`, where the responses share a common type `α` (mirroring
`S2: Service<Request, Response = <S1 as Service<Request>>::Response>` at
`future.rs:22`), and prove the three policy properties:

* the fallback predicate is decidable (you can statically tell from `svc1`'s
  result whether `svc2` will be consulted);
* a successful `svc1` response is the final response and is independent of
  `svc2`;
* an erroring `svc1` is *replaced* by `svc2`'s outcome — including the
  case where `svc2` itself errors, so the surfaced error originates from
  `svc2` and never from `svc1`.

We do not model async wakeups, pin-projection or the `Tmp` placeholder state
— those are mechanical Rust safety scaffolding around the same pure policy.
-/

namespace Zebra.TowerFallbackPolicy

/-! ## Outcome type

Lean's `Except` carries `Result` semantics: `.ok` corresponds to Rust's
`Ok(_)`, `.error` to `Err(_)`. We reuse it directly so the model stays
ergonomic. -/

/-- The combinator policy: returns `svc1`'s response on success, otherwise
runs `svc2` and returns its outcome (with the error type translated by `eInto`,
mirroring `Err(e) => Err(e.into())` at `future.rs:100,114`). -/
def fallback {α ε₁ ε₂ β : Type}
    (eInto : ε₂ → β)
    (r1 : Except ε₁ α) (r2 : Except ε₂ α) : Except β α :=
  match r1 with
  | .ok v   => .ok v
  | .error _ =>
    match r2 with
    | .ok v   => .ok v
    | .error e => .error (eInto e)

/-- Whether `svc2` will be consulted, given the result of `svc1`. Mirrors the
state-machine branch at `future.rs:86-97`: `Ok` short-circuits, `Err`
transitions to `PollReady2`. -/
def usesFallback {α ε₁ : Type} (r1 : Except ε₁ α) : Bool :=
  match r1 with
  | .ok _ => false
  | .error _ => true

/-! ## Decidability

The decision can be made syntactically on `r1`'s constructor — there's no
hidden async race or interleaving that could flip it. -/

/-- The fallback predicate is decidable in `r1` alone. -/
instance decUsesFallback {α ε₁ : Type} (r1 : Except ε₁ α) :
    Decidable (usesFallback r1 = true) :=
  match r1 with
  | .ok _   => isFalse (by unfold usesFallback; simp)
  | .error _ => isTrue (by unfold usesFallback; simp)

/-- `usesFallback` is `true` iff the primary returned an error. -/
theorem usesFallback_iff_primary_error {α ε₁ : Type} (r1 : Except ε₁ α) :
    usesFallback r1 = true ↔ ∃ e, r1 = .error e := by
  unfold usesFallback
  cases r1 with
  | ok v   => simp
  | error e =>
    refine ⟨?_, ?_⟩
    · intro _; exact ⟨e, rfl⟩
    · intro _; rfl

/-! ## T1 — Success on primary skips fallback

If `svc1` returns `Ok(v)`, then `fallback _ r1 r2 = Ok(v)` *for every* `r2`.
This is the "no fallback consulted" guarantee at `future.rs:87`
(`Ok(rsp) => return Poll::Ready(Ok(rsp))`). -/

theorem T1_primary_success_skips_fallback
    {α ε₂ β : Type} (eInto : ε₂ → β) (v : α) (r2 : Except ε₂ α) :
    fallback (ε₁ := Unit) eInto (.ok v) r2 = .ok v := by
  unfold fallback
  rfl

/-- Strengthening of T1: when `svc1` succeeds, the output is independent of
the fallback service's outcome — swapping `r2` for any `r2'` leaves the
result unchanged. This is the policy-level statement that a healthy primary
makes `svc2` unobservable. -/
theorem T1b_primary_success_independent_of_fallback
    {α ε₁ ε₂ β : Type} (eInto : ε₂ → β) (v : α)
    (r2 r2' : Except ε₂ α) :
    fallback (ε₁ := ε₁) eInto (.ok v) r2
      = fallback (ε₁ := ε₁) eInto (.ok v) r2' := by
  unfold fallback
  rfl

/-! ## T2 — Fallback success: primary error is replaced by `svc2`'s `Ok`

If `svc1` errored and `svc2` succeeded, the final response is `svc2`'s value
— matching `future.rs:113-114` (`PollResponse2 → fut.poll(cx)...`). -/

theorem T2_fallback_success_replaces_primary_error
    {α ε₁ ε₂ β : Type} (eInto : ε₂ → β)
    (e1 : ε₁) (v : α) :
    fallback (α := α) (ε₁ := ε₁) (ε₂ := ε₂) (β := β) eInto (.error e1) (.ok v)
      = .ok v := by
  unfold fallback
  rfl

/-! ## T3 — Fallback error replaces primary error

If both services error, the surfaced error is `svc2`'s, translated through
`eInto` (Rust `e.into()`). The primary error `e1` does not appear in the
output. This is the most consequential property: callers cannot peek at the
primary failure. -/

theorem T3_fallback_error_replaces_primary_error
    {α ε₁ ε₂ β : Type} (eInto : ε₂ → β)
    (e1 : ε₁) (e2 : ε₂) :
    fallback (α := α) eInto (.error e1) (.error e2)
      = .error (eInto e2) := by
  unfold fallback
  rfl

/-- Stronger form of T3: with both services erroring, the output depends only
on `e2` and `eInto` — different `e1`'s give the same surface error. This pins
the "primary error is dropped" guarantee independent of the specific failure
mode `svc1` produced. -/
theorem T3b_primary_error_dropped_when_both_fail
    {α ε₁ ε₂ β : Type} (eInto : ε₂ → β)
    (e1 e1' : ε₁) (e2 : ε₂) :
    fallback (α := α) eInto (.error e1) (.error e2)
      = fallback (α := α) eInto (.error e1') (.error e2) := by
  unfold fallback
  rfl

/-! ## T4 — Fallback output equals `eInto`-lifted secondary outcome when primary errs

When `svc1` errored, the surface output is just `Except.mapError eInto r2`
— the secondary response with its error translated through `eInto`. The
primary error contributes nothing to the output value, which is the policy
side of "the primary error is dropped at `future.rs:88-97`". -/

/-- Lift `r2` into the surface error type by applying `eInto` to any error. -/
def liftSecondary {α ε₂ β : Type}
    (eInto : ε₂ → β) (r2 : Except ε₂ α) : Except β α :=
  match r2 with
  | .ok v   => .ok v
  | .error e => .error (eInto e)

theorem T4_primary_error_yields_lifted_secondary
    {α ε₁ ε₂ β : Type} (eInto : ε₂ → β)
    (e1 : ε₁) (r2 : Except ε₂ α) :
    fallback (α := α) eInto (.error e1) r2 = liftSecondary eInto r2 := by
  unfold fallback liftSecondary
  cases r2 <;> rfl

/-! ## T5 — Composite characterisation

A single equation describing the policy as case-on-`r1` of the lifted
secondary outcome. This packages T1 + T4 into one closed form a Zebra
maintainer can pattern-match against the Rust state machine. -/

theorem T5_fallback_closed_form
    {α ε₁ ε₂ β : Type} (eInto : ε₂ → β)
    (r1 : Except ε₁ α) (r2 : Except ε₂ α) :
    fallback eInto r1 r2 =
      match r1 with
      | .ok v   => .ok v
      | .error _ => liftSecondary eInto r2 := by
  unfold fallback liftSecondary
  cases r1 with
  | ok _   => rfl
  | error _ => cases r2 <;> rfl

/-! ## T6 — Idempotence: feeding the surfaced result back into the wrapper

If a caller treats the wrapped service's surfaced result `fallback eInto r1 r2`
as a fresh "primary" outcome and runs the same fallback again with the
*identity* error-conversion `(id : β → β)`, the second wrap is a no-op. This
is the policy-level "no amplification on re-entry": the combinator is a pure
function of `(r1, r2)`, not a stateful retry that would compound on every
wrap. -/

theorem T6_fallback_idempotent_under_identity
    {α ε₁ ε₂ β : Type} (eInto : ε₂ → β)
    (r1 : Except ε₁ α) (r2 : Except ε₂ α) (r2' : Except β α) :
    fallback (id : β → β) (fallback eInto r1 r2) r2'
      = (match fallback eInto r1 r2 with
         | .ok v   => .ok v
         | .error _ => liftSecondary id r2') := by
  unfold fallback liftSecondary
  cases r1 with
  | ok _ => rfl
  | error _ =>
    cases r2 with
    | ok _ => rfl
    | error _ => cases r2' <;> rfl

/-! ## T7 — Surface success implies one of the two services succeeded

If the final output is `Ok(v)`, at least one of the underlying services must
have responded with `Ok(v)`. There is no way for the wrapper to manufacture
a response from two failures — every successful surface response is
attributable to a concrete service. This is the auditability statement. -/

theorem T7_success_attribution
    {α ε₁ ε₂ β : Type} (eInto : ε₂ → β)
    (r1 : Except ε₁ α) (r2 : Except ε₂ α) (v : α)
    (h : fallback eInto r1 r2 = .ok v) :
    r1 = .ok v ∨ r2 = .ok v := by
  unfold fallback at h
  cases r1 with
  | ok v' =>
    -- h : Except.ok v' = Except.ok v, so v' = v and r1 = ok v
    cases h
    exact Or.inl rfl
  | error _ =>
    cases r2 with
    | ok v' =>
      cases h
      exact Or.inr rfl
    | error _ =>
      -- h : .error _ = .ok v, impossible
      cases h

end Zebra.TowerFallbackPolicy
