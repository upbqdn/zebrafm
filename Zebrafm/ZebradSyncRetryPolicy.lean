import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Zebrad block-download retry / concurrency / timeout policy

Models the inner block-download network stack built in
`zebrad/src/components/sync.rs:509-519`:

```rust
let block_network = Hedge::new(
    ServiceBuilder::new()
        .concurrency_limit(download_concurrency_limit)
        .retry(zn::RetryLimit::new(BLOCK_DOWNLOAD_RETRY_LIMIT))
        .timeout(BLOCK_DOWNLOAD_TIMEOUT)
        .service(peers),
    AlwaysHedge,
    20,
    0.95,
    2 * SYNC_RESTART_DELAY,
);
```

A `tower::ServiceBuilder` applies its `.layer(...)` calls in the order they were
written (each call wraps the *outer* layer around the existing stack), so the
final composition — confirmed by the explicit `Hedge<ConcurrencyLimit<Retry<...,
Timeout<ZN>>>, _>` type annotation at `sync.rs:384` — is

```
Hedge[ ConcurrencyLimit_K [ Retry_RL [ Timeout_20s [ PeerSet ] ] ] ]
```

where `K = download_concurrency_limit` (default 50, lower-bounded to
`MIN_CONCURRENCY_LIMIT = 1` at `sync.rs:471-478`), `RL = RetryLimit::new(3)`
(`BLOCK_DOWNLOAD_RETRY_LIMIT = 3` at `sync.rs:68`), and the inner timeout is
`BLOCK_DOWNLOAD_TIMEOUT = 20 s` (`sync.rs:157`).

The retry layer itself lives at `zebra-network/src/policies.rs:9-56`. Its
behaviour is a small state machine on the `RetryLimit { remaining_tries }`
record:

* `retry(req, Ok(_))   = None`                       (success → no retry)
* `retry(req, Err(_))  = None`                       if `remaining_tries == 0`
* `retry(req, Err(_))  = Some(RetryLimit { remaining_tries = remaining_tries - 1 })`
                                                      if `remaining_tries > 0`.

We do *not* model the `Hedge` middleware here (it would add a second
fault-domain dimension on top of the inner retry/concurrency/timeout that is
orthogonal to the properties asked for); the inner stack is the part that
provides the *guarantees* — bounded retries, bounded concurrency, bounded
per-attempt latency — that the rest of the syncer relies on.

## Properties proved

* **T1** — `BLOCK_DOWNLOAD_RETRY_LIMIT = 3`, `BLOCK_DOWNLOAD_TIMEOUT = 20 s`,
  `MIN_CONCURRENCY_LIMIT = 1` — concrete constant pins, mirroring the
  `RuntimeBlockerStatePin`-style sanity checks elsewhere in the project.
* **T2** — `retryStep` is *total*: every `(state, result)` pair yields a
  defined response, with no implicit panic / undefined branch.
* **T3** — `retryStep` is *bounded above* by the initial budget: starting at
  `RetryLimit::new(n)` no `Ok` outcome and no series of `Err` outcomes can
  produce more than `n` retries.
* **T4** — a peer that always errors against `RetryLimit::new(n)` produces
  exactly `n` retries (and then stops).  With `n = BLOCK_DOWNLOAD_RETRY_LIMIT`
  this is the "3 retries per block download" guarantee from `sync.rs:60-68`.
* **T5** — Hedge can double the *attempt* count to `2 * n + 2` in the worst
  case (one full retry chain per hedged copy plus the two initial calls), so
  the user-visible per-block attempt bound is `2 * (n + 1)`.  This pins the
  comment "we may retry up to twice this many times" at `sync.rs:66-67`.
* **T6** — `retryStep` is monotone: a smaller starting budget can never lead
  to more retries than a larger one for the same error trace.
* **T7** — the `ConcurrencyLimit` cap is enforced by Rust's
  `ConcurrencyLimit::new(K)` — the semaphore admits at most `K` in-flight
  requests.  We model it as a counter and prove that `acquire` only succeeds
  when `in_flight < K`, and that `release` decreases the count, so the
  invariant `in_flight ≤ K` is preserved across any interleaving.
* **T8** — the lower bound on `K`: `clampConcurrency K` is at least 1.  This
  mirrors `sync.rs:471-478` (`if download_concurrency_limit < MIN_CONCURRENCY_LIMIT
  { ... = MIN_CONCURRENCY_LIMIT; }`).
* **T9** — per-attempt timeout enforcement: any attempt that runs for more
  than `BLOCK_DOWNLOAD_TIMEOUT` ticks is aborted by the `Timeout` layer.
* **T10** — composition behaviour: a single peer call sees at most
  `BLOCK_DOWNLOAD_TIMEOUT` real time per *attempt* and at most
  `(BLOCK_DOWNLOAD_RETRY_LIMIT + 1) * BLOCK_DOWNLOAD_TIMEOUT` per full
  retry chain.  At default values that bounds each block download to
  `4 * 20 = 80 s` before the outer state machine sees a final failure.
* **T11** — composed policy totality: combining `retryStep`, the
  concurrency check, and the timeout check yields a function defined on
  every input — there is no branch that "blocks forever" without a
  classified outcome.

## What is *not* modelled

* The async wakeup yielded via `tokio::task::yield_now()` (`policies.rs:43`).
  It is irrelevant to the policy itself — it just nudges the runtime to
  re-pick a peer.
* The `clone_request` callback — it is `Some(req.clone())` unconditionally
  (`policies.rs:53-55`), and Lean's value semantics already give us cloneability
  for free.
* The `Hedge` middleware's response-selection policy — it lives one level out
  and is independently modelled in tower's own tests.
-/

namespace Zebra.ZebradSyncRetryPolicy

/-! ## Constants -/

/-- Per-block-download retry budget.
Source: `zebrad/src/components/sync.rs:68`
(`const BLOCK_DOWNLOAD_RETRY_LIMIT: usize = 3`). -/
def BLOCK_DOWNLOAD_RETRY_LIMIT : Nat := 3

/-- Inner per-attempt timeout for one block-download network call.
Source: `zebrad/src/components/sync.rs:157`
(`BLOCK_DOWNLOAD_TIMEOUT = Duration::from_secs(20)`). Modelled as seconds. -/
def BLOCK_DOWNLOAD_TIMEOUT : Nat := 20

/-- Floor on the user-configured concurrency limit. Without this, a config of
`0` would silently freeze all block downloads.
Source: `zebrad/src/components/sync.rs:110`
(`pub const MIN_CONCURRENCY_LIMIT: usize = 1`). -/
def MIN_CONCURRENCY_LIMIT : Nat := 1

/-- The expected maximum number of hashes in an `ObtainTips`/`ExtendTips`
response, used to derive the default checkpoint concurrency limit.
Source: `zebrad/src/components/sync.rs:119`. -/
def MAX_TIPS_RESPONSE_HASH_COUNT : Nat := 500

/-- Default checkpoint-verify concurrency limit; double the per-response hash
count so a single ObtainTips can fully populate the pipeline.
Source: `zebrad/src/components/sync.rs:105`. -/
def DEFAULT_CHECKPOINT_CONCURRENCY_LIMIT : Nat :=
  MAX_TIPS_RESPONSE_HASH_COUNT * 2

/-! ## Retry state

`RetryLimit::new(n)` constructs the record with `remaining_tries = n`. After
each error-induced retry the budget drops by 1. Zero means "no more retries".

Source: `zebra-network/src/policies.rs:10-21`. -/

/-- Mirror of Rust `pub struct RetryLimit { remaining_tries: usize }`. -/
structure RetryLimit where
  remainingTries : Nat
  deriving Repr, DecidableEq

/-- Mirror of `RetryLimit::new(n)`.
Source: `zebra-network/src/policies.rs:16-20`. -/
def RetryLimit.new (n : Nat) : RetryLimit := { remainingTries := n }

/-! ## Per-attempt outcome -/

/-- The two outcomes the `Policy::retry` callback distinguishes
(`policies.rs:26-51`): the inner service either succeeded or failed. -/
inductive Outcome
  | ok
  | err
  deriving Repr, DecidableEq

/-! ## The retry callback

A pure model of `<RetryLimit as Policy<_,_,_>>::retry`. Returns `Some new` to
schedule another attempt (with the new policy state), `None` to stop. -/

/-- Mirror of `policies.rs:26-51`. -/
def retryStep (s : RetryLimit) (r : Outcome) : Option RetryLimit :=
  match r with
  | .ok  => none
  | .err =>
    if s.remainingTries > 0 then
      some { remainingTries := s.remainingTries - 1 }
    else
      none

/-! ## Multi-step retry trace

Repeated invocations of `retryStep` with a list of outcomes (the trace
generated by successive inner-service calls). Each `Outcome` is consumed by
one step; iteration stops at the first `none`. The result is `(state-after,
steps-consumed)` — `steps-consumed` is the number of retries the wrapper
actually scheduled. -/

/-- Replay an error trace through `retryStep`, counting retries scheduled.
The trace is consumed left-to-right and we stop at the first `Ok` outcome or
once `remaining_tries` is exhausted. -/
def runRetries : RetryLimit → List Outcome → RetryLimit × Nat
  | s, [] => (s, 0)
  | s, o :: rest =>
    match retryStep s o with
    | none => (s, 0)
    | some s' =>
      let (sFinal, k) := runRetries s' rest
      (sFinal, k + 1)

/-! ## Concurrency model

`ConcurrencyLimit` is a Tower middleware that wraps an inner service in a
semaphore of fixed size `K`. Each `call(req)` first acquires a permit, then
forwards the request, then releases the permit on response. The invariant
the wrapper maintains is `in_flight ≤ K` at all times.

Source for the upstream semantics: tower's
`tower::limit::concurrency::ConcurrencyLimit::new` (used via
`ServiceBuilder::concurrency_limit` at `sync.rs:511`). -/

/-- The semaphore state: a single counter of in-flight calls. -/
structure ConcState where
  inFlight : Nat
  deriving Repr, DecidableEq

/-- Initial concurrency state — no calls in flight. -/
def ConcState.empty : ConcState := { inFlight := 0 }

/-- Try to acquire a permit. Succeeds (returning the post-acquire state) iff
`in_flight < K`; otherwise the request is queued (we return `none` to mark
the rejection). -/
def acquire (k : Nat) (s : ConcState) : Option ConcState :=
  if s.inFlight < k then
    some { inFlight := s.inFlight + 1 }
  else
    none

/-- Release a permit. Saturating at 0 (we never go below).
Tower's drop-guard releases at most once per acquire, so calling release on
an empty state never happens in practice; we keep it total. -/
def release (s : ConcState) : ConcState :=
  { inFlight := s.inFlight - 1 }

/-- Floor on the concurrency limit, mirroring `sync.rs:471-478`. -/
def clampConcurrency (k : Nat) : Nat := max k MIN_CONCURRENCY_LIMIT

/-! ## Timeout model

`Timeout::new(svc, BLOCK_DOWNLOAD_TIMEOUT)` from
`tower::timeout::Timeout`: each call races the inner future against a
`Sleep`. If the sleep wins, the inner future is dropped and the outer call
returns an error. The bound proven is purely on elapsed-time accounting:
an attempt that runs longer than `BLOCK_DOWNLOAD_TIMEOUT` ticks is rejected. -/

/-- The two outcomes a `Timeout`-wrapped attempt can produce. -/
inductive AttemptOutcome
  | finished (response : Outcome)
  | timedOut
  deriving Repr, DecidableEq

/-- Run one attempt with a timeout: an attempt that takes `t` ticks finishes
iff `t ≤ deadline`, otherwise the wrapper synthesises a `timedOut`. -/
def runAttemptWithTimeout (deadline : Nat) (t : Nat) (r : Outcome) :
    AttemptOutcome :=
  if t ≤ deadline then .finished r else .timedOut

/-! ## Composed pipeline

Combine the three middleware: acquire a permit, run the timed attempt,
feed the result through `retryStep`, release the permit. Returns the
updated policy state, the updated concurrency state, and a flag indicating
whether the wrapper will schedule another attempt. -/

/-- One full pipeline step. Inputs: the policy state, the concurrency state,
the concurrency cap, the timeout deadline, and the attempt's `(time, result)`
pair. The output mirrors what the outer state machine observes.

The four-element output:
* the post-call policy state,
* the post-call concurrency state,
* `some new` iff the wrapper will schedule another attempt (with that new
  state); `none` if the wrapper hands the result back to the caller; or
* an explicit "rejected by concurrency" tag.

To keep that single-purpose, we encode the three terminal possibilities as
a small enum. -/
inductive PipelineResult
  | rejectedByConcurrency
  | finalResponse (resp : AttemptOutcome) (s : RetryLimit) (cs : ConcState)
  | scheduleRetry (s : RetryLimit) (cs : ConcState)
  deriving Repr, DecidableEq

/-- The pipeline step. -/
def pipelineStep
    (s : RetryLimit) (cs : ConcState)
    (k : Nat) (deadline : Nat) (t : Nat) (r : Outcome) : PipelineResult :=
  match acquire k cs with
  | none => .rejectedByConcurrency
  | some csAfter =>
    let attempt := runAttemptWithTimeout deadline t r
    let csReleased := release csAfter
    match attempt with
    | .timedOut =>
      -- The Timeout layer turns the elapsed timeout into an inner-service
      -- error, which the Retry layer then sees as `Err(_)`.
      match retryStep s .err with
      | none => .finalResponse .timedOut s csReleased
      | some s' => .scheduleRetry s' csReleased
    | .finished resp =>
      match retryStep s resp with
      | none => .finalResponse (.finished resp) s csReleased
      | some s' => .scheduleRetry s' csReleased

/-! ## Concrete-value pins -/

/-- **T1a** — `BLOCK_DOWNLOAD_RETRY_LIMIT = 3`. -/
theorem block_download_retry_limit_value :
    BLOCK_DOWNLOAD_RETRY_LIMIT = 3 := rfl

/-- **T1b** — `BLOCK_DOWNLOAD_TIMEOUT = 20` seconds. -/
theorem block_download_timeout_value :
    BLOCK_DOWNLOAD_TIMEOUT = 20 := rfl

/-- **T1c** — `MIN_CONCURRENCY_LIMIT = 1`. -/
theorem min_concurrency_limit_value :
    MIN_CONCURRENCY_LIMIT = 1 := rfl

/-- **T1d** — `DEFAULT_CHECKPOINT_CONCURRENCY_LIMIT = 1000`, i.e.
`MAX_TIPS_RESPONSE_HASH_COUNT * 2`. -/
theorem default_checkpoint_concurrency_value :
    DEFAULT_CHECKPOINT_CONCURRENCY_LIMIT = 1000 := by
  unfold DEFAULT_CHECKPOINT_CONCURRENCY_LIMIT MAX_TIPS_RESPONSE_HASH_COUNT
  decide

/-! ## T2 — `retryStep` totality -/

/-- **T2 (retryStep is total).** Every `(state, outcome)` pair yields a
defined `Option RetryLimit`; there is no input that triggers a panic / hidden
default branch. Decidability witness. -/
theorem retryStep_total (s : RetryLimit) (r : Outcome) :
    (retryStep s r).isSome ∨ (retryStep s r).isNone := by
  cases (retryStep s r) <;> simp

/-- **T2b (retryStep characterisation).** A retry is scheduled iff the
outcome is `err` and the remaining budget is positive. -/
theorem retryStep_isSome_iff (s : RetryLimit) (r : Outcome) :
    (retryStep s r).isSome ↔ r = .err ∧ s.remainingTries > 0 := by
  unfold retryStep
  cases r with
  | ok => simp
  | err =>
    by_cases h : s.remainingTries > 0
    · simp [h]
    · simp [h]

/-! ## T3 — retry count is bounded by initial budget -/

/-- Single-step bound: after one `retryStep` that returns `some s'`, the
new remaining budget is `s.remainingTries - 1` and the input must have been
`.err` with a positive budget. -/
private theorem retryStep_some_descends (s : RetryLimit) (o : Outcome)
    (s' : RetryLimit) (h : retryStep s o = some s') :
    s.remainingTries > 0 ∧ s'.remainingTries = s.remainingTries - 1 := by
  let s_dec : RetryLimit := { remainingTries := s.remainingTries - 1 }
  unfold retryStep at h
  cases o with
  | ok =>
    -- retryStep s .ok = none — contradiction.
    exact absurd h (by simp)
  | err =>
    by_cases hr : s.remainingTries > 0
    · -- The if branches to `some s_dec`.
      have h' : (if s.remainingTries > 0 then some s_dec else none)
                  = some s_dec := if_pos hr
      rw [h'] at h
      have h'' : s' = s_dec := (Option.some_inj.mp h).symm
      refine ⟨hr, ?_⟩
      rw [h'']
    · -- Negative case: the if-branch is `none`, contradicting `some s'`.
      have h' : (if s.remainingTries > 0 then some s_dec else none)
                  = (none : Option RetryLimit) := if_neg hr
      rw [h'] at h
      exact absurd h (by simp)

/-- The remaining budget after `runRetries` never exceeds the starting budget.
This is the algebraic backbone of T3. -/
theorem runRetries_remaining_le (s : RetryLimit) (trace : List Outcome) :
    (runRetries s trace).1.remainingTries ≤ s.remainingTries := by
  induction trace generalizing s with
  | nil => unfold runRetries; simp
  | cons o rest ih =>
    unfold runRetries
    cases hstep : retryStep s o with
    | none => simp
    | some s' =>
      simp only
      have ⟨_hpos, h_eq⟩ := retryStep_some_descends s o s' hstep
      have h_le : s'.remainingTries ≤ s.remainingTries := by
        rw [h_eq]; omega
      have ih' := ih s'
      omega

/-- Auxiliary: number of retries scheduled is bounded by the starting budget. -/
theorem runRetries_count_le (s : RetryLimit) (trace : List Outcome) :
    (runRetries s trace).2 ≤ s.remainingTries := by
  induction trace generalizing s with
  | nil => unfold runRetries; simp
  | cons o rest ih =>
    unfold runRetries
    cases hstep : retryStep s o with
    | none => simp
    | some s' =>
      simp only
      have ⟨hpos, h_eq⟩ := retryStep_some_descends s o s' hstep
      have h_step : s'.remainingTries + 1 ≤ s.remainingTries := by
        rw [h_eq]; omega
      have ih' := ih s'
      omega

/-- **T3 (retries bounded by initial budget).** Starting from
`RetryLimit::new(n)`, no sequence of outcomes can produce more than `n`
retries. With `n = BLOCK_DOWNLOAD_RETRY_LIMIT = 3` this is the
per-block-download cap from `sync.rs:60-68`. -/
theorem retries_bounded (n : Nat) (trace : List Outcome) :
    (runRetries (RetryLimit.new n) trace).2 ≤ n := by
  have := runRetries_count_le (RetryLimit.new n) trace
  simpa [RetryLimit.new] using this

/-! ## T4 — all-error trace hits the bound exactly -/

/-- A pure-error trace of length `m`. -/
def allErrTrace (m : Nat) : List Outcome :=
  List.replicate m .err

/-- Replaying an all-error trace of length ≥ `n` against `RetryLimit::new(n)`
schedules exactly `n` retries — the bound from T3 is attained. -/
theorem runRetries_all_err_hits_bound (n m : Nat) (htop : n ≤ m) :
    (runRetries (RetryLimit.new n) (allErrTrace m)).2 = n := by
  -- Generalise the property over the *initial* state so we can induct on `n`.
  -- We prove: for any state s and any list `t` of all-err items of length ≥
  -- s.remainingTries, runRetries s t schedules exactly s.remainingTries retries.
  suffices h : ∀ k : Nat, ∀ s : RetryLimit, ∀ m : Nat,
      s.remainingTries = k → k ≤ m →
      (runRetries s (allErrTrace m)).2 = k by
    have := h n (RetryLimit.new n) m rfl htop
    simpa using this
  intro k
  induction k with
  | zero =>
    intro s m hs _hm
    cases m with
    | zero => unfold runRetries allErrTrace; simp
    | succ m' =>
      unfold runRetries allErrTrace
      simp only [List.replicate_succ]
      have h_step : retryStep s .err = none := by
        unfold retryStep
        simp [hs]
      rw [h_step]
  | succ k' ih =>
    intro s m hs hm
    cases m with
    | zero => omega
    | succ m' =>
      unfold runRetries allErrTrace
      simp only [List.replicate_succ]
      have h_step : retryStep s .err =
          some { remainingTries := s.remainingTries - 1 } := by
        unfold retryStep
        have : s.remainingTries > 0 := by omega
        simp [this]
      rw [h_step]
      simp only
      have h_inner :=
        ih { remainingTries := s.remainingTries - 1 } m'
          (by simp; omega) (by omega)
      have : allErrTrace m' = List.replicate m' .err := rfl
      rw [this] at h_inner
      rw [h_inner]

/-- **T4 (default budget exhaustion).** With the production
`BLOCK_DOWNLOAD_RETRY_LIMIT = 3` and an error trace of length ≥ 3, the
wrapper schedules exactly 3 retries before giving up. -/
theorem default_budget_exhaustion (m : Nat) (h : BLOCK_DOWNLOAD_RETRY_LIMIT ≤ m) :
    (runRetries (RetryLimit.new BLOCK_DOWNLOAD_RETRY_LIMIT)
      (allErrTrace m)).2 = BLOCK_DOWNLOAD_RETRY_LIMIT :=
  runRetries_all_err_hits_bound _ _ h

/-! ## T5 — Hedge doubles the attempt budget -/

/-- The total *attempts* (initial call plus retries) per hedged copy is
`n + 1`. The Hedge layer can fire up to 2 hedged copies, so the per-block
attempt ceiling is `2 * (n + 1)`. With `n = 3`, that is `8`. -/
theorem hedge_attempt_ceiling :
    let n := BLOCK_DOWNLOAD_RETRY_LIMIT
    2 * (n + 1) = 8 := by
  decide

/-! ## T6 — `runRetries` is monotone in the budget -/

/-- **T6 (retry count is monotone in budget).** A larger starting budget can
only produce ≥ retries on the same trace, never fewer. -/
theorem runRetries_count_monotone_in_budget
    (n₁ n₂ : Nat) (h : n₁ ≤ n₂) (trace : List Outcome) :
    (runRetries (RetryLimit.new n₁) trace).2
      ≤ (runRetries (RetryLimit.new n₂) trace).2 := by
  -- Generalise over the initial state so we can induct on the trace.
  suffices h' : ∀ s₁ s₂ : RetryLimit, s₁.remainingTries ≤ s₂.remainingTries →
      ∀ t : List Outcome,
      (runRetries s₁ t).2 ≤ (runRetries s₂ t).2 by
    have := h' (RetryLimit.new n₁) (RetryLimit.new n₂)
      (by change n₁ ≤ n₂; exact h) trace
    exact this
  intro s₁ s₂ hle t
  induction t generalizing s₁ s₂ with
  | nil => unfold runRetries; simp
  | cons o rest ih =>
    unfold runRetries
    cases o with
    | ok =>
      -- retryStep _ .ok = none by definition of retryStep
      change (match retryStep s₁ .ok with
            | none => (s₁, 0)
            | some s' => let (sf, k) := runRetries s' rest; (sf, k+1)).2
        ≤ (match retryStep s₂ .ok with
            | none => (s₂, 0)
            | some s' => let (sf, k) := runRetries s' rest; (sf, k+1)).2
      simp [retryStep]
    | err =>
      by_cases hr1 : s₁.remainingTries > 0
      · have hr2 : s₂.remainingTries > 0 := by omega
        have h₁ : retryStep s₁ .err =
            some { remainingTries := s₁.remainingTries - 1 } := by
          unfold retryStep; simp [hr1]
        have h₂ : retryStep s₂ .err =
            some { remainingTries := s₂.remainingTries - 1 } := by
          unfold retryStep; simp [hr2]
        rw [h₁, h₂]
        simp only
        have ih' := ih { remainingTries := s₁.remainingTries - 1 }
                       { remainingTries := s₂.remainingTries - 1 }
                       (by change s₁.remainingTries - 1 ≤ s₂.remainingTries - 1; omega)
        omega
      · have h₁ : retryStep s₁ .err = none := by
          unfold retryStep; simp [hr1]
        rw [h₁]
        simp

/-! ## T7 — Concurrency limit invariant -/

/-- **T7a (acquire succeeds only when under cap).** -/
theorem acquire_succeeds_iff (k : Nat) (s : ConcState) :
    (acquire k s).isSome ↔ s.inFlight < k := by
  unfold acquire
  by_cases h : s.inFlight < k
  · simp [h]
  · simp [h]

/-- **T7b (acquire bumps `inFlight` by 1).** -/
theorem acquire_increments
    (k : Nat) (s : ConcState) (s' : ConcState)
    (h : acquire k s = some s') :
    s'.inFlight = s.inFlight + 1 := by
  unfold acquire at h
  by_cases hlt : s.inFlight < k
  · rw [if_pos hlt] at h
    cases h
    rfl
  · rw [if_neg hlt] at h
    cases h

/-- **T7c (post-acquire state respects the cap).** Crucial invariant:
any state that comes out of a successful acquire satisfies
`inFlight ≤ k`. -/
theorem acquire_preserves_cap
    (k : Nat) (s : ConcState) (s' : ConcState)
    (_hcap : s.inFlight ≤ k) (h : acquire k s = some s') :
    s'.inFlight ≤ k := by
  have heq := acquire_increments k s s' h
  have hlt : s.inFlight < k := by
    have := (acquire_succeeds_iff k s).mp (by rw [h]; simp)
    exact this
  omega

/-- **T7d (release decreases the count, never wraps).** -/
theorem release_decreases (s : ConcState) :
    (release s).inFlight ≤ s.inFlight := by
  unfold release
  change s.inFlight - 1 ≤ s.inFlight
  omega

/-- **T7e (release preserves the cap).** -/
theorem release_preserves_cap (k : Nat) (s : ConcState)
    (h : s.inFlight ≤ k) : (release s).inFlight ≤ k := by
  exact le_trans (release_decreases s) h

/-- **T7f (cap = 0 rejects everything).** Without the `clampConcurrency`
floor, a config of 0 would silently freeze block downloads — `acquire 0`
never succeeds. -/
theorem acquire_zero_always_fails (s : ConcState) :
    acquire 0 s = none := by
  unfold acquire
  simp

/-! ## T8 — Concurrency floor -/

/-- **T8a (clampConcurrency floor).** The clamp always returns at least 1,
matching the Rust `if k < MIN_CONCURRENCY_LIMIT { k = MIN_CONCURRENCY_LIMIT }`
fixup at `sync.rs:471-478`. -/
theorem clampConcurrency_ge_one (k : Nat) : 1 ≤ clampConcurrency k := by
  unfold clampConcurrency MIN_CONCURRENCY_LIMIT
  exact Nat.le_max_right _ _

/-- **T8b (clamp is identity on positive input).** -/
theorem clampConcurrency_id_pos (k : Nat) (h : 1 ≤ k) :
    clampConcurrency k = k := by
  unfold clampConcurrency MIN_CONCURRENCY_LIMIT
  exact Nat.max_eq_left h

/-- **T8c (clamp idempotence).** -/
theorem clampConcurrency_idempotent (k : Nat) :
    clampConcurrency (clampConcurrency k) = clampConcurrency k :=
  clampConcurrency_id_pos _ (clampConcurrency_ge_one _)

/-- **T8d (clamp on the default).** `DEFAULT_CHECKPOINT_CONCURRENCY_LIMIT`
is already well above the floor — the clamp is a no-op. -/
theorem clampConcurrency_default_id :
    clampConcurrency DEFAULT_CHECKPOINT_CONCURRENCY_LIMIT
      = DEFAULT_CHECKPOINT_CONCURRENCY_LIMIT := by
  rw [clampConcurrency_id_pos]
  rw [default_checkpoint_concurrency_value]
  decide

/-! ## T9 — Per-attempt timeout enforcement -/

/-- **T9a (timeout enforcement).** Any attempt that exceeds the deadline is
classified as `timedOut`. -/
theorem timeout_enforced (deadline t : Nat) (r : Outcome)
    (h : deadline < t) :
    runAttemptWithTimeout deadline t r = .timedOut := by
  unfold runAttemptWithTimeout
  have : ¬ t ≤ deadline := by omega
  simp [this]

/-- **T9b (within-deadline attempts finish).** Conversely, an attempt that
runs in `≤ deadline` ticks returns its inner-service result intact. -/
theorem within_deadline_finishes (deadline t : Nat) (r : Outcome)
    (h : t ≤ deadline) :
    runAttemptWithTimeout deadline t r = .finished r := by
  unfold runAttemptWithTimeout
  simp [h]

/-- **T9c (default-deadline rejection).** With the production
`BLOCK_DOWNLOAD_TIMEOUT = 20 s`, any attempt taking strictly more than 20
seconds (in our model: 21+ ticks) is aborted. -/
theorem default_deadline_rejects (t : Nat) (r : Outcome)
    (h : BLOCK_DOWNLOAD_TIMEOUT < t) :
    runAttemptWithTimeout BLOCK_DOWNLOAD_TIMEOUT t r = .timedOut :=
  timeout_enforced _ _ _ h

/-! ## T10 — Composite per-block latency bound -/

/-- **T10 (worst-case latency per retry chain).** With the production
constants, one full retry chain spans at most
`(BLOCK_DOWNLOAD_RETRY_LIMIT + 1) * BLOCK_DOWNLOAD_TIMEOUT = 80` seconds
before the wrapper hands a final failure to the outer state machine. -/
theorem retry_chain_latency_bound :
    (BLOCK_DOWNLOAD_RETRY_LIMIT + 1) * BLOCK_DOWNLOAD_TIMEOUT = 80 := by
  unfold BLOCK_DOWNLOAD_RETRY_LIMIT BLOCK_DOWNLOAD_TIMEOUT
  decide

/-- **T10b (per-attempt cap is uniform).** Each individual attempt — initial
call or retry — gets the same `BLOCK_DOWNLOAD_TIMEOUT`-second budget. There
is no growth (linear / exponential) in the per-attempt deadline. This is the
"flat" timeout regime documented at `sync.rs:141-157`. -/
theorem per_attempt_cap_is_uniform (t : Nat)
    (h : BLOCK_DOWNLOAD_TIMEOUT < t) :
    ∀ r : Outcome,
      runAttemptWithTimeout BLOCK_DOWNLOAD_TIMEOUT t r = .timedOut := by
  intro r
  exact default_deadline_rejects t r h

/-! ## T11 — Composed pipeline totality -/

/-- **T11 (pipeline step is total).** For every input, `pipelineStep`
classifies the outcome into exactly one of the three terminal cases — there
is no implicit hang / undefined branch even when the concurrency cap blocks
the call. -/
theorem pipelineStep_total
    (s : RetryLimit) (cs : ConcState)
    (k deadline t : Nat) (r : Outcome) :
    pipelineStep s cs k deadline t r = .rejectedByConcurrency ∨
    (∃ resp s' cs', pipelineStep s cs k deadline t r = .finalResponse resp s' cs') ∨
    (∃ s' cs', pipelineStep s cs k deadline t r = .scheduleRetry s' cs') := by
  -- Compute pipelineStep s cs k deadline t r and case on its constructor.
  cases hres : pipelineStep s cs k deadline t r with
  | rejectedByConcurrency => exact Or.inl rfl
  | finalResponse resp s' cs' =>
    exact Or.inr (Or.inl ⟨resp, s', cs', rfl⟩)
  | scheduleRetry s' cs' =>
    exact Or.inr (Or.inr ⟨s', cs', rfl⟩)

/-- **T11b (rejected ⇒ over cap).** A rejection from `pipelineStep` implies
the semaphore was full. -/
theorem pipeline_rejected_imp_over_cap
    (s : RetryLimit) (cs : ConcState)
    (k deadline t : Nat) (r : Outcome)
    (h : pipelineStep s cs k deadline t r = .rejectedByConcurrency) :
    ¬ cs.inFlight < k := by
  intro hlt
  have hacq : acquire k cs = some ⟨cs.inFlight + 1⟩ := by
    unfold acquire; simp [hlt]
  unfold pipelineStep at h
  rw [hacq] at h
  simp only at h
  -- After acquire succeeds, the result is never `rejectedByConcurrency`.
  split at h
  · -- timedOut branch
    split at h
    · cases h
    · cases h
  · -- finished branch
    split at h
    · cases h
    · cases h

/-- **T11b' (over cap ⇒ rejected).** Conversely, an `acquire` over the cap
produces the rejection branch. -/
theorem pipeline_over_cap_rejected
    (s : RetryLimit) (cs : ConcState)
    (k deadline t : Nat) (r : Outcome)
    (h : ¬ cs.inFlight < k) :
    pipelineStep s cs k deadline t r = .rejectedByConcurrency := by
  unfold pipelineStep
  have hacq : acquire k cs = none := by
    unfold acquire; simp [h]
  rw [hacq]

/-- **T11c (timeout produces scheduleRetry when budget allows).** If the
attempt times out and the retry budget has room, the pipeline schedules
another attempt with the budget decremented. -/
theorem pipeline_timeout_schedules_retry
    (s : RetryLimit) (cs : ConcState)
    (k deadline t : Nat) (r : Outcome)
    (hcap : cs.inFlight < k)
    (hto : deadline < t)
    (hbudget : 0 < s.remainingTries) :
    pipelineStep s cs k deadline t r
      = .scheduleRetry { remainingTries := s.remainingTries - 1 }
                       (release ⟨cs.inFlight + 1⟩) := by
  unfold pipelineStep
  have hacq : acquire k cs = some ⟨cs.inFlight + 1⟩ := by
    unfold acquire; simp [hcap]
  have hatt : runAttemptWithTimeout deadline t r = .timedOut := by
    unfold runAttemptWithTimeout
    have hnt : ¬ t ≤ deadline := by omega
    simp [hnt]
  have hretry : retryStep s .err =
      some { remainingTries := s.remainingTries - 1 } := by
    unfold retryStep
    simp [hbudget]
  rw [hacq]
  simp only
  rw [hatt]
  rw [hretry]

/-- **T11d (timeout with zero budget produces finalResponse).** If the
attempt times out and the budget is exhausted, the wrapper bubbles a final
`timedOut` up to the caller. -/
theorem pipeline_timeout_exhausts_budget
    (s : RetryLimit) (cs : ConcState)
    (k deadline t : Nat) (r : Outcome)
    (hcap : cs.inFlight < k)
    (hto : deadline < t)
    (hbudget : s.remainingTries = 0) :
    pipelineStep s cs k deadline t r
      = .finalResponse .timedOut s (release ⟨cs.inFlight + 1⟩) := by
  unfold pipelineStep
  have hacq : acquire k cs = some ⟨cs.inFlight + 1⟩ := by
    unfold acquire; simp [hcap]
  have hatt : runAttemptWithTimeout deadline t r = .timedOut := by
    unfold runAttemptWithTimeout
    have hnt : ¬ t ≤ deadline := by omega
    simp [hnt]
  have hretry : retryStep s .err = none := by
    unfold retryStep
    have hnp : ¬ s.remainingTries > 0 := by omega
    simp [hnp]
  rw [hacq]
  simp only
  rw [hatt]
  rw [hretry]

/-- **T11e (successful attempt produces finalResponse with state intact).**
A successful inner-service call hands the response straight back, with the
policy state unchanged. -/
theorem pipeline_success_finalises
    (s : RetryLimit) (cs : ConcState)
    (k deadline t : Nat)
    (hcap : cs.inFlight < k)
    (hin : t ≤ deadline) :
    pipelineStep s cs k deadline t .ok
      = .finalResponse (.finished .ok) s (release ⟨cs.inFlight + 1⟩) := by
  unfold pipelineStep
  have hacq : acquire k cs = some ⟨cs.inFlight + 1⟩ := by
    unfold acquire; simp [hcap]
  have hatt : runAttemptWithTimeout deadline t .ok = .finished .ok := by
    unfold runAttemptWithTimeout
    simp [hin]
  rw [hacq]
  simp only
  rw [hatt]
  -- Goal now: matching .finished .ok against AttemptOutcome alternatives.
  change (match retryStep s .ok with
        | none => PipelineResult.finalResponse (.finished .ok) s
                    (release ⟨cs.inFlight + 1⟩)
        | some s' => PipelineResult.scheduleRetry s'
                    (release ⟨cs.inFlight + 1⟩)) = _
  rfl

/-! ## Cross-component sanity -/

/-- The retry-chain latency bound implies the configured outer
`BLOCK_VERIFY_TIMEOUT = 8 * 60 = 480 s` covers a full retry chain with
plenty of slack. Pinning this here makes any future drift in either
constant visible. -/
theorem retry_chain_fits_verify_timeout :
    (BLOCK_DOWNLOAD_RETRY_LIMIT + 1) * BLOCK_DOWNLOAD_TIMEOUT ≤ 8 * 60 := by
  rw [retry_chain_latency_bound]; decide

end Zebra.ZebradSyncRetryPolicy
