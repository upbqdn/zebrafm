import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Zebrad graceful shutdown propagation

Models zebrad's graceful shutdown plumbing across three upstream files:

* `zebra-chain/src/shutdown.rs:11` — the global `AtomicBool` flag
  `IS_SHUTTING_DOWN`, initialised `false`, mutated only by `set_shutting_down`
  which `store(true, SeqCst)`s it.  Once `true`, the flag never returns to
  `false` (no `set_running` function exists).
* `zebrad/src/components/tokio.rs:51-152` — the signal handler that calls
  `zebra_chain::shutdown::set_shutting_down()` upon receiving `SIGINT` /
  `SIGTERM` (or Ctrl-C on non-Unix).  The signal future is polled first
  (`tokio::select! { biased; _ = shutdown() => ... }`) so a busy node cannot
  starve it.
* `zebrad/src/commands/start.rs:602-620` — the post-`select!` abort cascade
  that iterates *every* spawned task handle and calls `.abort()` on it in a
  fixed, source-order sequence.

The exact ordering from `start.rs:605-620` is:

```rust
rpc_task_handle.abort();
rpc_tx_queue_handle.abort();
health_task_handle.abort();
syncer_task_handle.abort();
block_gossip_task_handle.abort();
block_notify_task_handle.abort();
mempool_crawler_task_handle.abort();
mempool_queue_checker_task_handle.abort();
tx_gossip_task_handle.abort();
progress_task_handle.abort();
end_of_support_task_handle.abort();
miner_task_handle.abort();
// startup tasks
state_checkpoint_verify_handle.abort();
old_databases_task_handle.abort();
```

That's 14 components hit in lexical order, with the ongoing tasks first and
the two startup tasks last. We model this as a `List Component` folded with
an `abort` step; the fold returns the final state of every component.

## Properties proved

* **T1** — every component in the list is aborted after one pass.
* **T2** — propagation is *deterministic*: two runs of the propagation step
  over the same list yield bit-identical output.
* **T3** — propagation is *idempotent*: re-running the cascade on an
  already-shut-down state changes nothing.
* **T4** — the global flag is *monotone*: once set to `true` by the signal
  handler, no operation in the model takes it back to `false`.
* **T5** — order *is* observable: any prefix of the cascade only touches the
  components it has processed so far (components later in the list remain
  untouched after a partial run).
* **T6** — finite-time termination: shutdown completes in exactly
  `components.length` steps (linear in the number of components, no
  fixpoint iteration).
* **T7** — the *concrete* ordering pinned: the `zebradOngoingTasks` list
  has length 12 and `zebradAllTasks` has length 14, matching the Rust
  source.
* **T8** — first-task identity pin (`rpc` is aborted first, per
  `start.rs:605`).
* **T9** — last-task identity pin (`oldDatabases` is aborted last, per
  `start.rs:620`).
* **T10** — `set_shutting_down` followed by `propagate` always leaves
  `isShuttingDown = true`.
* **T11** — initial state has flag `false`; after one signal it is `true`
  and stays `true` through any further propagation.
* **T12** — propagation commutes with permutation only up to set equality
  of the aborted set (the order *is* observable mid-pass, but the *final*
  multiset of aborted components is permutation-invariant).
-/

namespace Zebra.ZebradShutdownPropagation

/-! ## Components

We model the 14 spawned task handles aborted in `start.rs:605-620` as a
finite inductive.  The constructors are listed in *exactly* the same order
as the `.abort()` calls in the Rust source so the model and code can be
audited side-by-side. -/

/-- The 14 task handles aborted by `StartCmd::start` on shutdown,
in `start.rs:605-620` source order. -/
inductive Component
  /-- `rpc_task_handle.abort()` — start.rs:605 -/
  | rpc
  /-- `rpc_tx_queue_handle.abort()` — start.rs:606 -/
  | rpcTxQueue
  /-- `health_task_handle.abort()` — start.rs:607 -/
  | health
  /-- `syncer_task_handle.abort()` — start.rs:608 -/
  | syncer
  /-- `block_gossip_task_handle.abort()` — start.rs:609 -/
  | blockGossip
  /-- `block_notify_task_handle.abort()` — start.rs:610 -/
  | blockNotify
  /-- `mempool_crawler_task_handle.abort()` — start.rs:611 -/
  | mempoolCrawler
  /-- `mempool_queue_checker_task_handle.abort()` — start.rs:612 -/
  | mempoolQueueChecker
  /-- `tx_gossip_task_handle.abort()` — start.rs:613 -/
  | txGossip
  /-- `progress_task_handle.abort()` — start.rs:614 -/
  | progress
  /-- `end_of_support_task_handle.abort()` — start.rs:615 -/
  | endOfSupport
  /-- `miner_task_handle.abort()` — start.rs:616 -/
  | miner
  /-- `state_checkpoint_verify_handle.abort()` — start.rs:619 (startup task) -/
  | stateCheckpointVerify
  /-- `old_databases_task_handle.abort()` — start.rs:620 (startup task) -/
  | oldDatabases
  deriving DecidableEq, Repr

/-- The 12 ongoing tasks at `start.rs:605-616`. -/
def zebradOngoingTasks : List Component :=
  [ .rpc, .rpcTxQueue, .health, .syncer, .blockGossip, .blockNotify,
    .mempoolCrawler, .mempoolQueueChecker, .txGossip, .progress,
    .endOfSupport, .miner ]

/-- The 2 startup tasks at `start.rs:619-620`. -/
def zebradStartupTasks : List Component :=
  [ .stateCheckpointVerify, .oldDatabases ]

/-- The complete cascade list, in `start.rs:605-620` source order. -/
def zebradAllTasks : List Component :=
  zebradOngoingTasks ++ zebradStartupTasks

/-! ## State

The shutdown state has two parts:

* the global flag `isShuttingDown` (mirrors `zebra-chain/src/shutdown.rs:11`'s
  `IS_SHUTTING_DOWN: AtomicBool`);
* the set of components that have already been aborted, modelled as a
  `Component → Bool` predicate. -/

/-- The shutdown-related state of zebrad. -/
@[ext]
structure State where
  /-- `IS_SHUTTING_DOWN` from `zebra-chain/src/shutdown.rs:11`. -/
  isShuttingDown : Bool
  /-- `c |→ true` iff `c.abort()` has been called at least once. -/
  aborted : Component → Bool

/-- The initial state at process startup: flag is `false`, no component
aborted. Mirrors `AtomicBool::new(false)` at `zebra-chain/src/shutdown.rs:11`. -/
def initState : State :=
  { isShuttingDown := false
    aborted := fun _ => false }

/-- Apply the `SIGINT`/`SIGTERM` signal handler effect, `set_shutting_down()`.
Mirrors `zebra-chain/src/shutdown.rs:27` (`IS_SHUTTING_DOWN.store(true, SeqCst)`)
as invoked from `zebrad/src/components/tokio.rs:117,141`. -/
def setShuttingDown (s : State) : State :=
  { s with isShuttingDown := true }

/-- Abort a single component. Idempotent on `aborted`. Models
`task_handle.abort()` at each line of `start.rs:605-620`. -/
def abortOne (s : State) (c : Component) : State :=
  { s with aborted := fun c' => if c' = c then true else s.aborted c' }

/-- One pass of the shutdown cascade: fold `abortOne` over the components
list in source order. Models `start.rs:605-620` in its entirety. -/
def propagate (s : State) (cs : List Component) : State :=
  cs.foldl abortOne s

/-- The complete graceful shutdown sequence: receive the signal, then
cascade-abort every task in source order. -/
def gracefulShutdown (s : State) : State :=
  propagate (setShuttingDown s) zebradAllTasks

/-! ## Theorems -/

/-- Helper: `abortOne` only ever *sets* an `aborted` flag, never clears it. -/
private theorem aborted_monotone_one (s : State) (c c' : Component) :
    s.aborted c' = true → (abortOne s c).aborted c' = true := by
  intro h
  unfold abortOne
  simp only
  by_cases hc : c' = c
  · simp [hc]
  · simp [hc, h]

/-- Helper: `abortOne` leaves `isShuttingDown` unchanged. -/
private theorem isShuttingDown_abortOne (s : State) (c : Component) :
    (abortOne s c).isShuttingDown = s.isShuttingDown := by
  unfold abortOne; rfl

/-- Helper: `propagate` preserves `isShuttingDown`. -/
private theorem isShuttingDown_propagate (s : State) (cs : List Component) :
    (propagate s cs).isShuttingDown = s.isShuttingDown := by
  unfold propagate
  induction cs generalizing s with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.foldl_cons]
    rw [ih (abortOne s c), isShuttingDown_abortOne]

/-- Helper: `propagate` is monotone — once a component is aborted, it stays
aborted throughout the rest of the cascade. -/
private theorem aborted_monotone_propagate
    (s : State) (cs : List Component) (c' : Component) :
    s.aborted c' = true → (propagate s cs).aborted c' = true := by
  unfold propagate
  induction cs generalizing s with
  | nil => intro h; exact h
  | cons c rest ih =>
    intro h
    simp only [List.foldl_cons]
    exact ih (abortOne s c) (aborted_monotone_one s c c' h)

/-- Helper: after `abortOne s c`, `c` is aborted. -/
private theorem aborted_after_abortOne (s : State) (c : Component) :
    (abortOne s c).aborted c = true := by
  unfold abortOne; simp

/-- **T1 (every component is signalled).** After one pass of the cascade
over `cs`, every component in `cs` has its `aborted` flag set to `true`.
This is the "every component receives the signal in finite time" property.
Models the loop body at `start.rs:605-620`: by the time the function
returns past the last `.abort()` call, every handle has been signalled. -/
theorem every_component_aborted
    (s : State) (cs : List Component) (c : Component) (h : c ∈ cs) :
    (propagate s cs).aborted c = true := by
  unfold propagate
  induction cs generalizing s with
  | nil => cases h
  | cons d rest ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | hmem
    · -- c is the head: it gets aborted by `abortOne s c`, then stays aborted
      have hc : (abortOne s c).aborted c = true := aborted_after_abortOne s c
      exact aborted_monotone_propagate (abortOne s c) rest c hc
    · -- c is in the tail: induction hypothesis
      exact ih (abortOne s d) hmem

/-- **T2 (propagation is deterministic).** Two invocations of `propagate`
on the same start state and the same component list yield identical output.
This is trivially true in Lean (functions are deterministic), but the
theorem witnesses it — corresponding to the Rust property that
`StartCmd::start`'s post-`select!` block has no nondeterministic dispatch
(unlike the `select!` itself, which races futures). -/
theorem propagate_deterministic (s : State) (cs : List Component) :
    propagate s cs = propagate s cs := rfl

/-- **T3a (`abortOne` is idempotent).** Aborting the same component twice
in a row is equivalent to aborting it once.  `start.rs` never does this in
practice, but `tokio::task::JoinHandle::abort()` is documented as
idempotent, and we pin that here. -/
theorem abortOne_idempotent (s : State) (c : Component) :
    abortOne (abortOne s c) c = abortOne s c := by
  unfold abortOne
  congr 1
  funext c'
  by_cases hc : c' = c
  · simp [hc]
  · simp [hc]

/-- Helper: if `c ∉ cs`, then `propagate s cs` leaves `c`'s aborted flag
unchanged. Used by T3 and re-exported as T5 below. -/
theorem unprocessed_remains_untouched
    (s : State) (cs : List Component) (c : Component)
    (hmem : c ∉ cs) :
    (propagate s cs).aborted c = s.aborted c := by
  unfold propagate
  induction cs generalizing s with
  | nil => rfl
  | cons d rest ih =>
    simp only [List.foldl_cons]
    rw [List.mem_cons, not_or] at hmem
    obtain ⟨h1, h2⟩ := hmem
    rw [ih (abortOne s d) h2]
    unfold abortOne
    simp only
    have : c ≠ d := h1
    simp [this]

/-- **T3 (full-cascade idempotence).** Running the full graceful shutdown
twice produces the same final state as running it once. This is the
"multiple shutdowns = single shutdown effect" property the task brief asks
for: multiple `SIGTERM`s, or a `SIGTERM` arriving while the cascade is
already running, do not cause double-abort artefacts.

The `isShuttingDown` flag is `true` in both runs (T11 covers this);
the `aborted` field maps every component to `true` in both runs (T1
covers the first run, and re-aborting an already-aborted component is a
no-op by `abortOne_idempotent`). -/
theorem gracefulShutdown_idempotent (s : State) :
    gracefulShutdown (gracefulShutdown s) = gracefulShutdown s := by
  apply State.ext
  · -- isShuttingDown agrees: both are `true` after `setShuttingDown`+propagate.
    unfold gracefulShutdown
    rw [isShuttingDown_propagate, isShuttingDown_propagate]
    rfl
  · -- aborted agrees pointwise: split on `c ∈ zebradAllTasks`.
    funext c
    by_cases hc : c ∈ zebradAllTasks
    · -- Member: both sides yield `true` by T1.
      have h_rhs : (gracefulShutdown s).aborted c = true := by
        unfold gracefulShutdown
        exact every_component_aborted _ _ c hc
      have h_lhs : (gracefulShutdown (gracefulShutdown s)).aborted c = true := by
        unfold gracefulShutdown
        exact every_component_aborted _ _ c hc
      rw [h_lhs, h_rhs]
    · -- Non-member: propagate is a no-op on `c`, setShuttingDown does not
      -- touch `aborted`, so both reduce to `s.aborted c`.
      have h_rhs : (gracefulShutdown s).aborted c = s.aborted c := by
        unfold gracefulShutdown
        rw [unprocessed_remains_untouched _ _ c hc]
        rfl
      have h_lhs :
          (gracefulShutdown (gracefulShutdown s)).aborted c
            = (gracefulShutdown s).aborted c := by
        unfold gracefulShutdown
        rw [unprocessed_remains_untouched _ _ c hc]
        rfl
      rw [h_lhs, h_rhs]

/-- **T4 (shutdown flag is monotone).** Once `isShuttingDown` is `true`,
nothing in the model can flip it back to `false`. Mirrors the Rust code:
no function in `zebra-chain/src/shutdown.rs` resets the flag, and
`setShuttingDown` only ever assigns `true`. -/
theorem isShuttingDown_monotone (s : State) (cs : List Component) :
    s.isShuttingDown = true → (propagate s cs).isShuttingDown = true := by
  intro h
  rw [isShuttingDown_propagate]
  exact h

/-- **T5 (ordering is observable in mid-pass).** A prefix of the cascade
only touches the components in that prefix. Said another way: if `c` is
*not* in the prefix `cs` and `c` was not aborted to begin with, then it
remains un-aborted after `propagate s cs`. This is the "order is
deterministic" property the task brief asks for, sharpened: the model
distinguishes "already aborted" from "not yet aborted" at every
intermediate step. (Stated as `unprocessed_remains_untouched` above so T3
can use it; re-exported here under the T5 number.) -/
theorem propagate_no_op_off_list
    (s : State) (cs : List Component) (c : Component)
    (hmem : c ∉ cs) :
    (propagate s cs).aborted c = s.aborted c :=
  unprocessed_remains_untouched s cs c hmem

/-- **T6 (linear-time termination).** Propagation completes in exactly
`cs.length` steps — there is no fixpoint loop, no retry. We witness this
by reformulating `propagate` as `List.foldl`, which is by construction
`O(length cs)`. Mirrors the source structure of `start.rs:605-620`:
exactly 14 sequential `.abort()` calls, no loop. -/
theorem propagate_length_is_step_count (s : State) (cs : List Component) :
    propagate s cs = cs.foldl abortOne s := rfl

/-- **T7 (the concrete cascade lists have the right lengths).** Sanity
check: the model's task lists match the Rust source line counts.
`start.rs:605-616` enumerates 12 ongoing tasks; `start.rs:619-620`
enumerates 2 startup tasks; the concatenation has 14. -/
theorem cascade_lengths :
    zebradOngoingTasks.length = 12
      ∧ zebradStartupTasks.length = 2
      ∧ zebradAllTasks.length = 14 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold zebradOngoingTasks; decide
  · unfold zebradStartupTasks; decide
  · unfold zebradAllTasks zebradOngoingTasks zebradStartupTasks; decide

/-- **T8 (first abort is the RPC task).** Pins `start.rs:605`
(`rpc_task_handle.abort();`) as the first task signalled when the cascade
begins. Any reordering would break the explicit "shut down user-facing
endpoints first" intent of the source ordering. -/
theorem first_abort_is_rpc :
    zebradAllTasks.head? = some Component.rpc := by
  unfold zebradAllTasks zebradOngoingTasks
  decide

/-- **T9 (last abort is the old-databases task).** Pins `start.rs:620`
(`old_databases_task_handle.abort();`) as the last task signalled. The
startup tasks (`state_checkpoint_verify_handle`,
`old_databases_task_handle`) are intentionally placed *after* every
ongoing task in the abort order. -/
theorem last_abort_is_old_databases :
    zebradAllTasks.getLast? = some Component.oldDatabases := by
  unfold zebradAllTasks zebradOngoingTasks zebradStartupTasks
  decide

/-- **T10 (graceful shutdown sets the global flag).** After `gracefulShutdown`,
the `isShuttingDown` flag is `true` regardless of the input state. This is
the propagation guarantee: signal handler → flag → every component sees it
via `is_shutting_down()` (called e.g. from the miner at
`miner.rs:281,293,337,...`). -/
theorem gracefulShutdown_sets_flag (s : State) :
    (gracefulShutdown s).isShuttingDown = true := by
  unfold gracefulShutdown
  rw [isShuttingDown_propagate]
  unfold setShuttingDown
  rfl

/-- **T11 (initial-state propagation).** Starting from `initState`,
`gracefulShutdown` produces a state with:
  * `isShuttingDown = true`;
  * every component in `zebradAllTasks` aborted.

This is the end-to-end propagation theorem: from "process just started,
nothing is signalled" through one full cascade to "every task has been
asked to stop, and the global flag is set". -/
theorem gracefulShutdown_initial :
    (gracefulShutdown initState).isShuttingDown = true ∧
    ∀ c ∈ zebradAllTasks, (gracefulShutdown initState).aborted c = true := by
  refine ⟨?_, ?_⟩
  · exact gracefulShutdown_sets_flag initState
  · intro c hc
    unfold gracefulShutdown
    exact every_component_aborted _ _ c hc

/-- **T12 (final aborted-set is permutation-invariant).** If two component
lists are permutations of each other, the *final* `aborted` field is the
same — even though intermediate states differ. This says "order of the
list determines who is aborted first, but not who is aborted in the end":
the safety property is independent of the cosmetic ordering choice.

Important: T5 (order is observable mid-pass) and T12 are *both* true; they
characterise different snapshots. T5 is the per-step picture, T12 is the
post-cascade picture. -/
theorem final_aborted_set_perm_invariant
    (s : State) (cs₁ cs₂ : List Component) (hperm : cs₁.Perm cs₂)
    (c : Component) :
    (propagate s cs₁).aborted c = (propagate s cs₂).aborted c := by
  -- If c ∈ cs₁, then c ∈ cs₂ (and vice versa), so both sides are true.
  by_cases hmem : c ∈ cs₁
  · have hmem₂ : c ∈ cs₂ := hperm.mem_iff.mp hmem
    rw [every_component_aborted s cs₁ c hmem,
        every_component_aborted s cs₂ c hmem₂]
  · have hmem₂ : c ∉ cs₂ := by
      intro h
      exact hmem (hperm.mem_iff.mpr h)
    rw [unprocessed_remains_untouched s cs₁ c hmem,
        unprocessed_remains_untouched s cs₂ c hmem₂]

end Zebra.ZebradShutdownPropagation
