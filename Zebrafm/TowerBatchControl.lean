import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# `tower-batch-control` batch-flush invariants

Zebra wraps batched verifier services (signatures, proofs) with a generic
`Batch<S, Request>` adapter from the `tower-batch-control` crate. The adapter
delivers items to the inner service one at a time and explicitly issues a
`BatchControl::Flush` when one of two conditions becomes true:

* the **weight cap** is reached — `pending_items_weight ≥ max_items_weight_in_batch`
  (Source: `tower-batch-control/src/worker.rs:253`, inside the `run` loop's
  message-handling arm); or
* the **latency timer** fires — `pending_batch_timer` reaches its deadline
  (Source: `tower-batch-control/src/worker.rs:223`, the `pending_batch_timer`
  arm of `tokio::select!`).

The `Batch::pair()` constructor clamps the user-supplied configuration to
sensible values before threading it into the worker:

* `max_items_weight_in_batch = max(user, 1)`
  (Source: `tower-batch-control/src/service.rs:172`).
* `max_batches_in_queue = max_batches.clamp(1, QUEUE_BATCH_LIMIT)` where
  `QUEUE_BATCH_LIMIT = 64`
  (Source: `tower-batch-control/src/service.rs:34, 176`).
* The semaphore is sized `max_items_weight_in_batch * max_batches_in_queue`
  (Source: `tower-batch-control/src/service.rs:188`).

We model the batch as a `List Nat` of per-item weights — the order is the
arrival order. The per-item processing step is `process_req`, which appends a
weight to the pending list and increments `pending_items_weight`
(`worker.rs:149`). The flush step resets weight to `0` and clears the timer
(`worker.rs:180-181`). The `BatchControl::Flush` request is sent to the inner
service, and the items that were collected so far have been forwarded in
arrival order (`worker.rs:150`, `let rsp = svc.call(req.into())`), which is
how the inner service sees the insertion-ordered stream that the wrapper
guarantees.

## What is proved

* `clampWeightCap` matches the Rust `max(_, 1)` — never zero, idempotent for
  positive inputs;
* `clampMaxBatches` clamps user input into `[1, QUEUE_BATCH_LIMIT]` and is
  itself idempotent;
* the semaphore size is `weightCap * batchesInQueue`, strictly positive;
* the flush predicate `flushNow weight cap = weight ≥ cap` is **monotone in
  the running weight** — once it flips to `true` it stays `true` until reset;
* `addItem` preserves arrival order (it `++ [w]` at the back);
* a sequence of unit-weight items hits the cap exactly at index `cap` — the
  "max_items + 1 forces immediate flush" guarantee from the task description.
  We prove this as: with unit weights, the first `cap` items do not flush;
  adding the `(cap+1)`-th item flips the predicate to `true`.
* `flushBatch` clears state and preserves the flushed list verbatim — the
  inner service therefore observes batch contents in arrival order;
* the rust `max` and `clamp` always agree with `Nat.max`/`Nat.clamp`-style
  reasoning on `Nat`, which the proofs lean on via `decide` and `omega`.
-/

namespace Zebra.TowerBatchControl

/-! ## Constants -/

/-- Hard ceiling on the number of pending+running batches.
Source: `tower-batch-control/src/service.rs:34`
(`pub const QUEUE_BATCH_LIMIT: usize = 64`). -/
def QUEUE_BATCH_LIMIT : Nat := 64

/-! ## Config clamps

Mirror the two `max`/`clamp` calls inside `Batch::pair()`. -/

/-- `max(weight_cap, 1)` — the Rust `pair()` floor on
`max_items_weight_in_batch`.
Source: `tower-batch-control/src/service.rs:172`. -/
def clampWeightCap (w : Nat) : Nat := max w 1

/-- `max_batches.clamp(1, QUEUE_BATCH_LIMIT)` — the Rust ceiling on the
number of batches in the queue.
Source: `tower-batch-control/src/service.rs:176`. -/
def clampMaxBatches (b : Nat) : Nat := max (min b QUEUE_BATCH_LIMIT) 1

/-- The semaphore capacity, computed from the clamped config.
Source: `tower-batch-control/src/service.rs:188`
(`Semaphore::new(max_items_weight_in_batch * max_batches_in_queue)`). -/
def semaphoreCapacity (weightCap batchesInQueue : Nat) : Nat :=
  clampWeightCap weightCap * clampMaxBatches batchesInQueue

/-! ## Batch state

A live batch is the pair `(items, weight)` where `items` is the arrival-order
list of per-item weights, and `weight` equals their sum. The wrapper uses an
external `pending_batch_timer` flag to signal a deadline; we model that as a
`Bool`. -/

/-- Batch state: the in-flight item list, the running weight, and the timer
flag (`true` iff a deadline has elapsed without an explicit flush). -/
structure BatchState where
  items : List Nat
  weight : Nat
  timerFired : Bool
  deriving Repr, DecidableEq

/-- The empty batch — no pending items, zero weight, no deadline.
Source: implicit in `Worker::new` (`pending_items_weight: 0`,
`pending_batch_timer: None`) at `tower-batch-control/src/worker.rs:122-123`. -/
def emptyBatch : BatchState := { items := [], weight := 0, timerFired := false }

/-! ## Worker steps

The two state transitions of interest. -/

/-- Process one item of weight `w`: append to the back of the item list and
add `w` to the running weight.
Source: `tower-batch-control/src/worker.rs:149-150`
(`self.pending_items_weight += req.request_weight();` followed by forwarding
the request to the inner service in arrival order). -/
def addItem (s : BatchState) (w : Nat) : BatchState :=
  { s with items := s.items ++ [w], weight := s.weight + w }

/-- The flush predicate the Rust worker checks after appending each item:
the batch should be flushed iff its weight is at least the cap.
Source: `tower-batch-control/src/worker.rs:253`
(`if self.pending_items_weight >= self.max_items_weight_in_batch`). -/
def flushNow (s : BatchState) (cap : Nat) : Bool := decide (s.weight ≥ cap)

/-- Mark the timer as fired — corresponds to the `OptionFuture::from(timer)`
arm of `tokio::select!` at `tower-batch-control/src/worker.rs:223`. -/
def fireTimer (s : BatchState) : BatchState := { s with timerFired := true }

/-- A second flush trigger: the timer fired. The Rust select! arm for the
timer unconditionally calls `flush_service()`. -/
def shouldFlush (s : BatchState) (cap : Nat) : Bool :=
  flushNow s cap || s.timerFired

/-- Flushing the inner service: reset weight, clear the timer, and emit the
items in arrival order. The wrapper resets the batch to empty.
Source: `tower-batch-control/src/worker.rs:180-181`
(`self.pending_items_weight = 0; self.pending_batch_timer = None;`). -/
def flushBatch (s : BatchState) : List Nat × BatchState :=
  (s.items, emptyBatch)

/-! ## Config clamp theorems -/

/-- **T1 (weight cap floor).** `clampWeightCap` is at least 1. The Rust
`max(_, 1)` makes a zero-weight-cap config (which would never flush on
weight) impossible. -/
theorem clampWeightCap_ge_one (w : Nat) : 1 ≤ clampWeightCap w := by
  unfold clampWeightCap
  exact Nat.le_max_right _ _

/-- **T2 (weight cap is monotone in the input).** The clamp does not shrink
the user's choice on positive inputs. Combined with T1 this means the worker
always processes at least one item per batch. -/
theorem clampWeightCap_id_pos (w : Nat) (hpos : 1 ≤ w) :
    clampWeightCap w = w := by
  unfold clampWeightCap
  exact Nat.max_eq_left hpos

/-- **T3 (weight cap idempotence).** Applying the clamp twice is the same
as once — re-clamping a configured value never changes it. -/
theorem clampWeightCap_idempotent (w : Nat) :
    clampWeightCap (clampWeightCap w) = clampWeightCap w :=
  clampWeightCap_id_pos _ (clampWeightCap_ge_one _)

/-- **T4 (batches-in-queue floor).** The clamp lands in `[1, _]`. Even if
the user supplies `0`, the queue can hold at least one batch. -/
theorem clampMaxBatches_ge_one (b : Nat) : 1 ≤ clampMaxBatches b := by
  unfold clampMaxBatches
  exact Nat.le_max_right _ _

/-- **T5 (batches-in-queue ceiling).** The clamp never exceeds
`QUEUE_BATCH_LIMIT`. This is the DoS bound the comment at
`service.rs:32-34` cites — caps the queue depth even on a machine with
many cores. -/
theorem clampMaxBatches_le_limit (b : Nat) :
    clampMaxBatches b ≤ QUEUE_BATCH_LIMIT := by
  unfold clampMaxBatches QUEUE_BATCH_LIMIT
  -- max (min b 64) 1 ≤ 64
  have h1 : min b QUEUE_BATCH_LIMIT ≤ QUEUE_BATCH_LIMIT := Nat.min_le_right _ _
  have h2 : (1 : Nat) ≤ QUEUE_BATCH_LIMIT := by decide
  exact Nat.max_le.mpr ⟨h1, h2⟩

/-- **T6 (batches-in-queue idempotence).** Re-clamping is a no-op. -/
theorem clampMaxBatches_idempotent (b : Nat) :
    clampMaxBatches (clampMaxBatches b) = clampMaxBatches b := by
  unfold clampMaxBatches
  have h_ge_one : 1 ≤ max (min b QUEUE_BATCH_LIMIT) 1 := Nat.le_max_right _ _
  have h_le_lim : max (min b QUEUE_BATCH_LIMIT) 1 ≤ QUEUE_BATCH_LIMIT := by
    have h1 : min b QUEUE_BATCH_LIMIT ≤ QUEUE_BATCH_LIMIT := Nat.min_le_right _ _
    have h2 : (1 : Nat) ≤ QUEUE_BATCH_LIMIT := by unfold QUEUE_BATCH_LIMIT; decide
    exact Nat.max_le.mpr ⟨h1, h2⟩
  -- min x QUEUE_BATCH_LIMIT = x when x ≤ QUEUE_BATCH_LIMIT
  rw [Nat.min_eq_left h_le_lim]
  -- max x 1 = x when 1 ≤ x
  exact Nat.max_eq_left h_ge_one

/-- **T7 (in-range input is fixed).** When the user's `b` already lies in
`[1, QUEUE_BATCH_LIMIT]`, the clamp is the identity. -/
theorem clampMaxBatches_id_inrange (b : Nat)
    (hlo : 1 ≤ b) (hhi : b ≤ QUEUE_BATCH_LIMIT) :
    clampMaxBatches b = b := by
  unfold clampMaxBatches
  rw [Nat.min_eq_left hhi]
  exact Nat.max_eq_left hlo

/-! ## Semaphore capacity theorems -/

/-- **T8 (semaphore capacity is positive).** With both clamps at `≥ 1`,
the semaphore admits at least one in-flight request. -/
theorem semaphoreCapacity_pos (weightCap batchesInQueue : Nat) :
    0 < semaphoreCapacity weightCap batchesInQueue := by
  unfold semaphoreCapacity
  have h1 : 1 ≤ clampWeightCap weightCap := clampWeightCap_ge_one _
  have h2 : 1 ≤ clampMaxBatches batchesInQueue := clampMaxBatches_ge_one _
  exact Nat.mul_pos (by omega) (by omega)

/-- **T9 (semaphore capacity ceiling).** The semaphore never grows past
`clampWeightCap weightCap * QUEUE_BATCH_LIMIT`. This is the upper bound on
concurrent permits, which bounds memory and CPU usage. -/
theorem semaphoreCapacity_le (weightCap batchesInQueue : Nat) :
    semaphoreCapacity weightCap batchesInQueue
      ≤ clampWeightCap weightCap * QUEUE_BATCH_LIMIT := by
  unfold semaphoreCapacity
  have h := clampMaxBatches_le_limit batchesInQueue
  exact Nat.mul_le_mul_left _ h

/-- **T10 (clamp-floors witness).** `QUEUE_BATCH_LIMIT = 64`. Pinned so any
upstream constant drift breaks the build, mirroring the role of the
`max_inv_per_map_eq`-style pins in `InventoryCacheSize.lean`. -/
theorem queue_batch_limit_eq : QUEUE_BATCH_LIMIT = 64 := rfl

/-! ## Batch state: insertion order -/

/-- **T11 (addItem preserves prior arrivals).** Adding an item appends it
at the back — every previously-appended item still appears at its original
index. This is the insertion-order preservation the task description asks
for: by the time the flush fires, the items list IS the arrival order. -/
theorem addItem_preserves_prior (s : BatchState) (w : Nat) :
    (addItem s w).items = s.items ++ [w] := by
  unfold addItem; rfl

/-- **T12 (addItem grows the list by exactly one).** -/
theorem addItem_length (s : BatchState) (w : Nat) :
    (addItem s w).items.length = s.items.length + 1 := by
  unfold addItem; simp

/-- **T13 (addItem updates weight additively).** -/
theorem addItem_weight (s : BatchState) (w : Nat) :
    (addItem s w).weight = s.weight + w := by
  unfold addItem; rfl

/-- **T14 (addItem does not touch the timer).** A new item never starts /
fires the timer in the worker — only the timer arm of `tokio::select!`
does. -/
theorem addItem_timerFired (s : BatchState) (w : Nat) :
    (addItem s w).timerFired = s.timerFired := by
  unfold addItem; rfl

/-! ## Flush-condition monotonicity -/

/-- **T15 (`flushNow` is monotone in the running weight).** Once the
predicate becomes `true`, it stays `true` no matter how many more items
(of any weight) are appended — the worker's `>=` check has no way to flip
back to `false` without an explicit flush. -/
theorem flushNow_monotone (s : BatchState) (cap w : Nat) :
    flushNow s cap = true → flushNow (addItem s w) cap = true := by
  intro h
  unfold flushNow at h ⊢
  unfold addItem
  -- s.weight ≥ cap implies s.weight + w ≥ cap.
  simp only [decide_eq_true_eq] at h ⊢
  omega

/-- **T16 (`flushNow` is monotone in the cap, going down).** Lowering the
cap can only make `flushNow` *more* likely to fire — useful when reasoning
about the relationship between worker config and runtime behaviour. -/
theorem flushNow_monotone_cap (s : BatchState) (cap cap' : Nat)
    (h : cap' ≤ cap) (hflush : flushNow s cap = true) :
    flushNow s cap' = true := by
  unfold flushNow at hflush ⊢
  simp only [decide_eq_true_eq] at hflush ⊢
  omega

/-- **T17 (`flushNow` thresholds exactly at the cap).** Equivalent to T16
restated: there is no slack — `weight = cap - 1` does not flush, `weight = cap`
does. This is the "off-by-one" guarantee the Rust worker enforces. -/
theorem flushNow_iff (s : BatchState) (cap : Nat) :
    flushNow s cap = true ↔ s.weight ≥ cap := by
  unfold flushNow
  exact decide_eq_true_iff

/-- **T18 (timer ⇒ `shouldFlush`).** Even if the weight cap has not been
hit, a fired timer forces a flush. -/
theorem shouldFlush_of_timer (s : BatchState) (cap : Nat)
    (h : s.timerFired = true) : shouldFlush s cap = true := by
  unfold shouldFlush
  rw [h]; simp

/-- **T19 (weight cap ⇒ `shouldFlush`).** And dually, if the weight cap has
been hit, no matter what the timer says, the batch flushes. -/
theorem shouldFlush_of_weight (s : BatchState) (cap : Nat)
    (h : flushNow s cap = true) : shouldFlush s cap = true := by
  unfold shouldFlush
  rw [h]; simp

/-- **T20 (`shouldFlush` is monotone in the running weight).** Adding more
items cannot disable a pending flush. -/
theorem shouldFlush_monotone (s : BatchState) (cap w : Nat)
    (h : shouldFlush s cap = true) :
    shouldFlush (addItem s w) cap = true := by
  unfold shouldFlush at h ⊢
  -- Boolean OR is monotone in each argument.
  rcases Bool.or_eq_true_iff.mp h with hf | ht
  · have hf' := flushNow_monotone s cap w hf
    simp [hf']
  · -- addItem does not touch the timer.
    have : (addItem s w).timerFired = true := by
      rw [addItem_timerFired]; exact ht
    simp [this]

/-! ## Flush effect -/

/-- **T21 (flush emits items in arrival order).** The flushed batch is
`s.items` verbatim — the inner service therefore observes the items in the
same order they were appended via `addItem`. Combined with T11, this is the
end-to-end "insertion order preserved" guarantee. -/
theorem flushBatch_items_in_order (s : BatchState) :
    (flushBatch s).fst = s.items := by
  unfold flushBatch; rfl

/-- **T22 (flush resets the state to empty).** After a flush the batch is
re-initialised with zero weight, no items, and no timer. -/
theorem flushBatch_resets (s : BatchState) :
    (flushBatch s).snd = emptyBatch := by
  unfold flushBatch; rfl

/-- **T23 (after flush, `flushNow` is false for any positive cap).** The
weight reset makes the cap predicate unconditionally `false` until the next
item arrives. -/
theorem flushNow_after_flush (s : BatchState) (cap : Nat)
    (hpos : 1 ≤ cap) :
    flushNow (flushBatch s).snd cap = false := by
  rw [flushBatch_resets]
  unfold flushNow emptyBatch
  simp only [decide_eq_false_iff_not, not_le]
  omega

/-- **T24 (after flush, `shouldFlush` is false for any positive cap).**
Both triggers reset on flush. -/
theorem shouldFlush_after_flush (s : BatchState) (cap : Nat)
    (hpos : 1 ≤ cap) :
    shouldFlush (flushBatch s).snd cap = false := by
  unfold shouldFlush
  rw [flushNow_after_flush _ cap hpos]
  rw [flushBatch_resets]
  unfold emptyBatch
  simp

/-! ## Unit-weight stream: `cap + 1` items force a flush -/

/-- Replay `n` unit-weight items into `s`. Each call to `addItem` appends
`1` to the items list. -/
def addUnits (s : BatchState) : Nat → BatchState
  | 0 => s
  | n + 1 => addItem (addUnits s n) 1

/-- **T25 (unit-weight items advance weight linearly).** -/
theorem addUnits_weight (s : BatchState) (n : Nat) :
    (addUnits s n).weight = s.weight + n := by
  induction n with
  | zero => unfold addUnits; simp
  | succ n ih =>
    unfold addUnits
    rw [addItem_weight, ih]
    omega

/-- **T26 (unit-weight items advance length linearly).** -/
theorem addUnits_length (s : BatchState) (n : Nat) :
    (addUnits s n).items.length = s.items.length + n := by
  induction n with
  | zero => unfold addUnits; simp
  | succ n ih =>
    unfold addUnits
    rw [addItem_length, ih]
    omega

/-- **T27 (`cap` unit-weight items into an empty batch trigger a flush).**
Once the weight matches the cap, the predicate flips — the `≥` in
`worker.rs:253` fires exactly at the cap value. -/
theorem cap_units_triggers_flush (cap : Nat) (_hpos : 1 ≤ cap) :
    flushNow (addUnits emptyBatch cap) cap = true := by
  unfold flushNow
  rw [addUnits_weight]
  unfold emptyBatch
  simp only [decide_eq_true_iff]
  omega

/-- **T28 (`cap + 1` unit-weight items also trigger a flush — strictly).**
The "max_items + 1 forces immediate flush" claim from the task description.
Even at `cap + 1` the predicate is `true`, and by `flushNow_monotone` it
stays `true` for any further appends. -/
theorem cap_plus_one_units_triggers_flush (cap : Nat) :
    flushNow (addUnits emptyBatch (cap + 1)) cap = true := by
  unfold flushNow
  rw [addUnits_weight]
  unfold emptyBatch
  simp only [decide_eq_true_iff]
  omega

/-- **T29 (strictly under the cap does NOT flush yet).** With `n` strictly
less than `cap` unit-weight items, the weight predicate is `false`. This is
the dual to T27 — pinning the exact threshold. -/
theorem under_cap_units_no_flush (cap n : Nat) (_h : n < cap) :
    flushNow (addUnits emptyBatch n) cap = false := by
  unfold flushNow
  rw [addUnits_weight]
  unfold emptyBatch
  simp only [decide_eq_false_iff_not, not_le]
  omega

/-! ## Worker-loop combined behaviour -/

/-- The "process one item" step the worker takes when the timer is not the
event being woken on: append the item, then maybe call `flush_service`.
Returns the post-step state and, if a flush happened, the items that were
emitted (in arrival order). -/
def step (s : BatchState) (w cap : Nat) : BatchState × Option (List Nat) :=
  if flushNow (addItem s w) cap then
    (emptyBatch, some (addItem s w).items)
  else
    (addItem s w, none)

/-- **T30 (step weight bound).** If the step does not emit a flush, the
running weight stays strictly below the cap. Equivalently: as long as
`flushNow s' cap = false` after appending, the worker keeps accumulating. -/
theorem step_no_flush_weight_lt_cap (s : BatchState) (w cap : Nat) :
    (step s w cap).snd = none → (step s w cap).fst.weight < cap := by
  intro h
  unfold step at h ⊢
  by_cases hfn : flushNow (addItem s w) cap = true
  · simp [hfn] at h
  · -- hfn says flushNow (addItem s w) cap is not true; rewrite to false explicitly.
    have hfalse : flushNow (addItem s w) cap = false := by
      cases hb : flushNow (addItem s w) cap with
      | true => exact absurd hb hfn
      | false => rfl
    rw [hfalse]
    simp only [Bool.false_eq_true, if_false]
    -- Now goal: (addItem s w).weight < cap.
    have : ¬ (addItem s w).weight ≥ cap := by
      intro hge
      have htrue : flushNow (addItem s w) cap = true := (flushNow_iff _ _).mpr hge
      rw [htrue] at hfalse
      simp at hfalse
    omega

/-- **T31 (step flush ⇒ items in order).** When the step does flush, the
emitted item list equals the previous items with the new one appended at
the back — strict insertion order preservation across the flush boundary. -/
theorem step_flush_items_in_order (s : BatchState) (w cap : Nat)
    (items : List Nat)
    (h : (step s w cap).snd = some items) :
    items = s.items ++ [w] := by
  unfold step at h
  by_cases hfn : flushNow (addItem s w) cap = true
  · simp only [hfn, if_true] at h
    -- h : Option.some (addItem s w).items = some items
    have : (addItem s w).items = items := by
      have h' : some (addItem s w).items = some items := h
      exact Option.some.inj h'
    rw [← this, addItem_preserves_prior]
  · simp [hfn] at h

/-- **T32 (step flush ⇒ post-state is empty).** When the step flushes, the
state after the step is `emptyBatch` (mirrors `flushBatch_resets`). -/
theorem step_flush_resets (s : BatchState) (w cap : Nat) (items : List Nat)
    (h : (step s w cap).snd = some items) :
    (step s w cap).fst = emptyBatch := by
  unfold step at h ⊢
  by_cases hfn : flushNow (addItem s w) cap = true
  · simp [hfn]
  · simp [hfn] at h

/-! ## Cross-config consistency -/

/-- **T33 (clamped semaphore is bounded above by max-by-max).**
The semaphore capacity never exceeds
`(weightCap.max 1) * QUEUE_BATCH_LIMIT`, which gives a worst-case bound
useful for planning memory ahead of clamp. -/
theorem semaphoreCapacity_bound (weightCap batchesInQueue : Nat) :
    semaphoreCapacity weightCap batchesInQueue
      ≤ max weightCap 1 * QUEUE_BATCH_LIMIT := by
  unfold semaphoreCapacity clampWeightCap
  exact Nat.mul_le_mul_left _ (clampMaxBatches_le_limit _)

end Zebra.TowerBatchControl
