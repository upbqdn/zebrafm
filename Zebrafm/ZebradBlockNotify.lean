import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-!
# Zebrad block-notify task

Models the `-blocknotify` port at `zebrad/src/components/notify.rs` (PR #10726).
On each best-chain-tip change, the task runs an operator-supplied shell command,
with every `%s` substituted by the new tip's block hash in `getbestblockhash`
hex format. Three invariants matter for an operator who wires the notify
command into other infrastructure:

1. **IBD gating.** The command is run only once the node is "close to the
   network tip" — `sync_status.wait_until_close_to_tip().await` is awaited
   between observing the tip change and spawning the process
   (`notify.rs:92-95`). A node still in initial block download therefore never
   fires the callback, even if its best tip changes (this is zcashd's
   `-blocknotify` semantics).
2. **Exact `%s` substitution.** Every `%s` in the command is replaced with
   `block::Hash`'s `Display`, which is the same as `getbestblockhash`
   (`notify.rs:172-174`). That output is a *fixed* 64-char lowercase
   `[0-9a-f]` string, so the substituted value contains no shell
   metacharacters.
3. **Non-zero exit does not block validation.** A failed command is logged
   and reaped on a detached `tokio::spawn` task; the main `run_block_notify`
   loop returns immediately to await the next tip change
   (`notify.rs:146-165`).

We model the task at a level that captures these three guarantees without
modelling tokio, shells, or process trees.

## Model

* A *block hash* is a 32-byte sequence (`List Nat` of length 32, each `< 256`).
* The hex *display* is a `List Char` of length `2 * 32 = 64`, each character
  a lowercase hex digit.
* A *command template* is a `List Char`.
* `replaceAllPs` is the function that substitutes every contiguous `['%', 's']`
  with a replacement, mirroring Rust's `str::replace("%s", &hash.to_string())`.
* `tryNotify` is the IBD gate: it returns `some rendered` iff the node is
  close to the tip, otherwise `none`.
* A *spawn-and-reap* lifecycle has three states (`pending`, `succeeded`,
  `failed`); the *main loop state* (`MainLoopState`) advances independently.
  The "main loop never blocks on a child" property is the theorem that
  `worldStep`'s effect on `MainLoopState` is the same regardless of child
  state.

## Theorems proved

* **T1 (IBD gate suppresses).** `closeToTip = false` ⇒ `tryNotify` returns
  `none`. Models `notify.rs:92-95` blocking the spawn during IBD.
* **T2 (IBD gate passes once close).** `closeToTip = true` ⇒ `tryNotify`
  returns `some (render cmd h)`.
* **T3 (gating iff).** `tryNotify`'s `isSome` is exactly `closeToTip`.
* **T4 (no placeholders ⇒ identity).** A command containing no `%s`
  literal is left exactly unchanged by `render`. Pins `notify.rs/tests.rs:36`
  (`render_command("echo hello", h) = "echo hello"`).
* **T5 (one placeholder concrete case).** Pins
  `render_command("a %s b", h) = "a <hex> b"` on a concrete short template.
* **T6 (two placeholders ⇒ each becomes the same hash).** Pins
  `render_command("%s%s", h) = "<hex><hex>"`. Two distinct `%s`s, same
  display substituted into both.
* **T7 (substitution length).** The rendered command's length is exactly
  `cmd.length + countPs cmd * (DISPLAY_LEN - PS_LEN)`. The rendered size
  is purely a function of the template — no attacker-controlled input can
  affect it.
* **T8 (display length is exactly 64).** For any 32-byte block hash, the
  hex display is exactly 64 characters. Pins `notify.rs/tests.rs:49`.
* **T9 (display is hex).** Every character of the display is a lowercase
  hex digit. Pins `notify.rs/tests.rs:50-52`.
* **T10 (display contains no shell metacharacters).** Strengthens T9 to the
  specific shell-injection invariant: no `$`, `` ` ``, `\`, `;`, `|`, `&`,
  `<`, `>`, `(`, `)`, `'`, `"`, space, or newline ever appears. Safety
  promise behind the Rust comment "no shell metacharacters" at
  `notify.rs:171`.
* **T11 (failure does not block main loop).** Regardless of what the child
  transitions to, the main loop advances by exactly one iteration per
  `worldStep`. Formal version of "non-zero exit does not block validation"
  at `notify.rs:146-165`.
* **T12 (full pipeline characterisation).** One iteration of the notify
  loop outputs `none` iff IBD is active, otherwise `some (render cmd h)`.
* **T13 (default Config disables notify).** The default configuration sets
  `block_notify_command = None`. Pins `notify.rs:42-48` and the test at
  `notify.rs/tests.rs:56-58`.
-/

namespace Zebra.ZebradBlockNotify

/-! ## Hash bytes and display -/

/-- The number of bytes in a Zcash block hash. -/
def HASH_BYTES : Nat := 32

/-- A block hash: a `List Nat` of length 32, each byte `< 256`. -/
structure BlockHash where
  bytes : List Nat
  length_eq : bytes.length = HASH_BYTES
  bytes_valid : ∀ b ∈ bytes, b < 256

/-- Lowercase hex digit for a nibble in `[0, 16)`. -/
def hexDigit (n : Nat) : Char :=
  if n = 0 then '0'
  else if n = 1 then '1'
  else if n = 2 then '2'
  else if n = 3 then '3'
  else if n = 4 then '4'
  else if n = 5 then '5'
  else if n = 6 then '6'
  else if n = 7 then '7'
  else if n = 8 then '8'
  else if n = 9 then '9'
  else if n = 10 then 'a'
  else if n = 11 then 'b'
  else if n = 12 then 'c'
  else if n = 13 then 'd'
  else if n = 14 then 'e'
  else 'f'

/-- The two hex chars (high then low nibble) for a byte. -/
def byteHex (b : Nat) : List Char :=
  [hexDigit (b / 16), hexDigit (b % 16)]

/-- The full hex display of a list of bytes — concatenation of each
byte's `byteHex` in order. -/
def bytesHex (bs : List Nat) : List Char :=
  bs.foldr (fun b acc => byteHex b ++ acc) []

/-- The hex display of a `BlockHash`. -/
def display (h : BlockHash) : List Char := bytesHex h.bytes

/-! ## Hex-digit characterisation -/

/-- A character is a lowercase hex digit iff it is one of `'0'..'9'` or
`'a'..'f'`. -/
def isLowercaseHex (c : Char) : Bool :=
  c = '0' ∨ c = '1' ∨ c = '2' ∨ c = '3' ∨ c = '4' ∨ c = '5'
    ∨ c = '6' ∨ c = '7' ∨ c = '8' ∨ c = '9'
    ∨ c = 'a' ∨ c = 'b' ∨ c = 'c' ∨ c = 'd' ∨ c = 'e' ∨ c = 'f'

theorem hexDigit_isLowercaseHex (n : Nat) (h : n < 16) :
    isLowercaseHex (hexDigit n) = true := by
  interval_cases n <;> (unfold hexDigit isLowercaseHex; decide)

/-! ## byteHex properties -/

theorem byteHex_length (b : Nat) : (byteHex b).length = 2 := by
  unfold byteHex
  rfl

/-- Each char of `byteHex b` is a lowercase hex digit, provided `b < 256`. -/
theorem byteHex_chars_hex (b : Nat) (hb : b < 256) (c : Char)
    (hc : c ∈ byteHex b) : isLowercaseHex c = true := by
  unfold byteHex at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  have h_hi : b / 16 < 16 := by omega
  have h_lo : b % 16 < 16 := Nat.mod_lt b (by decide)
  rcases hc with hc | hc
  · rw [hc]; exact hexDigit_isLowercaseHex _ h_hi
  · rw [hc]; exact hexDigit_isLowercaseHex _ h_lo

/-! ## bytesHex length and chars -/

theorem bytesHex_length (bs : List Nat) :
    (bytesHex bs).length = 2 * bs.length := by
  unfold bytesHex
  induction bs with
  | nil => simp
  | cons b rest ih =>
    simp only [List.foldr_cons, List.length_append, List.length_cons]
    rw [byteHex_length, ih]
    omega

theorem bytesHex_chars_hex (bs : List Nat)
    (hbs : ∀ b ∈ bs, b < 256) (c : Char) (hc : c ∈ bytesHex bs) :
    isLowercaseHex c = true := by
  unfold bytesHex at hc
  induction bs with
  | nil => simp at hc
  | cons b rest ih =>
    simp only [List.foldr_cons, List.mem_append] at hc
    rcases hc with hc | hc
    · exact byteHex_chars_hex b (hbs b List.mem_cons_self) c hc
    · exact ih (fun b' hb' => hbs b' (List.mem_cons_of_mem b hb')) hc

/-! ## `%s` substitution

We implement `replaceAllPs` and `countPs` with explicit recursion on the
character pair `(head, second-head)`. The auto-generated equations reduce
by `rfl` so case-analysis is simple. -/

/-- Replace every contiguous `['%', 's']` in `cmd` with `repl`.
Mirrors Rust's `cmd.replace("%s", &hash.to_string())`. -/
def replaceAllPs (repl : List Char) : List Char → List Char
  | [] => []
  | c :: [] => [c]
  | c :: d :: rest =>
      if c = '%' ∧ d = 's' then repl ++ replaceAllPs repl rest
      else c :: replaceAllPs repl (d :: rest)

/-- Rendering a command: the function the Rust `render_command` implements. -/
def render (cmd : List Char) (h : BlockHash) : List Char :=
  replaceAllPs (display h) cmd

/-- Number of `%s` placeholders in `cmd` (non-overlapping, left-to-right —
matching Rust's `str::replace`). -/
def countPs : List Char → Nat
  | [] => 0
  | _ :: [] => 0
  | c :: d :: rest =>
      if c = '%' ∧ d = 's' then 1 + countPs rest
      else countPs (d :: rest)

/-! ## IBD gate -/

/-- The IBD gate. Models `SyncStatus::wait_until_close_to_tip` as a flag:
`true` ⇒ we are close to the network tip, `false` ⇒ still in IBD. -/
def tryNotify (closeToTip : Bool) (cmd : List Char) (h : BlockHash) :
    Option (List Char) :=
  if closeToTip then some (render cmd h) else none

/-! ## Child lifecycle -/

/-- The spawn-and-reap lifecycle of a notify child. Mirrors the three
observable outcomes in `notify.rs:148-162`: success, non-zero exit, or
spawn error. The `failed` case folds together the two error branches because
they have the same effect on the main loop (a `warn!` log line). -/
inductive ChildState
  /-- Child has been spawned and reaping is in progress. -/
  | pending
  /-- Child exited with status 0. -/
  | succeeded
  /-- Child exited non-zero (or spawn failed). -/
  | failed
  deriving DecidableEq, Repr

/-- The main-loop state we care about for the "doesn't block validation"
proof: a counter of completed tip-change loop iterations. The Rust code's
main loop never awaits the child, so this counter advances regardless of
whether the child has succeeded, failed, or is still pending. -/
@[ext]
structure MainLoopState where
  iterations : Nat
  deriving Repr

/-- A "world" combines the main loop and a most-recently-spawned child. -/
@[ext]
structure World where
  main : MainLoopState
  child : ChildState
  deriving Repr

/-- The main loop's iteration step: it advances regardless of the child. -/
def mainStep (m : MainLoopState) : MainLoopState :=
  { iterations := m.iterations + 1 }

/-- The reaper's transition: `pending` may go to `succeeded` or `failed`,
the terminal states stay put. The reaper does NOT touch the main loop. -/
def childStep (target : ChildState) (c : ChildState) : ChildState :=
  match c with
  | .pending => target
  | s => s

/-- A "transition" of the world: the main loop advances by one iteration,
and the child (if pending) may transition to its target state. -/
def worldStep (target : ChildState) (w : World) : World :=
  { main := mainStep w.main
    child := childStep target w.child }

/-! ## Config -/

/-- The block-notify configuration. Mirrors
`Config { block_notify_command: Option<String> }` at `notify.rs:24-37`. -/
structure Config where
  blockNotifyCommand : Option (List Char)
  deriving Repr

/-- The default configuration: notify is disabled. Mirrors
`Config::default()` at `notify.rs:42-48`. -/
def defaultConfig : Config := { blockNotifyCommand := none }

/-! ## Constants -/

/-- The length of the `%s` substring (2 chars: `'%'` and `'s'`). -/
def PS_LEN : Nat := 2

/-- The length of a block hash display (64 = 2 * 32). -/
def DISPLAY_LEN : Nat := 64

/-! ## Equational lemmas for `replaceAllPs` and `countPs` -/

theorem replaceAllPs_nil (repl : List Char) :
    replaceAllPs repl [] = [] := rfl

theorem replaceAllPs_singleton (repl : List Char) (c : Char) :
    replaceAllPs repl [c] = [c] := rfl

theorem replaceAllPs_ps (rest repl : List Char) :
    replaceAllPs repl ('%' :: 's' :: rest)
      = repl ++ replaceAllPs repl rest := by
  change (if ('%' : Char) = '%' ∧ ('s' : Char) = 's'
          then repl ++ replaceAllPs repl rest
          else '%' :: replaceAllPs repl ('s' :: rest))
        = repl ++ replaceAllPs repl rest
  simp

theorem replaceAllPs_not_ps (c d : Char) (rest repl : List Char)
    (h : ¬ (c = '%' ∧ d = 's')) :
    replaceAllPs repl (c :: d :: rest)
      = c :: replaceAllPs repl (d :: rest) := by
  change (if c = '%' ∧ d = 's'
          then repl ++ replaceAllPs repl rest
          else c :: replaceAllPs repl (d :: rest))
        = c :: replaceAllPs repl (d :: rest)
  simp [h]

theorem countPs_nil : countPs [] = 0 := rfl

theorem countPs_singleton (c : Char) : countPs [c] = 0 := rfl

theorem countPs_ps (rest : List Char) :
    countPs ('%' :: 's' :: rest) = 1 + countPs rest := by
  change (if ('%' : Char) = '%' ∧ ('s' : Char) = 's'
          then 1 + countPs rest
          else countPs ('s' :: rest))
        = 1 + countPs rest
  simp

theorem countPs_not_ps (c d : Char) (rest : List Char)
    (h : ¬ (c = '%' ∧ d = 's')) :
    countPs (c :: d :: rest) = countPs (d :: rest) := by
  change (if c = '%' ∧ d = 's'
          then 1 + countPs rest
          else countPs (d :: rest))
        = countPs (d :: rest)
  simp [h]

/-! ## T1 — T3: IBD gate -/

/-- **T1 (IBD gate suppresses).** When `closeToTip = false`, the notify
command is not spawned. Models the `wait_until_close_to_tip().await` blocker
at `notify.rs:92-95`: while IBD is on, the callback never fires. -/
theorem tryNotify_suppresses_during_IBD
    (cmd : List Char) (h : BlockHash) :
    tryNotify false cmd h = none := by
  unfold tryNotify; rfl

/-- **T2 (IBD gate passes once close).** When `closeToTip = true`, the notify
command is spawned with the rendered template. -/
theorem tryNotify_fires_when_close_to_tip
    (cmd : List Char) (h : BlockHash) :
    tryNotify true cmd h = some (render cmd h) := by
  unfold tryNotify; rfl

/-- **T3 (gating iff).** `tryNotify` succeeds iff we are close to the tip. -/
theorem tryNotify_isSome_iff (closeToTip : Bool) (cmd : List Char)
    (h : BlockHash) :
    (tryNotify closeToTip cmd h).isSome ↔ closeToTip = true := by
  unfold tryNotify
  cases closeToTip <;> simp

/-! ## T4 — T6: `%s` substitution

The general "no placeholders ⇒ identity" theorem T4 follows by induction
on the command, using the equational lemmas above. -/

/-- **T4 (no placeholders ⇒ identity).** A command containing no `%s`
literal is fixed by `replaceAllPs`, so `render` returns the template
unchanged. Pins `notify.rs/tests.rs:36`
(`render_command("echo hello", h) = "echo hello"`). -/
theorem render_no_placeholder_is_identity
    (cmd : List Char) (h : BlockHash) (hzero : countPs cmd = 0) :
    render cmd h = cmd := by
  unfold render
  -- Induction on cmd; case-split on whether the head pair is a `%s`.
  induction cmd with
  | nil => exact replaceAllPs_nil _
  | cons c rest ih =>
    cases rest with
    | nil => exact replaceAllPs_singleton _ c
    | cons d rest' =>
      by_cases hps : c = '%' ∧ d = 's'
      · -- `c :: d :: rest' = '%' :: 's' :: rest'`. But countPs ≥ 1, contradiction.
        exfalso
        obtain ⟨hc, hd⟩ := hps
        subst hc; subst hd
        rw [countPs_ps] at hzero
        omega
      · -- Head pair is not `%s`. Pass through.
        rw [replaceAllPs_not_ps c d rest' (display h) hps]
        congr 1
        -- Need replaceAllPs (display h) (d :: rest') = d :: rest'.
        -- Use ih on rest = d :: rest'.
        have h_tail : countPs (d :: rest') = 0 := by
          rw [countPs_not_ps c d rest' hps] at hzero
          exact hzero
        exact ih h_tail

/-- **T5 (one-`%s` concrete witness).** Pins the
`render_command("a %s b", h) = "a <hex> b"` invariant on a concrete short
template. The template is `['a', ' ', '%', 's', ' ', 'b']`. -/
theorem render_one_placeholder_concrete (h : BlockHash) :
    render ['a', ' ', '%', 's', ' ', 'b'] h
      = 'a' :: ' ' :: (display h ++ [' ', 'b']) := by
  unfold render
  -- Step through using the equational lemmas.
  rw [replaceAllPs_not_ps 'a' ' ' _ _ (by decide)]
  rw [replaceAllPs_not_ps ' ' '%' _ _ (by decide)]
  rw [replaceAllPs_ps]
  rw [replaceAllPs_not_ps ' ' 'b' _ _ (by decide)]
  rw [replaceAllPs_singleton]

/-- **T6 (two-`%s` ⇒ each becomes the same hash).** Pins
`render_command("%s%s", h) = "<hex><hex>"`. Two distinct `%s`s, the SAME
`display` substituted into both. -/
theorem render_two_placeholders_same_hash (h : BlockHash) :
    render ['%', 's', '%', 's'] h = display h ++ display h := by
  unfold render
  rw [show (['%', 's', '%', 's'] : List Char)
        = '%' :: 's' :: '%' :: 's' :: [] from rfl]
  rw [replaceAllPs_ps]
  rw [replaceAllPs_ps]
  rw [replaceAllPs_nil]
  simp

/-! ## T8: display length pin (needed by T7) -/

/-- **T8 (display length is exactly 64).** For any 32-byte block hash, the
hex display is exactly 64 characters. Pins
`assert_eq!(rendered.len(), 64)` at `notify.rs/tests.rs:49`. -/
theorem display_length (h : BlockHash) : (display h).length = DISPLAY_LEN := by
  unfold display DISPLAY_LEN
  rw [bytesHex_length, h.length_eq]
  decide

/-! ## T7: substitution length -/

/-- Strong-induction helper: the length identity for `replaceAllPs` against
a fixed replacement of length `= DISPLAY_LEN`. We use a Nat strong-induction
on `cmd.length`. -/
private theorem replaceAllPs_length_helper (repl : List Char)
    (h_repl : repl.length = DISPLAY_LEN) (k : Nat) :
    ∀ cmd : List Char, cmd.length = k →
      (replaceAllPs repl cmd).length
        = cmd.length + countPs cmd * (DISPLAY_LEN - PS_LEN) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro cmd hlen
    match cmd, hlen with
    | [], _ =>
      rw [replaceAllPs_nil, countPs_nil]; decide
    | [c], _ =>
      rw [replaceAllPs_singleton, countPs_singleton]; simp
    | c :: d :: rest', hlen =>
      by_cases hps : c = '%' ∧ d = 's'
      · obtain ⟨hc, hd⟩ := hps
        subst hc; subst hd
        rw [replaceAllPs_ps, countPs_ps]
        rw [List.length_append, h_repl]
        have h_rest_lt : rest'.length < k := by
          simp [List.length_cons] at hlen
          omega
        rw [ih rest'.length h_rest_lt rest' rfl]
        unfold DISPLAY_LEN PS_LEN
        simp [List.length_cons]
        omega
      · rw [replaceAllPs_not_ps c d rest' repl hps]
        rw [countPs_not_ps c d rest' hps]
        have h_rest_lt : (d :: rest').length < k := by
          simp [List.length_cons] at hlen
          simp [List.length_cons]
          omega
        rw [show ((c :: replaceAllPs repl (d :: rest')).length :)
            = 1 + (replaceAllPs repl (d :: rest')).length from by
          simp [List.length_cons]; omega]
        rw [ih (d :: rest').length h_rest_lt (d :: rest') rfl]
        simp [List.length_cons]
        omega

private theorem replaceAllPs_length_strong (repl : List Char)
    (h_repl : repl.length = DISPLAY_LEN) (cmd : List Char) :
    (replaceAllPs repl cmd).length
      = cmd.length + countPs cmd * (DISPLAY_LEN - PS_LEN) :=
  replaceAllPs_length_helper repl h_repl cmd.length cmd rfl

/-- **T7 (substitution length).** The rendered command's length is exactly
`cmd.length + countPs cmd * (DISPLAY_LEN - PS_LEN)`. The rendered size is
purely a function of the template — no attacker-controlled input can affect
it (the hash is fixed-size 64). -/
theorem render_length (cmd : List Char) (h : BlockHash) :
    (render cmd h).length
      = cmd.length + countPs cmd * (DISPLAY_LEN - PS_LEN) := by
  unfold render
  have h_disp_len : (display h).length = DISPLAY_LEN := display_length h
  exact replaceAllPs_length_strong (display h) h_disp_len cmd

/-! ## T9 — T10: display safety -/

/-- **T9 (display is lowercase hex).** Every character of the display is a
lowercase hex digit. Pins the `is_ascii_hexdigit() && !is_ascii_uppercase()`
test at `notify.rs/tests.rs:50-52`. -/
theorem display_chars_lowercase_hex (h : BlockHash) (c : Char)
    (hc : c ∈ display h) : isLowercaseHex c = true := by
  unfold display at hc
  exact bytesHex_chars_hex h.bytes h.bytes_valid c hc

/-- **T10 (display contains no shell metacharacters).** Strengthens T9: no
character of the display is any of the listed shell metacharacters or
whitespace. This is the safety promise behind the Rust comment "no shell
metacharacters" at `notify.rs:171`. -/
theorem display_chars_noShellMeta (h : BlockHash) (c : Char)
    (hc : c ∈ display h) :
    c ≠ '$' ∧ c ≠ '`' ∧ c ≠ '\\' ∧ c ≠ ';' ∧ c ≠ '|' ∧ c ≠ '&'
      ∧ c ≠ '<' ∧ c ≠ '>' ∧ c ≠ '(' ∧ c ≠ ')' ∧ c ≠ '\'' ∧ c ≠ '"'
      ∧ c ≠ ' ' ∧ c ≠ '\n' := by
  have h_hex : isLowercaseHex c = true := display_chars_lowercase_hex h c hc
  unfold isLowercaseHex at h_hex
  simp only [decide_eq_true_eq] at h_hex
  rcases h_hex with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;>
    (subst h; decide)

/-! ## T11: child lifecycle invariance -/

/-- **T11 (failure does not block the main loop).** Regardless of what the
child transitions to (`succeeded`, `failed`, or stays `pending`), the main
loop advances by exactly one iteration per `worldStep`. This is the
formal version of "non-zero exit does not block validation" at
`notify.rs:146-165`: the main loop never awaits the child. -/
theorem main_loop_advances_regardless_of_child
    (target : ChildState) (w : World) :
    (worldStep target w).main.iterations = w.main.iterations + 1 := by
  unfold worldStep mainStep; rfl

/-- **T11' (main loop result invariant under any child target).** Two
`worldStep`s with different child targets agree on the main loop. -/
theorem main_loop_invariant_under_target
    (target1 target2 : ChildState) (w : World) :
    (worldStep target1 w).main = (worldStep target2 w).main := by
  unfold worldStep; rfl

/-! ## T12: full pipeline -/

/-- The end-to-end action a single `run_block_notify` iteration takes:
observe a tip change, wait for IBD to end, render and "spawn" the command.
Models the loop body at `notify.rs:82-105`. -/
def iterationOutput (closeToTip : Bool) (cmd : List Char) (h : BlockHash) :
    Option (List Char) :=
  tryNotify closeToTip cmd h

/-- **T12 (full pipeline characterisation).** One iteration of the notify
loop outputs `none` iff IBD is active, and `some r` iff IBD is over with
`r = render cmd h`. -/
theorem iteration_output_none_iff_IBD
    (closeToTip : Bool) (cmd : List Char) (h : BlockHash) :
    iterationOutput closeToTip cmd h = none ↔ closeToTip = false := by
  unfold iterationOutput tryNotify
  cases closeToTip <;> simp

/-- **T12' (full pipeline: close to tip ⇒ spawns rendered command).** -/
theorem iteration_output_some_when_close_to_tip
    (cmd : List Char) (h : BlockHash) :
    iterationOutput true cmd h = some (render cmd h) := by
  unfold iterationOutput tryNotify; rfl

/-! ## T13: default config -/

/-- **T13 (default config disables notify).** The default configuration
sets `block_notify_command = None`, so the notify task is not spawned
unless the operator opts in. Models `Config::default()` at `notify.rs:42-48`
and the test at `notify.rs/tests.rs:56-58`. -/
theorem defaultConfig_disables_notify :
    defaultConfig.blockNotifyCommand = none := by
  unfold defaultConfig; rfl

end Zebra.ZebradBlockNotify
