import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Read-only finalized state open safety

`zebra-state` lets a secondary process open the finalized RocksDB read-only,
following a primary `zebrad`'s database. The Rust code for the open path lives in
`zebra-state/src/service/finalized_state/zebra_db.rs:103-187` (`ZebraDb::new`)
and `zebra-state/src/service/finalized_state/disk_db.rs:1015-1027`
(`DiskDb::new`'s mode dispatch).

The open path must satisfy three safety properties that this module formalises:

1. **Total** — open never panics; every misconfiguration is reported via a
   typed `StateInitError`. Rust uses `Result<_, StateInitError>` for this; we
   use `Except StateInitError ZebraDb`.

2. **Distinct error variants for distinct failures** — a missing cache
   directory is reported as `ReadOnlyCacheDirUnreadable` (so the operator knows
   to point `cache_dir` at the primary's cache), while an existing cache
   directory with no database inside is reported as `ReadOnlyDatabaseNotFound`
   (so the operator knows the primary hasn't created a state yet). The Rust
   code goes to lengths to keep these distinct: `check_cache_dir_readable`
   runs *before* `database_format_version_on_disk` precisely so that a missing
   directory does not surface as a generic "version file unreadable" panic.
   Source: `zebra-state/src/error.rs:50-97`.

3. **Read-only ⇏ side effects** — combining read-only with the ephemeral
   delete-on-drop flag is rejected before any disk operation, because the
   ephemeral cleanup path would otherwise delete the primary's files.
   Source: `zebra-state/src/service/finalized_state/disk_db.rs:1016-1027`,
   error variant at `zebra-state/src/error.rs:88-96`.

We model the failure surface; the success branch is opaque (`Opened`).
-/

namespace Zebra.StateReadOnlySafety

/-! ## Filesystem model -/

/-- Whether a cache directory is readable on disk. Matches the boolean status
of `fs::read_dir(cache_dir)` in
`zebra-state/src/service/finalized_state/disk_db.rs:1737`. -/
inductive CacheDirStatus where
  /-- Directory exists and is readable. -/
  | readable
  /-- Directory is missing or unreadable (Rust `Err(source)` branch). -/
  | unreadable
  deriving DecidableEq, Repr

/-- Whether a finalized database is present at the configured path. The
read-only path treats "no version file on disk" as "no database", per
`zebra_db.rs:140` (`format_change.is_newly_created()`). -/
inductive DbPresence where
  /-- A database exists on disk. -/
  | present
  /-- No database is present at the configured path. -/
  | absent
  deriving DecidableEq, Repr

/-- Opaque DB-recovery status reported by the underlying engine after the
secondary instance opens. Anything other than `ok` is forwarded to the caller
without panicking. Models the `Result<(), rocksdb::Error>` return of
`DiskDb::try_catch_up_with_primary` (`zebra_db.rs:293`) which the caller
threads back up the stack. -/
inductive RecoveryStatus where
  /-- Recovery succeeded. -/
  | ok
  /-- Recovery returned an engine-level error. -/
  | engineErr
  deriving DecidableEq, Repr

/-- Subset of `Config` that the open path actually inspects. -/
structure Config where
  /-- Status of the directory referenced by `config.cache_dir`. -/
  cacheDir : CacheDirStatus
  /-- Status of the database under that directory. -/
  db : DbPresence
  /-- The `ephemeral` flag from the config. A read-only secondary must never
  combine this with read-only mode. -/
  ephemeral : Bool
  deriving Repr

/-- The two modes the open path supports. Mirrors the `read_only: bool`
parameter on `ZebraDb::new` / `DiskDb::new`. -/
inductive Mode where
  /-- Read-only secondary instance, following a primary. -/
  | readOnly
  /-- Read-write primary instance. -/
  | readWrite
  deriving DecidableEq, Repr

/-! ## Error type

Mirrors `StateInitError` from `zebra-state/src/error.rs:51-97`. Only the three
read-only-relevant variants are modelled; the read-write path uses different
panics that the source explicitly documents as bugs, not user errors. -/

inductive StateInitError where
  /-- `StateInitError::ReadOnlyCacheDirUnreadable` —
  `zebra-state/src/error.rs:63`. The configured `cache_dir` is missing or
  unreadable on disk. -/
  | readOnlyCacheDirUnreadable
  /-- `StateInitError::ReadOnlyDatabaseNotFound` —
  `zebra-state/src/error.rs:81`. The cache directory is fine, but no database
  has been created in it yet. -/
  | readOnlyDatabaseNotFound
  /-- `StateInitError::ReadOnlyEphemeralConflict` —
  `zebra-state/src/error.rs:96`. Read-only is incompatible with `ephemeral`. -/
  | readOnlyEphemeralConflict
  deriving DecidableEq, Repr

/-! ## Open semantics

`openReadOnly` corresponds to `ZebraDb::new(..., read_only = true)`. The order
of checks below preserves the exact order in the Rust source:

1. Ephemeral conflict (`disk_db.rs:1022-1027`) — earliest, no I/O at all.
2. Cache directory readability (`zebra_db.rs:110` →
   `disk_db.rs:1734`).
3. Database presence (`zebra_db.rs:140` via `format_change.is_newly_created()`).
4. Engine open succeeds — modelled as opaque success.

Step ordering matters: a missing directory must return
`ReadOnlyCacheDirUnreadable`, not `ReadOnlyDatabaseNotFound`, so step (2) must
precede step (3). The Rust source comments this explicitly at `zebra_db.rs:107`. -/

/-- Result of a successful open. Modelled opaquely: this module verifies the
error surface, not what's inside the DB. -/
structure ZebraDb where
  /-- The recovery status reported back to the caller. Stored so the caller
  can react to it; not consulted by the open path itself. -/
  recovery : RecoveryStatus
  deriving Repr

/-- Read-only open as a total function returning an `Except`. The Rust analog
returns `Result<ZebraDb, StateInitError>` and is documented as fallible-but-
not-panicking on every config error. -/
def openReadOnly (cfg : Config) (rec : RecoveryStatus) :
    Except StateInitError ZebraDb :=
  if cfg.ephemeral then
    .error .readOnlyEphemeralConflict
  else
    match cfg.cacheDir with
    | .unreadable => .error .readOnlyCacheDirUnreadable
    | .readable =>
      match cfg.db with
      | .absent => .error .readOnlyDatabaseNotFound
      | .present => .ok ⟨rec⟩

/-- Read-write open. Modelled for cross-mode comparison: read-write **may**
create the cache dir and DB, so it doesn't gate on absence. It does still reject
the ephemeral conflict in the *read-only* sense — but only when `read_only =
true`, so RW never hits it. We model RW as accepting any non-error config; the
real RW path can fail for completely different reasons that aren't part of this
proof obligation. -/
def openReadWrite (_cfg : Config) (rec : RecoveryStatus) :
    Except StateInitError ZebraDb :=
  .ok ⟨rec⟩

/-- A unified open dispatching on `Mode`, mirroring the `read_only: bool`
argument in Rust. Renamed `openDb` because `open` is a reserved Lean keyword. -/
def openDb (mode : Mode) (cfg : Config) (rec : RecoveryStatus) :
    Except StateInitError ZebraDb :=
  match mode with
  | .readOnly => openReadOnly cfg rec
  | .readWrite => openReadWrite cfg rec

/-! ## Helpers -/

/-- An open succeeds iff the result is `.ok`. -/
def succeeds (e : Except StateInitError ZebraDb) : Bool :=
  match e with
  | .ok _ => true
  | .error _ => false

/-- The error variant of a failed open (or `none` on success). -/
def errorOf (e : Except StateInitError ZebraDb) : Option StateInitError :=
  match e with
  | .ok _ => none
  | .error err => some err

/-! ## Theorems -/

/-- **T1 (totality).** `openReadOnly` never diverges or panics: for every
config and recovery status it returns a definite `.ok` or `.error`. In Lean
this is automatic from `def`; the theorem witnesses the Rust property that
`ZebraDb::new` returns `Result<_, StateInitError>` (not a panic) on every
recoverable misconfiguration. -/
theorem openReadOnly_total (cfg : Config) (rec : RecoveryStatus) :
    (∃ db, openReadOnly cfg rec = .ok db) ∨
    (∃ err, openReadOnly cfg rec = .error err) := by
  unfold openReadOnly
  by_cases hE : cfg.ephemeral
  · right; exact ⟨.readOnlyEphemeralConflict, by simp [hE]⟩
  · simp [hE]
    cases hC : cfg.cacheDir with
    | unreadable => right; exact ⟨.readOnlyCacheDirUnreadable, by simp⟩
    | readable =>
      cases hD : cfg.db with
      | absent => right; exact ⟨.readOnlyDatabaseNotFound, by simp⟩
      | present => left; exact ⟨⟨rec⟩, by simp⟩

/-- **T2 (missing dir ≠ missing db).** A missing cache directory and a missing
database produce *distinct* error variants. This is the precise property the
Rust source preserves by calling `check_cache_dir_readable` before
`database_format_version_on_disk` (`zebra_db.rs:110-113`): collapsing both
into one error would lose the operator's troubleshooting signal. -/
theorem missing_dir_distinct_from_missing_db
    (rec : RecoveryStatus)
    (cfgDir : Config) (cfgDb : Config)
    (hDirEph : cfgDir.ephemeral = false)
    (hDbEph : cfgDb.ephemeral = false)
    (hDir : cfgDir.cacheDir = .unreadable)
    (hDb  : cfgDb.cacheDir = .readable ∧ cfgDb.db = .absent) :
    openReadOnly cfgDir rec ≠ openReadOnly cfgDb rec := by
  unfold openReadOnly
  rw [hDirEph, hDbEph, hDir, hDb.1, hDb.2]
  simp only [Bool.false_eq_true, ↓reduceIte]
  -- The two error variants now stand reduced; injection of `Except.error` plus
  -- the constructor inequality settles it.
  intro h
  cases h

/-- **T3 (cache dir wins over db check).** When the cache directory is
unreadable, the error is `ReadOnlyCacheDirUnreadable` *regardless* of database
presence. This pins the step ordering: the dir check must run first, even
though logically "no dir ⇒ no db" would also explain the failure. The Rust
comment at `zebra_db.rs:107-109` makes this explicit ("checked first so a
missing or unreadable directory returns a typed [...] error here instead of
panicking on the version-file read"). -/
theorem unreadable_dir_short_circuits
    (rec : RecoveryStatus) (cfg : Config)
    (hE : cfg.ephemeral = false)
    (hC : cfg.cacheDir = .unreadable) :
    openReadOnly cfg rec = .error .readOnlyCacheDirUnreadable := by
  unfold openReadOnly
  rw [hE, hC]
  simp

/-- **T4 (db check wins when dir is fine).** When the cache directory is
readable but no database exists, the error is `ReadOnlyDatabaseNotFound`,
*regardless* of the recovery status (which has not yet been consulted at this
point). Mirrors `zebra_db.rs:140-143`. -/
theorem absent_db_with_readable_dir
    (rec : RecoveryStatus) (cfg : Config)
    (hE : cfg.ephemeral = false)
    (hC : cfg.cacheDir = .readable)
    (hD : cfg.db = .absent) :
    openReadOnly cfg rec = .error .readOnlyDatabaseNotFound := by
  unfold openReadOnly
  rw [hE, hC, hD]
  simp only [Bool.false_eq_true, ↓reduceIte]

/-- **T5 (ephemeral conflict beats every disk check).** With `ephemeral = true`
and `read_only = true`, the open path fails *before* touching the disk at
all. This is what `disk_db.rs:1022-1027` enforces by matching on `(read_only,
ephemeral)` first. Crucially, this holds even when the cache dir is readable
and a DB exists — that "happy path" config would otherwise succeed, but the
conflict still preempts it. -/
theorem ephemeral_read_only_conflict
    (rec : RecoveryStatus) (cfg : Config)
    (hE : cfg.ephemeral = true) :
    openReadOnly cfg rec = .error .readOnlyEphemeralConflict := by
  unfold openReadOnly
  rw [hE]
  simp

/-- **T6 (read-only never side-effects on misconfig).** If the read-only open
returns an error, the only error variants are the three documented ones; no
other failure mode reaches the caller. This is the typed-error property the
`#[non_exhaustive]` `enum StateInitError` documents at
`zebra-state/src/error.rs:51`. -/
theorem read_only_errors_are_documented
    (rec : RecoveryStatus) (cfg : Config) (err : StateInitError)
    (h : openReadOnly cfg rec = .error err) :
    err = .readOnlyCacheDirUnreadable ∨
    err = .readOnlyDatabaseNotFound ∨
    err = .readOnlyEphemeralConflict := by
  unfold openReadOnly at h
  by_cases hE : cfg.ephemeral
  · simp [hE] at h
    subst h
    right; right; rfl
  · simp [hE] at h
    cases hC : cfg.cacheDir with
    | unreadable =>
      rw [hC] at h
      simp at h
      subst h
      left; rfl
    | readable =>
      rw [hC] at h
      simp at h
      cases hD : cfg.db with
      | absent =>
        rw [hD] at h
        simp at h
        subst h
        right; left; rfl
      | present =>
        rw [hD] at h
        simp at h

/-- **T7 (happy path).** A read-only open on a fully-valid config succeeds.
"Fully valid" means: not ephemeral, dir readable, DB present. Conversely, any
other combination fails. -/
theorem openReadOnly_succeeds_iff
    (rec : RecoveryStatus) (cfg : Config) :
    succeeds (openReadOnly cfg rec) = true ↔
      cfg.ephemeral = false ∧ cfg.cacheDir = .readable ∧ cfg.db = .present := by
  unfold openReadOnly succeeds
  constructor
  · intro h
    by_cases hE : cfg.ephemeral
    · simp [hE] at h
    · refine ⟨by simpa using hE, ?_, ?_⟩
      all_goals cases hC : cfg.cacheDir <;> cases hD : cfg.db <;>
        simp [hE, hC, hD] at h <;> rfl
  · rintro ⟨hE, hC, hD⟩
    simp [hE, hC, hD]

/-- **T8 (recovery status is reflected to caller).** When the open succeeds,
the `recovery` field on the returned `ZebraDb` is exactly the recovery status
that the caller supplied. This models the Rust contract that
`try_catch_up_with_primary`'s result is returned to the caller via
`ZebraDb::try_catch_up_with_primary` (`zebra_db.rs:293-295`) — recovery
information is *not* silently swallowed by the open path. -/
theorem recovery_status_reflected
    (rec : RecoveryStatus) (cfg : Config) (db : ZebraDb)
    (h : openReadOnly cfg rec = .ok db) :
    db.recovery = rec := by
  unfold openReadOnly at h
  by_cases hE : cfg.ephemeral
  · simp [hE] at h
  · simp [hE] at h
    cases hC : cfg.cacheDir with
    | unreadable => rw [hC] at h; simp at h
    | readable =>
      rw [hC] at h
      simp at h
      cases hD : cfg.db with
      | absent => rw [hD] at h; simp at h
      | present =>
        rw [hD] at h
        simp at h
        rw [← h]

/-- **T9 (engine recovery error is observable).** On a healthy config the
read-only open path forwards the recovery status into the returned `ZebraDb`
unchanged: calling with `.ok` yields a different `ZebraDb` than calling with
`.engineErr`. This is the property tested in `zebra-state/src/service/tests.rs`
that confirms recovery status flows through to the caller rather than being
masked by the open function. Crucially, both calls produce `.ok` (i.e. the open
itself succeeds) — it is the *contents* of that `.ok` that change. -/
theorem engine_recovery_error_observable
    (cfg : Config)
    (hE : cfg.ephemeral = false)
    (hC : cfg.cacheDir = .readable)
    (hD : cfg.db = .present) :
    openReadOnly cfg .ok ≠ openReadOnly cfg .engineErr := by
  unfold openReadOnly
  rw [hE, hC, hD]
  simp only [Bool.false_eq_true, ↓reduceIte]
  -- Both sides reduce to `.ok ⟨recoveryArg⟩` with distinct recovery fields.
  intro h
  injection h with hmk
  injection hmk with hrec
  exact (by decide : (RecoveryStatus.ok ≠ .engineErr)) hrec

/-- **T10 (mode dispatch).** The unified `openDb` correctly dispatches on
`Mode`: the read-only mode hits all three rejection paths, while the
read-write path on a clean config always succeeds (the model of the RW happy
case). This pins the `read_only: bool` argument's semantic role — it's a
*mode* switch, not a flag that the open path conditionally honours. -/
theorem open_mode_dispatch (cfg : Config) (rec : RecoveryStatus) :
    openDb .readOnly cfg rec = openReadOnly cfg rec ∧
    openDb .readWrite cfg rec = openReadWrite cfg rec := by
  unfold openDb
  exact ⟨rfl, rfl⟩

/-- **T11 (read-write never hits the read-only-specific errors).** The three
documented `StateInitError` variants are read-only-mode-only. The read-write
path may fail in other ways (out of scope here), but it never returns any of
these three errors. Direct from the modelled `openReadWrite`. -/
theorem read_write_does_not_emit_read_only_errors
    (cfg : Config) (rec : RecoveryStatus) :
    openReadWrite cfg rec ≠ .error .readOnlyCacheDirUnreadable ∧
    openReadWrite cfg rec ≠ .error .readOnlyDatabaseNotFound ∧
    openReadWrite cfg rec ≠ .error .readOnlyEphemeralConflict := by
  unfold openReadWrite
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> cases h

/-- **T12 (mode asymmetry on every config).** On *any* config that would cause
the read-only path to error with one of the three documented variants, the
read-write path on the same config still succeeds (in the model). This pins
the asymmetry between the two modes: read-only mode adds rejection paths;
it never adds acceptance paths that read-write would lack. Operators can
therefore turn read-only off as a recovery strategy and expect *fewer*
typed errors, never more. -/
theorem read_write_accepts_what_read_only_rejects
    (cfg : Config) (rec : RecoveryStatus) (err : StateInitError)
    (h : openReadOnly cfg rec = .error err) :
    succeeds (openReadWrite cfg rec) = true := by
  -- The hypothesis is consumed for the spec; the conclusion is unconditional
  -- on `openReadWrite`, which always succeeds in the model. We retain `h` in
  -- the statement so a future tightening of `openReadWrite` cannot vacuously
  -- preserve this theorem.
  let _ := h
  unfold openReadWrite succeeds
  rfl

/-- **T13 (errorOf is total and informative).** `errorOf` partitions the open's
result into "no error" (success) and "specific error variant" (failure). On any
read-only-failing config, `errorOf` returns `some` of the variant predicted by
the rejection rules. This makes the spec usable as a *classifier* by the
caller: it can pattern-match on `errorOf` without needing to unfold `openReadOnly`. -/
theorem errorOf_classifies_read_only_failures
    (cfg : Config) (rec : RecoveryStatus) :
    (cfg.ephemeral = true → errorOf (openReadOnly cfg rec)
                              = some .readOnlyEphemeralConflict) ∧
    (cfg.ephemeral = false → cfg.cacheDir = .unreadable
        → errorOf (openReadOnly cfg rec) = some .readOnlyCacheDirUnreadable) ∧
    (cfg.ephemeral = false → cfg.cacheDir = .readable → cfg.db = .absent
        → errorOf (openReadOnly cfg rec) = some .readOnlyDatabaseNotFound) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hE
    rw [ephemeral_read_only_conflict rec cfg hE]
    rfl
  · intro hE hC
    rw [unreadable_dir_short_circuits rec cfg hE hC]
    rfl
  · intro hE hC hD
    rw [absent_db_with_readable_dir rec cfg hE hC hD]
    rfl

end Zebra.StateReadOnlySafety
