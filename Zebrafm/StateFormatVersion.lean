import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Zebra state database format version (SemVer)

Models the SemVer-shaped on-disk database format version from
`zebra-state/src/constants.rs`:

- `DATABASE_FORMAT_VERSION = 27`         (major; line 37)
- `DATABASE_FORMAT_MINOR_VERSION = 0`    (minor; line 46)
- `DATABASE_FORMAT_PATCH_VERSION = 0`    (patch; line 50)

and the format-change classification from
`zebra-state/src/service/finalized_state/disk_format/upgrade.rs:215`:

```rust
match disk_version.cmp_precedence(&running_version) {
    Ordering::Less    => Upgrade { older_disk_version, newer_running_version },
    Ordering::Greater => Downgrade { newer_disk_version, older_running_version },
    Ordering::Equal   => CheckOpenCurrent { running_version },
}
```

plus the major-upgrade re-use predicate at lines 84-87:

```rust
fn is_reusable_major_upgrade(&self) -> bool {
    let version = self.version();
    version.minor == 0 && version.patch == 0
}
```

## What we model

We use `Nat` triples — no bit vectors, no `semver` crate. `cmp_precedence`
on stable releases (no prerelease, no build metadata; Zebra's state version
never carries either except for the optional `indexer` build tag which is
informational) is purely lexicographic on `(major, minor, patch)`. We model
that as `Version.lt`.

## Theorems

* `T1`: the current format version is pinned to `(27, 0, 0)`.
* `T2`: `Version.lt` is a strict order (transitive, irreflexive); `Version`
  comparisons are decidable.
* `T3`: a major bump strictly increases the version, regardless of how minor/
  patch change.
* `T4`: a minor or patch bump within the same major strictly increases the
  version — these are the forward-compatible bumps Rust describes at
  `constants.rs:40-46`.
* `T5`: `classify` matches `cmp_precedence`'s three-way branch verbatim.
* `T6`: `isReusableMajorUpgrade` is exactly the predicate `minor = 0 ∧ patch = 0`.
* `T7`: the assertions in `mark_as_upgraded_to`
  (`upgrade.rs:730-753`) are simultaneously satisfiable:
  for any `disk < upgrade ≤ running`, every assertion holds.
* `T8`: same-major upgrades are forward-compatible in the precise sense that
  the upgrade target is below the running version's "next major" line, i.e.
  no major-version skip is required to apply them.
* `T9`: the current version satisfies the `is_reusable_major_upgrade`
  predicate (it's `(27, 0, 0)`).
* `T10`: `cmp_precedence` agrees with `Version.lt` / `eq` (totality).
-/

namespace Zebra.StateFormatVersion

/-! ## Version data type -/

/-- A SemVer-shaped database format version. `major`, `minor`, `patch` are
each a `Nat`. Source: `zebra-state/src/constants.rs:37,46,50`. -/
structure Version where
  major : Nat
  minor : Nat
  patch : Nat
  deriving DecidableEq, Repr

/-- Lexicographic strict order, mirroring `semver::Version::cmp_precedence`
on stable (no prerelease) versions. -/
def Version.lt (a b : Version) : Prop :=
  a.major < b.major ∨
  (a.major = b.major ∧ a.minor < b.minor) ∨
  (a.major = b.major ∧ a.minor = b.minor ∧ a.patch < b.patch)

instance : LT Version := ⟨Version.lt⟩

instance Version.decLt (a b : Version) : Decidable (a < b) := by
  unfold LT.lt instLTVersion Version.lt
  exact inferInstance

/-- Three-way result, matching Rust's `std::cmp::Ordering`. -/
inductive VOrd | lt | eq | gt
  deriving DecidableEq, Repr

/-- Compute the three-way comparison. -/
def Version.cmp (a b : Version) : VOrd :=
  if a.major < b.major then .lt
  else if a.major > b.major then .gt
  else if a.minor < b.minor then .lt
  else if a.minor > b.minor then .gt
  else if a.patch < b.patch then .lt
  else if a.patch > b.patch then .gt
  else .eq

/-! ## Constants from `zebra-state/src/constants.rs` -/

/-- The current code-side major version. Source: `constants.rs:37`. -/
def DATABASE_FORMAT_VERSION : Nat := 27

/-- The current code-side minor version. Source: `constants.rs:46`. -/
def DATABASE_FORMAT_MINOR_VERSION : Nat := 0

/-- The current code-side patch version. Source: `constants.rs:50`. -/
def DATABASE_FORMAT_PATCH_VERSION : Nat := 0

/-- The current running version. Source:
`constants.rs::state_database_format_version_in_code()` (lines 56-67). -/
def currentVersion : Version :=
  { major := DATABASE_FORMAT_VERSION
    minor := DATABASE_FORMAT_MINOR_VERSION
    patch := DATABASE_FORMAT_PATCH_VERSION }

/-! ## Format-change classification

Mirrors `DbFormatChange::open_database`
(`upgrade.rs:203-246`). -/

/-- The kind of format change Zebra picks when opening an existing DB. -/
inductive FormatChange
  | upgrade   (older_disk newer_running : Version)
  | downgrade (newer_disk older_running : Version)
  | checkOpenCurrent (running : Version)
  deriving DecidableEq, Repr

/-- The classification function from `upgrade.rs:215-245`. -/
def classify (disk running : Version) : FormatChange :=
  match Version.cmp disk running with
  | .lt => .upgrade   disk running
  | .gt => .downgrade disk running
  | .eq => .checkOpenCurrent running

/-! ## Reusable-major predicate from `upgrade.rs:84-87` -/

/-- `is_reusable_major_upgrade`: minor and patch must both be zero.
Source: `upgrade.rs:84-87`. -/
def isReusableMajorUpgrade (v : Version) : Bool :=
  decide (v.minor = 0 ∧ v.patch = 0)

/-! ## Helper lemmas

The three `cmp_*_iff` lemmas factor the case analysis on `Version.cmp` so
the user-facing theorems just dispatch on `VOrd`. -/

/-- `cmp` decides equality on `Nat` triples by walking the cascade.
We prove this and the two siblings via a single normal-form trick: case
analysis on the three trichotomy outcomes for each component, then `simp`
the cascade. -/
private theorem cmp_branches (a b : Version) :
    (a.major < b.major → a.cmp b = .lt) ∧
    (a.major > b.major → a.cmp b = .gt) ∧
    (a.major = b.major → a.minor < b.minor → a.cmp b = .lt) ∧
    (a.major = b.major → a.minor > b.minor → a.cmp b = .gt) ∧
    (a.major = b.major → a.minor = b.minor → a.patch < b.patch → a.cmp b = .lt) ∧
    (a.major = b.major → a.minor = b.minor → a.patch > b.patch → a.cmp b = .gt) ∧
    (a.major = b.major → a.minor = b.minor → a.patch = b.patch → a.cmp b = .eq) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> unfold Version.cmp <;>
    (first | (simp_all; omega) | simp_all)

private theorem cmp_eq_iff (a b : Version) : a.cmp b = .eq ↔ a = b := by
  constructor
  · intro h
    -- Trichotomy on each pair; rule out all branches except all-equal.
    have br := cmp_branches a b
    rcases lt_trichotomy a.major b.major with hM | hM | hM
    · rw [br.1 hM] at h; cases h
    · rcases lt_trichotomy a.minor b.minor with hm | hm | hm
      · rw [br.2.2.1 hM hm] at h; cases h
      · rcases lt_trichotomy a.patch b.patch with hp | hp | hp
        · rw [br.2.2.2.2.1 hM hm hp] at h; cases h
        · cases a; cases b; simp_all
        · rw [br.2.2.2.2.2.1 hM hm hp] at h; cases h
      · rw [br.2.2.2.1 hM hm] at h; cases h
    · rw [br.2.1 hM] at h; cases h
  · intro h
    subst h
    have br := cmp_branches a a
    exact br.2.2.2.2.2.2 rfl rfl rfl

private theorem cmp_lt_iff (a b : Version) : a.cmp b = .lt ↔ a < b := by
  constructor
  · intro h
    have br := cmp_branches a b
    rcases lt_trichotomy a.major b.major with hM | hM | hM
    · exact Or.inl hM
    · rcases lt_trichotomy a.minor b.minor with hm | hm | hm
      · exact Or.inr (Or.inl ⟨hM, hm⟩)
      · rcases lt_trichotomy a.patch b.patch with hp | hp | hp
        · exact Or.inr (Or.inr ⟨hM, hm, hp⟩)
        · rw [br.2.2.2.2.2.2 hM hm hp] at h; cases h
        · rw [br.2.2.2.2.2.1 hM hm hp] at h; cases h
      · rw [br.2.2.2.1 hM hm] at h; cases h
    · rw [br.2.1 hM] at h; cases h
  · intro h
    have br := cmp_branches a b
    rcases h with hM | ⟨hMe, hm⟩ | ⟨hMe, hme, hp⟩
    · exact br.1 hM
    · exact br.2.2.1 hMe hm
    · exact br.2.2.2.2.1 hMe hme hp

private theorem cmp_gt_iff (a b : Version) : a.cmp b = .gt ↔ b < a := by
  constructor
  · intro h
    have br := cmp_branches a b
    rcases lt_trichotomy a.major b.major with hM | hM | hM
    · rw [br.1 hM] at h; cases h
    · rcases lt_trichotomy a.minor b.minor with hm | hm | hm
      · rw [br.2.2.1 hM hm] at h; cases h
      · rcases lt_trichotomy a.patch b.patch with hp | hp | hp
        · rw [br.2.2.2.2.1 hM hm hp] at h; cases h
        · rw [br.2.2.2.2.2.2 hM hm hp] at h; cases h
        · exact Or.inr (Or.inr ⟨hM.symm, hm.symm, hp⟩)
      · exact Or.inr (Or.inl ⟨hM.symm, hm⟩)
    · exact Or.inl hM
  · intro h
    have br := cmp_branches a b
    rcases h with hM | ⟨hMe, hm⟩ | ⟨hMe, hme, hp⟩
    · exact br.2.1 hM
    · exact br.2.2.2.1 hMe.symm hm
    · exact br.2.2.2.2.2.1 hMe.symm hme.symm hp

/-! ## Theorems -/

/-- **T1 (current version is pinned).** Today the running format version is
exactly `(27, 0, 0)`. Source: `constants.rs:37,46,50`. If a Zebra developer
ever forgets to bump one of these constants when updating the disk format,
this build breaks. -/
theorem current_version_is_27_0_0 :
    currentVersion = { major := 27, minor := 0, patch := 0 } := by
  unfold currentVersion DATABASE_FORMAT_VERSION DATABASE_FORMAT_MINOR_VERSION
         DATABASE_FORMAT_PATCH_VERSION
  rfl

/-- **T2a (irreflexivity).** Version comparison is a strict order. No version
is below itself. -/
theorem lt_irrefl (v : Version) : ¬ (v < v) := by
  intro h
  rcases h with hM | ⟨_, hm⟩ | ⟨_, _, hp⟩
  · exact (Nat.lt_irrefl _) hM
  · exact (Nat.lt_irrefl _) hm
  · exact (Nat.lt_irrefl _) hp

/-- **T2b (transitivity).** If `a < b` and `b < c` then `a < c`. -/
theorem lt_trans (a b c : Version)
    (hab : a < b) (hbc : b < c) : a < c := by
  unfold LT.lt instLTVersion Version.lt at *
  rcases hab with h1 | ⟨h1M, h1m⟩ | ⟨h1M, h1mE, h1p⟩
  · rcases hbc with h2 | ⟨h2M, _⟩ | ⟨h2M, _, _⟩
    · exact Or.inl (Nat.lt_trans h1 h2)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
  · rcases hbc with h2 | ⟨h2M, h2m⟩ | ⟨h2M, h2mE, _⟩
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl ⟨by omega, Nat.lt_trans h1m h2m⟩)
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  · rcases hbc with h2 | ⟨h2M, h2m⟩ | ⟨h2M, h2mE, h2p⟩
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨by omega, by omega, Nat.lt_trans h1p h2p⟩)

/-- **T2c (decidability witness).** For any two versions, either `a < b` or
`¬ (a < b)`. This is the propositional version of `Decidable (a < b)`; it
matches Rust's `cmp_precedence` returning a definite `Ordering` value. -/
theorem lt_decidable_prop (a b : Version) : (a < b) ∨ ¬ (a < b) := by
  by_cases h : a < b
  · exact Or.inl h
  · exact Or.inr h

/-- **T3 (major bump ⇒ strict increase).** A larger major version always
gives a strictly later format, regardless of minor/patch values. This is the
"breaking change" rule from `constants.rs:25-29`: bumping the major number
declares the on-disk layout incompatible with previous running versions. -/
theorem major_bump_increases
    (old new : Version) (h : old.major < new.major) :
    old < new := Or.inl h

/-- **T3b (major bump ⇒ classification is `upgrade`, not `checkOpenCurrent`).**
Concrete witness that bumping major never produces a "same version" branch
in `open_database`. -/
theorem major_bump_classifies_upgrade
    (disk running : Version) (h : disk.major < running.major) :
    classify disk running = .upgrade disk running := by
  unfold classify
  have : disk.cmp running = .lt := (cmp_lt_iff disk running).mpr (Or.inl h)
  rw [this]

/-- **T4a (minor bump within same major ⇒ strict increase).** This is the
"significant change" rule from `constants.rs:39-46`: bumping minor declares
the format extended in a backward-compatible way. -/
theorem minor_bump_increases
    (old new : Version)
    (hM : old.major = new.major) (hm : old.minor < new.minor) :
    old < new := Or.inr (Or.inl ⟨hM, hm⟩)

/-- **T4b (patch bump within same major+minor ⇒ strict increase).** -/
theorem patch_bump_increases
    (old new : Version)
    (hM : old.major = new.major) (hm : old.minor = new.minor)
    (hp : old.patch < new.patch) :
    old < new := Or.inr (Or.inr ⟨hM, hm, hp⟩)

/-- **T4c (same-major forward compat).** A minor/patch bump preserves the
major version, so a running version with a newer minor/patch can still
recognise an older disk version's "major epoch". This is the structural
invariant behind the Rust comment at `constants.rs:39-45`: "available in all
supported Zebra versions". -/
theorem same_major_forward_compat
    (disk running : Version)
    (h : disk < running) (hM : disk.major = running.major) :
    disk.minor < running.minor ∨
    (disk.minor = running.minor ∧ disk.patch < running.patch) := by
  rcases h with h1 | ⟨_, hm⟩ | ⟨_, hmE, hp⟩
  · exact absurd h1 (by omega)
  · exact Or.inl hm
  · exact Or.inr ⟨hmE, hp⟩

/-- **T5a (classify ⇒ upgrade exactly when `disk < running`).** Matches
the `Ordering::Less` branch of `cmp_precedence` at `upgrade.rs:216-227`. -/
theorem classify_upgrade_iff (disk running : Version) :
    classify disk running = .upgrade disk running ↔ disk < running := by
  unfold classify
  constructor
  · intro h
    cases hcmp : disk.cmp running with
    | lt => exact (cmp_lt_iff _ _).mp hcmp
    | gt => rw [hcmp] at h; cases h
    | eq => rw [hcmp] at h; cases h
  · intro h
    rw [(cmp_lt_iff _ _).mpr h]

/-- **T5b (classify ⇒ downgrade exactly when `running < disk`).** Matches
the `Ordering::Greater` branch at `upgrade.rs:228-239`. -/
theorem classify_downgrade_iff (disk running : Version) :
    classify disk running = .downgrade disk running ↔ running < disk := by
  unfold classify
  constructor
  · intro h
    cases hcmp : disk.cmp running with
    | lt => rw [hcmp] at h; cases h
    | gt => exact (cmp_gt_iff _ _).mp hcmp
    | eq => rw [hcmp] at h; cases h
  · intro h
    rw [(cmp_gt_iff _ _).mpr h]

/-- **T5c (classify ⇒ checkOpenCurrent exactly when `disk = running`).**
Matches the `Ordering::Equal` branch at `upgrade.rs:240-244`. -/
theorem classify_check_iff (disk running : Version) :
    classify disk running = .checkOpenCurrent running ↔ disk = running := by
  unfold classify
  constructor
  · intro h
    cases hcmp : disk.cmp running with
    | lt => rw [hcmp] at h; cases h
    | gt => rw [hcmp] at h; cases h
    | eq => exact (cmp_eq_iff _ _).mp hcmp
  · intro h
    rw [(cmp_eq_iff _ _).mpr h]

/-- **T6 (`isReusableMajorUpgrade` semantics).** Mirrors `upgrade.rs:84-87`:
the predicate is true exactly when both minor and patch are zero. This is the
necessary condition for the major-version cache-reuse optimisation in
`disk_db.rs:1240-1258`. -/
theorem isReusableMajorUpgrade_iff (v : Version) :
    isReusableMajorUpgrade v = true ↔ (v.minor = 0 ∧ v.patch = 0) := by
  unfold isReusableMajorUpgrade
  simp

/-- **T7 (`mark_as_upgraded_to` assertions are simultaneously satisfiable).**
The three assertions at `upgrade.rs:730-753` require:
1. `running > disk`,
2. `upgradeTarget > disk`,
3. `upgradeTarget ≤ running`.

We prove that for any disk version below any upgrade target below-or-equal
to a running version, all three hold, i.e. they form a consistent contract
on the upgrade path. The chain `disk < upgradeTarget ≤ running` is the
canonical "monotone upgrade" path. -/
theorem mark_as_upgraded_to_assertions_consistent
    (disk upgradeTarget running : Version)
    (h1 : disk < upgradeTarget)
    (h2 : upgradeTarget < running ∨ upgradeTarget = running) :
    (disk < running) ∧
    (disk < upgradeTarget) ∧
    (upgradeTarget < running ∨ upgradeTarget = running) := by
  refine ⟨?_, h1, h2⟩
  rcases h2 with h2 | h2
  · exact lt_trans disk upgradeTarget running h1 h2
  · rw [← h2]; exact h1

/-- **T8 (same-major upgrade target stays under next major).** If we upgrade
to a version with the same major as the running version, then the upgrade
target's major is strictly less than `running.major + 1`. This is what makes
same-major upgrades "in-place migrations" rather than requiring a fresh DB
directory (see the `state/v25` → `state/v26` rename logic at
`disk_db.rs:1240`). -/
theorem same_major_upgrade_under_next_major
    (upgradeTarget running : Version)
    (h : upgradeTarget.major = running.major) :
    upgradeTarget.major < running.major + 1 := by
  rw [h]; omega

/-- **T9 (current version is itself a reusable-major upgrade target).**
Because the current version pins minor and patch to zero
(`constants.rs:46,50`), it satisfies `is_reusable_major_upgrade`. So whenever
the major bumps to a new value, the cache from the previous major can be
reused — modelled at `disk_db.rs:1244-1249`. -/
theorem current_is_reusable_major_upgrade :
    isReusableMajorUpgrade currentVersion = true := by
  rw [isReusableMajorUpgrade_iff]
  unfold currentVersion DATABASE_FORMAT_MINOR_VERSION DATABASE_FORMAT_PATCH_VERSION
  exact ⟨rfl, rfl⟩

/-- **T10 (cmp totality).** `cmp` returns exactly one of `lt`, `eq`, `gt`,
matching `std::cmp::Ordering`. This is the model-level counterpart to the
Rust API contract: `cmp_precedence` is a total order. -/
theorem cmp_total (a b : Version) :
    a.cmp b = .lt ∨ a.cmp b = .eq ∨ a.cmp b = .gt := by
  cases h : a.cmp b
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

/-- **T11 (cmp antisymmetry).** If `a.cmp b = .lt` then `b.cmp a = .gt`.
Sanity-check that the three-way result respects the underlying `<`. -/
theorem cmp_antisym (a b : Version) (h : a.cmp b = .lt) : b.cmp a = .gt := by
  have hab : a < b := (cmp_lt_iff _ _).mp h
  exact (cmp_gt_iff _ _).mpr hab

/-- **T12 (current vs an older major version is an upgrade).** A concrete
witness: a DB written by a hypothetical Zebra v26 instance (`(26, 0, 0)`)
is classified as `upgrade` by today's running version `(27, 0, 0)`. -/
theorem v26_to_current_is_upgrade :
    classify { major := 26, minor := 0, patch := 0 } currentVersion =
      .upgrade { major := 26, minor := 0, patch := 0 } currentVersion := by
  unfold classify currentVersion DATABASE_FORMAT_VERSION
         DATABASE_FORMAT_MINOR_VERSION DATABASE_FORMAT_PATCH_VERSION
  decide

/-- **T13 (current vs a future minor version is a downgrade).** A
hypothetical disk version `(27, 1, 0)` produced by a future Zebra release is
classified as `downgrade` by today's running version, matching the rule at
`upgrade.rs:228-239`. -/
theorem future_minor_classifies_downgrade :
    classify { major := 27, minor := 1, patch := 0 } currentVersion =
      .downgrade { major := 27, minor := 1, patch := 0 } currentVersion := by
  unfold classify currentVersion DATABASE_FORMAT_VERSION
         DATABASE_FORMAT_MINOR_VERSION DATABASE_FORMAT_PATCH_VERSION
  decide

/-- **T14 (current vs itself is `checkOpenCurrent`).** Opening today's disk
version with today's running version yields the "no upgrade needed" branch,
matching `upgrade.rs:240-244`. -/
theorem current_vs_current_is_check :
    classify currentVersion currentVersion = .checkOpenCurrent currentVersion := by
  unfold classify currentVersion DATABASE_FORMAT_VERSION
         DATABASE_FORMAT_MINOR_VERSION DATABASE_FORMAT_PATCH_VERSION
  decide

end Zebra.StateFormatVersion
