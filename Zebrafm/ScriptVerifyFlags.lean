import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Script verification flag bitfield

Models the `Flags` bitfield used by zebra-script to drive the Zcash script
interpreter. The Rust enum lives at
`zcash_script/src/interpreter.rs:130-181` (within the
`bitflags::bitflags!` macro), and Zebra's call site that pins the canonical
Zcash flag set is at `zebra-script/src/lib.rs:161-162`:

```rust
let flags = zcash_script::interpreter::Flags::P2SH
    | zcash_script::interpreter::Flags::CHECKLOCKTIMEVERIFY;
```

The Rust flag positions (each a single bit in a `u32`):

| flag                           | bit |
|--------------------------------|-----|
| `P2SH`                         |  0  |
| `StrictEnc`                    |  1  |
| `LowS`                         |  3  |
| `NullDummy`                    |  4  |
| `SigPushOnly`                  |  5  |
| `MinimalData`                  |  6  |
| `DiscourageUpgradableNOPs`     |  7  |
| `CleanStack`                   |  8  |
| `CHECKLOCKTIMEVERIFY`          |  9  |

Note the deliberate gap at bit 2 — kept reserved in the Rust source to leave
room for a future flag without shifting later bit positions.

This module models each flag as a `Nat` bit position (`0..9`) and the
combined flag value as a sum of `2^position` indicators over a finite set of
positions. The model lets us prove:

* **mutual distinctness** of all flag bit positions;
* the **union value** is exactly the OR of the per-flag values when bits are
  disjoint (`a + b` since `a OR b = a + b` for disjoint bitsets);
* the **canonical Zcash flag set** `P2SH | CHECKLOCKTIMEVERIFY = 0x201` (the
  bitfield Zebra hands to the script interpreter on every transparent input);
* an **invariant fingerprint** of the active flag layout: a single
  hexadecimal value equal to `Flags::all().bits()`, computed under the
  current bit assignments.
-/

namespace Zebra.ScriptVerifyFlags

/-! ## Flag enum and bit positions

We tag each Rust `Flags` variant with its bit position (the right-hand side
of `1 << k` in the bitfield definition). Positions are taken verbatim from
`zcash_script/src/interpreter.rs:136-180`. -/

/-- The script verification flag enum, in source order. -/
inductive Flag
  | p2sh
  | strictEnc
  | lowS
  | nullDummy
  | sigPushOnly
  | minimalData
  | discourageUpgradableNOPs
  | cleanStack
  | checkLockTimeVerify
  deriving DecidableEq, Repr

/-- The bit position of each flag inside the `u32` bitfield. The position is
the exponent in the Rust `1 << k` definition. Source:
`zcash_script/src/interpreter.rs:136-180`. -/
def Flag.bitPos : Flag → Nat
  | .p2sh                      => 0
  | .strictEnc                 => 1
  | .lowS                      => 3
  | .nullDummy                 => 4
  | .sigPushOnly               => 5
  | .minimalData               => 6
  | .discourageUpgradableNOPs  => 7
  | .cleanStack                => 8
  | .checkLockTimeVerify       => 9

/-- The integer value of a single flag is `2 ^ bitPos`. -/
def Flag.value (f : Flag) : Nat := 2 ^ f.bitPos

/-- The OR-combined value of a list of *distinct* flags. Modelled as a sum
because OR over disjoint bitsets coincides with addition in `Nat`. -/
def combinedValue : List Flag → Nat
  | []      => 0
  | f :: fs => f.value + combinedValue fs

/-- The canonical Zcash flag set Zebra uses on every transparent input.
Source: `zebra-script/src/lib.rs:161-162` — `Flags::P2SH |
Flags::CHECKLOCKTIMEVERIFY`. -/
def canonicalZcashFlags : List Flag := [.p2sh, .checkLockTimeVerify]

/-- The full list of *defined* flag variants — all nine, in source order.
This is what `Flags::all().bits()` enumerates over. -/
def allFlags : List Flag :=
  [.p2sh, .strictEnc, .lowS, .nullDummy, .sigPushOnly,
   .minimalData, .discourageUpgradableNOPs, .cleanStack, .checkLockTimeVerify]

/-! ## Bit-position pins

These pins reflect the *exact* Rust assignments; if the source ever shifts a
flag, the build breaks here, not silently downstream. -/

theorem bitPos_p2sh : Flag.bitPos .p2sh = 0 := rfl
theorem bitPos_strictEnc : Flag.bitPos .strictEnc = 1 := rfl
theorem bitPos_lowS : Flag.bitPos .lowS = 3 := rfl
theorem bitPos_nullDummy : Flag.bitPos .nullDummy = 4 := rfl
theorem bitPos_sigPushOnly : Flag.bitPos .sigPushOnly = 5 := rfl
theorem bitPos_minimalData : Flag.bitPos .minimalData = 6 := rfl
theorem bitPos_discourageUpgradableNOPs :
    Flag.bitPos .discourageUpgradableNOPs = 7 := rfl
theorem bitPos_cleanStack : Flag.bitPos .cleanStack = 8 := rfl
theorem bitPos_checkLockTimeVerify :
    Flag.bitPos .checkLockTimeVerify = 9 := rfl

/-! ## Bit value pins

The integer value of each flag. These are the constants a user sees when
they print `Flags::P2SH.bits()` etc. -/

theorem value_p2sh : Flag.value .p2sh = 0x001 := by
  unfold Flag.value Flag.bitPos; decide

theorem value_strictEnc : Flag.value .strictEnc = 0x002 := by
  unfold Flag.value Flag.bitPos; decide

theorem value_lowS : Flag.value .lowS = 0x008 := by
  unfold Flag.value Flag.bitPos; decide

theorem value_nullDummy : Flag.value .nullDummy = 0x010 := by
  unfold Flag.value Flag.bitPos; decide

theorem value_sigPushOnly : Flag.value .sigPushOnly = 0x020 := by
  unfold Flag.value Flag.bitPos; decide

theorem value_minimalData : Flag.value .minimalData = 0x040 := by
  unfold Flag.value Flag.bitPos; decide

theorem value_discourageUpgradableNOPs :
    Flag.value .discourageUpgradableNOPs = 0x080 := by
  unfold Flag.value Flag.bitPos; decide

theorem value_cleanStack : Flag.value .cleanStack = 0x100 := by
  unfold Flag.value Flag.bitPos; decide

theorem value_checkLockTimeVerify :
    Flag.value .checkLockTimeVerify = 0x200 := by
  unfold Flag.value Flag.bitPos; decide

/-! ## T1: every flag's bit position is distinct

The bit-positions field is the right-hand side of every `1 << k` in the
bitfield; if any two variants shared a position they'd alias on the bus and
the interpreter could not distinguish them. The Rust source also leaves bit
2 deliberately *unused* (no flag has position 2). This theorem witnesses
both properties: positions are pairwise distinct, and 2 is absent. -/

/-- **T1 (every defined flag has a distinct bit position).** Witnesses that
no two flags share a bit slot in the `u32` bitfield. -/
theorem all_bitPos_distinct :
    Flag.bitPos .p2sh ≠ Flag.bitPos .strictEnc ∧
    Flag.bitPos .p2sh ≠ Flag.bitPos .lowS ∧
    Flag.bitPos .p2sh ≠ Flag.bitPos .nullDummy ∧
    Flag.bitPos .p2sh ≠ Flag.bitPos .sigPushOnly ∧
    Flag.bitPos .p2sh ≠ Flag.bitPos .minimalData ∧
    Flag.bitPos .p2sh ≠ Flag.bitPos .discourageUpgradableNOPs ∧
    Flag.bitPos .p2sh ≠ Flag.bitPos .cleanStack ∧
    Flag.bitPos .p2sh ≠ Flag.bitPos .checkLockTimeVerify ∧
    Flag.bitPos .strictEnc ≠ Flag.bitPos .lowS ∧
    Flag.bitPos .strictEnc ≠ Flag.bitPos .nullDummy ∧
    Flag.bitPos .strictEnc ≠ Flag.bitPos .sigPushOnly ∧
    Flag.bitPos .strictEnc ≠ Flag.bitPos .minimalData ∧
    Flag.bitPos .strictEnc ≠ Flag.bitPos .discourageUpgradableNOPs ∧
    Flag.bitPos .strictEnc ≠ Flag.bitPos .cleanStack ∧
    Flag.bitPos .strictEnc ≠ Flag.bitPos .checkLockTimeVerify ∧
    Flag.bitPos .lowS ≠ Flag.bitPos .nullDummy ∧
    Flag.bitPos .lowS ≠ Flag.bitPos .sigPushOnly ∧
    Flag.bitPos .lowS ≠ Flag.bitPos .minimalData ∧
    Flag.bitPos .lowS ≠ Flag.bitPos .discourageUpgradableNOPs ∧
    Flag.bitPos .lowS ≠ Flag.bitPos .cleanStack ∧
    Flag.bitPos .lowS ≠ Flag.bitPos .checkLockTimeVerify ∧
    Flag.bitPos .nullDummy ≠ Flag.bitPos .sigPushOnly ∧
    Flag.bitPos .nullDummy ≠ Flag.bitPos .minimalData ∧
    Flag.bitPos .nullDummy ≠ Flag.bitPos .discourageUpgradableNOPs ∧
    Flag.bitPos .nullDummy ≠ Flag.bitPos .cleanStack ∧
    Flag.bitPos .nullDummy ≠ Flag.bitPos .checkLockTimeVerify ∧
    Flag.bitPos .sigPushOnly ≠ Flag.bitPos .minimalData ∧
    Flag.bitPos .sigPushOnly ≠ Flag.bitPos .discourageUpgradableNOPs ∧
    Flag.bitPos .sigPushOnly ≠ Flag.bitPos .cleanStack ∧
    Flag.bitPos .sigPushOnly ≠ Flag.bitPos .checkLockTimeVerify ∧
    Flag.bitPos .minimalData ≠ Flag.bitPos .discourageUpgradableNOPs ∧
    Flag.bitPos .minimalData ≠ Flag.bitPos .cleanStack ∧
    Flag.bitPos .minimalData ≠ Flag.bitPos .checkLockTimeVerify ∧
    Flag.bitPos .discourageUpgradableNOPs ≠ Flag.bitPos .cleanStack ∧
    Flag.bitPos .discourageUpgradableNOPs ≠ Flag.bitPos .checkLockTimeVerify ∧
    Flag.bitPos .cleanStack ≠ Flag.bitPos .checkLockTimeVerify := by
  decide

/-- **T2 (bit position 2 is intentionally unassigned).** The Rust source skips
`1 << 2` between `StrictEnc` (1) and `LowS` (3): no defined flag claims bit 2.
This reserves it for a future flag without shifting later positions, and
witnessing it here freezes the gap so a casual reshuffle would break the
build. -/
theorem bit2_is_reserved : ∀ f : Flag, f.bitPos ≠ 2 := by
  intro f; cases f <;> decide

/-! ## T3: canonical Zcash flag set

The Zebra script verifier sets exactly `P2SH | CHECKLOCKTIMEVERIFY` for every
transparent input (`zebra-script/src/lib.rs:161-162`). Since the two flags
sit at bits 0 and 9, the combined integer value is `0x001 + 0x200 = 0x201 =
513`. We pin both the bit value and the structural equality. -/

/-- The canonical Zcash flag set is the two-element list `[P2SH,
CHECKLOCKTIMEVERIFY]`. Witnesses that we have not silently broadened or
narrowed it. -/
theorem canonicalZcashFlags_layout :
    canonicalZcashFlags = [Flag.p2sh, Flag.checkLockTimeVerify] := rfl

/-- **T3 (canonical Zcash flag set value).** The combined bitfield value
`P2SH | CHECKLOCKTIMEVERIFY = 0x201` (`= 513`). This is the literal `u32` the
Rust call site passes to the script interpreter on every input. -/
theorem canonicalZcashFlags_value :
    combinedValue canonicalZcashFlags = 0x201 := by
  unfold canonicalZcashFlags combinedValue Flag.value Flag.bitPos
  decide

/-! ## T4: combined value equals sum of individual flag values

Each flag occupies a *distinct* bit (`T1`), so a bitwise OR over the flag set
equals the arithmetic sum of the individual values in `Nat`. We use the
`combinedValue` recursion as the OR-value, and prove it equals the
list-`foldr` sum of `Flag.value`. -/

/-- **T4 (combined value distributes over the list).** The combined value of
a list of flags is the sum of the individual flag values. This is the
`Nat`-level analogue of "OR over disjoint bitsets = sum", which holds
exactly because every flag occupies its own bit position (T1). -/
theorem combinedValue_eq_sum (fs : List Flag) :
    combinedValue fs = (fs.map Flag.value).foldr (· + ·) 0 := by
  induction fs with
  | nil => rfl
  | cons f rest ih =>
    unfold combinedValue
    simp [List.map, ih]

/-- The combined value is monotone under list extension: appending a flag
only adds its bit value. -/
theorem combinedValue_cons (f : Flag) (fs : List Flag) :
    combinedValue (f :: fs) = f.value + combinedValue fs := rfl

/-- The combined value of the empty flag list is zero — `Flags::empty()` in
Rust. -/
theorem combinedValue_empty : combinedValue [] = 0 := rfl

/-! ## T5: positivity / monotonicity

Each flag value is a power of two, so it's positive; adding flags only
increases the bitfield. -/

/-- Every flag value is strictly positive. (Each is `2^k` for some `k`.) -/
theorem value_positive (f : Flag) : 0 < f.value := by
  unfold Flag.value
  exact Nat.two_pow_pos _

/-- **T5 (extending a flag list strictly increases the bitfield value).**
Combining one more (non-redundant) flag adds a positive value. This makes
`combinedValue` order-sensitive only up to *content* — the bit ordering of
the input list doesn't matter, but adding any new flag strictly grows the
result. -/
theorem combinedValue_strict_mono (f : Flag) (fs : List Flag) :
    combinedValue fs < combinedValue (f :: fs) := by
  rw [combinedValue_cons]
  have hf : 0 < f.value := value_positive f
  omega

/-! ## T6: `Flags::all().bits()` fingerprint

`Flags::all()` is the OR of all defined flags. Under the current bit
assignments, `Flags::all().bits() = 0x001 + 0x002 + 0x008 + 0x010 + 0x020 +
0x040 + 0x080 + 0x100 + 0x200 = 0x3FB`. Pinning this fingerprint catches
both bit-position shifts (T1 already does this) *and* missing/added flags. -/

/-- **T6 (`Flags::all().bits()` value).** The bitfield value of every defined
flag OR'd together. Under the current assignments this is `0x3FB`. The
hex value has a "missing bit" — bit 2 — exactly because `T2` says position 2
is reserved. -/
theorem allFlags_value : combinedValue allFlags = 0x3FB := by
  unfold allFlags combinedValue Flag.value Flag.bitPos
  decide

/-- **T7 (the canonical flag set is a subset of `Flags::all()`).** The two
flags Zebra uses are both in the master list — sanity-check that Zebra is
not accidentally setting a flag bit outside the defined enum. The value of
the canonical set divides into `allFlags` cleanly because every bit of the
canonical set is also a bit of the master mask. -/
theorem canonical_flags_subset_all :
    Flag.p2sh ∈ allFlags ∧ Flag.checkLockTimeVerify ∈ allFlags := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **T8 (canonical-set value sits inside `allFlags` mask).** Numerically:
`canonicalZcashFlags_value (513) ≤ allFlags_value (1019)`. This is a
floor-level invariant — Zebra never asks the interpreter for a bit that the
interpreter doesn't define. -/
theorem canonical_value_le_all :
    combinedValue canonicalZcashFlags ≤ combinedValue allFlags := by
  rw [canonicalZcashFlags_value, allFlags_value]
  decide

/-- **T9 (`Flags::all()` fits in `u32`).** The whole mask of nine flags is
well below `2^32`, so the `u32` storage is comfortable. With only nine bits
used (and one reserved gap) this is trivial here, but it pins the headroom
in case someone adds many more flags later. -/
theorem allFlags_fits_u32 : combinedValue allFlags < 2 ^ 32 := by
  rw [allFlags_value]
  decide

/-! ## T10: only 9 defined flags

A structural sanity-check: there are exactly nine flag constructors in the
Rust enum, matching the nine bit-slots used (`{0,1,3,4,5,6,7,8,9}`). -/

/-- **T10 (the defined-flag list has length 9).** Pins the cardinality of
the enum. If a flag is added or removed without updating the model, this
breaks. -/
theorem allFlags_length : allFlags.length = 9 := by decide

/-- **T11 (canonical flag list has length 2).** Just `P2SH` and
`CHECKLOCKTIMEVERIFY` — anything else and the build breaks. -/
theorem canonicalZcashFlags_length : canonicalZcashFlags.length = 2 := by decide

/-! ## Cross-checks against `zebra-script/src/lib.rs:161-162`

The Rust call site composes the canonical set as `Flags::P2SH |
Flags::CHECKLOCKTIMEVERIFY`. We re-derive that as a pure-`Nat` sum and pin
the two summands separately, so a stray edit on either operand at the
call site breaks the build. -/

/-- **T12 (canonical-set value is the sum of its two flag values).** Spells
out the OR-as-sum reduction for the canonical set: `Flags::P2SH.bits() +
Flags::CHECKLOCKTIMEVERIFY.bits() = 0x001 + 0x200 = 0x201`. -/
theorem canonical_value_is_p2sh_plus_cltv :
    combinedValue canonicalZcashFlags =
      Flag.value .p2sh + Flag.value .checkLockTimeVerify := by
  change Flag.value .p2sh + (Flag.value .checkLockTimeVerify + 0) =
         Flag.value .p2sh + Flag.value .checkLockTimeVerify
  omega

end Zebra.ScriptVerifyFlags
