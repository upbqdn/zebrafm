import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# CompactDifficulty from `zebra-chain/src/work/difficulty.rs`

The Bitcoin/Zcash 32-bit "compact bits" difficulty target encoding. The 32-bit
word is laid out as:

```text
  bits 31..24: 8-bit exponent byte ("size")
  bits 23..23: signed-mantissa sign bit (rejected if set)
  bits 22..0:  23-bit unsigned mantissa
```

The Rust exponent variable in `to_expanded` is computed as
`exponent = (self.0 >> 24) - OFFSET` with `OFFSET = 3`. So **exponent**
`e = sizeByte - 3`. The Rust normalisation match (`difficulty.rs:217-234`) is
keyed on `e`, not on `sizeByte`:

```text
  e ≥ 32   ⟷  sizeByte ≥ 35        → reject (overflow)
  e = 31   ⟷  sizeByte = 34         → shift `m << 16`, e' = 29
  e = 30   ⟷  sizeByte = 33         → shift `m << 8`,  e' = 29
  e < 0    ⟷  sizeByte ∈ {0, 1, 2}  → shift `m >> (|e|*8)`, e' = 0
  otherwise (0 ≤ e ≤ 29 i.e. sizeByte ∈ [3, 32]) → no shift
```

In particular the **no-shift** canonical range is `sizeByte ∈ [3, 32]`
(equivalently `e ∈ [0, 29]`), and on that range the expanded target is the
clean formula

```text
  to_expanded(c) = mantissa × 256^(sizeByte - 3)
```

For the inverse direction (`ExpandedDifficulty::to_compact`, line 460), the
Rust pipeline computes `size = bits/8 + 1`, then shifts the mantissa to fit
`UNSIGNED_MANTISSA_MASK`, then assembles the compact word as
`mantissa + (size << 24)`. Modelling `bits()` requires a `Nat → bit-length`
function; here we factor out the **bit-packing** stage (the final assembly) and
model the conditional shift through the `expanded → (mantissa, sizeByte)`
helper functions. The full Rust pipeline is exposed via
`toExpandedFullModel` and the partial inverse via `assembleCompact`.

We model:
  * `CompactDifficulty` as a `Nat` with the implicit invariant `< 2^32`;
  * the expanded target as a `Nat` (it can grow up to `≈ 2^248` but `Nat` is
    unbounded, so this is faithful);
  * `toExpanded` as a `Nat`-valued helper for the **canonical no-shift range**
    (`sizeByte ∈ [3, 32]`, sign bit clear) — equivalent to Rust's match arm
    `(m, e) => (m, e)`;
  * `toExpandedFullModel` as the full Rust pipeline, faithfully mirroring all
    five match arms (overflow reject, e=31 shift, e=30 shift, e<0 shift,
    identity);
  * `assembleCompact` as the bit-packing step `mantissa + (size << 24)` — this
    is **not** the Rust end-to-end `ExpandedDifficulty::to_compact`, which
    additionally derives `size` from the bit-length and conditionally shifts.
    It is the final assembly step of that pipeline (line 501).

Source: `zebra-chain/src/work/difficulty.rs:159` (`impl CompactDifficulty`),
        `zebra-chain/src/work/difficulty.rs:186` (`pub fn to_expanded`),
        `zebra-chain/src/work/difficulty.rs:460` (`pub fn to_compact`).
-/

namespace Zebra.CompactDifficulty

/-! ## Layout constants -/

/-- Exponent base: 256.
Source: `zebra-chain/src/work/difficulty.rs:161` -/
def BASE : Nat := 256

/-- Exponent offset: 3.
Source: `zebra-chain/src/work/difficulty.rs:164` -/
def OFFSET : Nat := 3

/-- Floating-point precision (mantissa width): 24 bits including sign.
Source: `zebra-chain/src/work/difficulty.rs:167` -/
def PRECISION : Nat := 24

/-- Sign bit of the signed mantissa: `1 << (PRECISION - 1) = 2^23`.
Source: `zebra-chain/src/work/difficulty.rs:170` -/
def SIGN_BIT : Nat := 2 ^ 23

/-- Unsigned mantissa mask / max value: `SIGN_BIT - 1 = 2^23 - 1`.
Source: `zebra-chain/src/work/difficulty.rs:175` -/
def UNSIGNED_MANTISSA_MASK : Nat := 2 ^ 23 - 1

/-- Upper bound on the compact word: `2^32`. -/
def U32_LIMIT : Nat := 2 ^ 32

/-! ## Field accessors -/

/-- The size byte (exponent byte): the top 8 bits of the compact word.
Source: `zebra-chain/src/work/difficulty.rs:211` (`self.0 >> PRECISION`) -/
def sizeByte (c : Nat) : Nat := c / 2 ^ 24

/-- The 23-bit unsigned mantissa: the low 23 bits of the compact word.
Source: `zebra-chain/src/work/difficulty.rs:205` (`self.0 & UNSIGNED_MANTISSA_MASK`) -/
def mantissa (c : Nat) : Nat := c % SIGN_BIT

/-- The sign-bit predicate: true iff bit 23 of the compact word is set.
Source: `zebra-chain/src/work/difficulty.rs:198` (`self.0 & SIGN_BIT == SIGN_BIT`) -/
def signBitSet (c : Nat) : Bool := (c / SIGN_BIT) % 2 = 1

/-- A compact value is **canonically encoded** iff:
  * the word fits in 32 bits,
  * the sign bit is clear,
  * `sizeByte ∈ [OFFSET, 32]`, i.e. exponent `e = sizeByte - OFFSET ∈ [0, 29]`.

The upper bound `32` is the largest size byte for which Rust's
`to_expanded` takes the **identity** match arm (`(m, e) => (m, e)`,
`difficulty.rs:233`) — no normalising shift is applied. Size bytes `33` and
`34` (i.e. exponent `30` and `31`) trigger the normalising shifts at
`difficulty.rs:225,227`; size bytes `≥ 35` are rejected outright at
`difficulty.rs:221`.

(The previous version of this predicate used `sizeByte c ≤ 29` and an
incorrect docstring claiming "normalisation fires at size bytes 30, 31".
That conflated size bytes with the exponent variable; the normalisation in
Rust is keyed on exponent `e = sizeByte − 3`, so it fires at size bytes
33 and 34. See FINDINGS Finding 10.) -/
def isCanonical (c : Nat) : Prop :=
  c < U32_LIMIT ∧
  signBitSet c = false ∧
  OFFSET ≤ sizeByte c ∧
  sizeByte c ≤ 32

/-! ## Encoder and decoder -/

/-- `to_expanded` for a canonical no-shift compact value: `mantissa × 256^(size - 3)`.
Source: `zebra-chain/src/work/difficulty.rs:186` (`pub fn to_expanded`),
        no-shift arm at `difficulty.rs:233`. -/
def toExpanded (c : Nat) : Nat :=
  mantissa c * BASE ^ (sizeByte c - OFFSET)

/-- `Option`-wrapped `toExpanded`: returns `none` for the rejected (sign-bit-set)
encodings, and `none` for zero results. This matches the Rust early-return on
sign bit set and on zero result.
Source: `zebra-chain/src/work/difficulty.rs:198,243-247` -/
def toExpandedOpt (c : Nat) : Option Nat :=
  if signBitSet c then
    none
  else
    let e := toExpanded c
    if e = 0 then none else some e

/-- The full Rust `to_expanded` pipeline modelled as a function `Nat → Option Nat`.
This faithfully mirrors **all** five branches of the match at
`difficulty.rs:217-234`, indexed by the exponent variable
`e := sizeByte c - OFFSET`:

  * sign-bit set → `none` (early return, `difficulty.rs:198`),
  * `e ≥ 32` (`sizeByte ≥ 35`) → `none` (overflow reject, line 221),
  * `e = 31` (`sizeByte = 34`):
    - `mantissa > 0xff` → `none` (line 224),
    - `mantissa ≤ 0xff` → `some (mantissa * 256^16 * 256^29)` (line 225,
      which sets `(m', e') = (m << 16, e - 2) = (m << 16, 29)`),
  * `e = 30` (`sizeByte = 33`):
    - `mantissa > 0xffff` → `none` (line 226),
    - `mantissa ≤ 0xffff` → `some (mantissa * 256^8 * 256^29)` (line 227,
      which sets `(m', e') = (m << 8, e - 1) = (m << 8, 29)`),
  * `e < 0` (`sizeByte ∈ {0, 1, 2}`) → `some (mantissa >> (|e|*8))` with
    final `e' = 0` (line 232),
  * otherwise (canonical no-shift, `e ∈ [0, 29]`, `sizeByte ∈ [3, 32]`) →
    `some (mantissa * 256^(sizeByte - 3))` (line 233).

Followed by the zero-rejection at line 243–247. -/
def toExpandedFullModel (c : Nat) : Option Nat :=
  if signBitSet c then
    none
  else
    let m := mantissa c
    let s := sizeByte c
    -- e ≥ 32  ⟺  s ≥ 35
    if s ≥ 35 then
      none
    -- e = 31  ⟺  s = 34
    else if s = 34 then
      if m > 0xff then none
      else
        let v := (m * 2 ^ 16) * BASE ^ 29
        if v = 0 then none else some v
    -- e = 30  ⟺  s = 33
    else if s = 33 then
      if m > 0xffff then none
      else
        let v := (m * 2 ^ 8) * BASE ^ 29
        if v = 0 then none else some v
    -- e < 0  ⟺  s ∈ {0, 1, 2}
    else if s < OFFSET then
      let shiftBits := (OFFSET - s) * 8
      let v := m / 2 ^ shiftBits
      if v = 0 then none else some v
    -- canonical no-shift arm: s ∈ [3, 32]
    else
      let v := m * BASE ^ (s - OFFSET)
      if v = 0 then none else some v

/-- **`assembleCompact`:** the bit-packing step `mantissa + (size << 24)` from
`difficulty.rs:501`. This is **not** the full Rust
`ExpandedDifficulty::to_compact` pipeline (line 460): the Rust function
additionally derives `size = self.bits() / 8 + 1`, then conditionally shifts
the mantissa to fit in `UNSIGNED_MANTISSA_MASK`. This `assembleCompact`
function captures only the final assembly step, taking an already-prepared
`(mantissa, size)` pair.

The function was previously named `toCompact`, but that name oversold the
semantic match: the previous version skipped the bit-length derivation and
the conditional shift. Rename per FINDINGS Finding 9.

Source: `zebra-chain/src/work/difficulty.rs:501` (`mantissa + (size << 24)`). -/
def assembleCompact (m : Nat) (size : Nat) : Nat :=
  m + size * 2 ^ 24

/-! ## Algebraic lemmas -/

/-- The sign bit equals `2^23`. -/
theorem SIGN_BIT_eq : SIGN_BIT = 8388608 := by
  unfold SIGN_BIT; decide

/-- The unsigned mantissa mask equals `2^23 - 1 = 8388607`. -/
theorem UNSIGNED_MANTISSA_MASK_eq : UNSIGNED_MANTISSA_MASK = 8388607 := by
  unfold UNSIGNED_MANTISSA_MASK; decide

/-- `mantissa c < SIGN_BIT`: the mantissa always fits in 23 bits. -/
theorem mantissa_lt_sign_bit (c : Nat) : mantissa c < SIGN_BIT := by
  unfold mantissa SIGN_BIT
  exact Nat.mod_lt _ (by decide)

/-- `mantissa c ≤ UNSIGNED_MANTISSA_MASK`: the mantissa never exceeds the mask. -/
theorem mantissa_le_mask (c : Nat) : mantissa c ≤ UNSIGNED_MANTISSA_MASK := by
  have h := mantissa_lt_sign_bit c
  unfold SIGN_BIT UNSIGNED_MANTISSA_MASK at *
  omega

/-- For a `c < 2^32`, the size byte fits in 8 bits. -/
theorem sizeByte_lt_256 (c : Nat) (h : c < U32_LIMIT) : sizeByte c < 256 := by
  unfold sizeByte U32_LIMIT at *
  omega

/-! ## Theorems -/

/-- **T1 (decomposition).** For any compact word `c < 2^32`,
`c = mantissa c + (signBit ? SIGN_BIT : 0) + sizeByte c * 2^24`. This is the
arithmetic skeleton behind every other theorem in this module. -/
theorem decomposition (c : Nat) (_ : c < U32_LIMIT) :
    c = mantissa c + (if signBitSet c then SIGN_BIT else 0) + sizeByte c * 2 ^ 24 := by
  unfold mantissa sizeByte signBitSet SIGN_BIT U32_LIMIT at *
  by_cases hb : (c / 8388608) % 2 = 1
  · simp [hb]; omega
  · simp [hb]; omega

/-- **T2 (sign bit clear ⇒ mantissa is the low 24 bits' value).** When the sign
bit is clear, `mantissa c = c % 2^24`. -/
theorem mantissa_when_sign_clear (c : Nat) (hs : signBitSet c = false) :
    mantissa c = c % 2 ^ 24 := by
  unfold mantissa signBitSet SIGN_BIT at *
  simp at hs
  omega

/-- **T3 (bit-level decompose/recompose).** This is *not* the end-to-end
`toExpanded`/`ExpandedDifficulty::to_compact` round-trip — that would require
a `bits()` computation on the expanded `Nat`, which is out of scope for this
module. This theorem shows that for any compact word `c < 2^32` with the sign
bit clear, splitting `c` into its low-23-bit mantissa and high-8-bit size byte
and then recombining via `assembleCompact (mantissa c) (sizeByte c)` recovers
`c` exactly. It is the encoder/decoder consistency lemma at the bit level,
supporting T4–T7 below.
Source: `zebra-chain/src/work/difficulty.rs:198` (early-return on signed),
        `zebra-chain/src/work/difficulty.rs:205` (mantissa extraction),
        `zebra-chain/src/work/difficulty.rs:211` (size extraction). -/
theorem compact_decompose_recompose (c : Nat) (h : c < U32_LIMIT)
    (hs : signBitSet c = false) :
    assembleCompact (mantissa c) (sizeByte c) = c := by
  unfold assembleCompact
  have hd := decomposition c h
  simp [hs] at hd
  omega

/-- **T4 (the compact word reconstructed from `(mantissa, size)`).** Constructing
a compact value from a mantissa `< SIGN_BIT` and a size byte `< 256` then
extracting the components recovers `(m, s)`. -/
theorem assembleCompact_mantissa (m size : Nat) (hm : m < SIGN_BIT) :
    mantissa (assembleCompact m size) = m := by
  unfold mantissa assembleCompact SIGN_BIT at *
  have : (m + size * 2 ^ 24) % 2 ^ 23 = m % 2 ^ 23 := by
    have : size * 2 ^ 24 = (size * 2) * 2 ^ 23 := by ring
    rw [this, Nat.add_mul_mod_self_right]
  rw [this]
  exact Nat.mod_eq_of_lt hm

theorem assembleCompact_sizeByte (m size : Nat) (hm : m < 2 ^ 24) :
    sizeByte (assembleCompact m size) = size := by
  unfold sizeByte assembleCompact
  have hpow : (0 : Nat) < 2 ^ 24 := by decide
  rw [Nat.add_mul_div_right _ _ hpow, Nat.div_eq_of_lt hm, Nat.zero_add]

/-- **T5 (round-trip from `(mantissa, size)` to compact and back).** -/
theorem roundtrip_components (m size : Nat) (hm : m < SIGN_BIT) :
    mantissa (assembleCompact m size) = m ∧ sizeByte (assembleCompact m size) = size := by
  refine ⟨assembleCompact_mantissa m size hm, assembleCompact_sizeByte m size ?_⟩
  unfold SIGN_BIT at hm
  have : (2 : Nat) ^ 23 < 2 ^ 24 := by decide
  omega

/-- **T6 (sign bit clear after `assembleCompact` for a sub-`SIGN_BIT` mantissa).**
Because the mantissa is `< SIGN_BIT = 2^23`, the only contribution to bit 23
of the reconstructed word comes from `size * 2^24`, which is always even at
the bit-23 position. Therefore the sign bit is clear for any size byte. -/
theorem assembleCompact_sign_clear (m size : Nat) (hm : m < SIGN_BIT) :
    signBitSet (assembleCompact m size) = false := by
  unfold signBitSet assembleCompact SIGN_BIT at *
  -- (m + size * 2^24) / 2^23 = (m / 2^23) + size * 2
  have hkey : (m + size * 2 ^ 24) / 2 ^ 23 = m / 2 ^ 23 + size * 2 := by
    have h_eq : size * 2 ^ 24 = size * 2 * 2 ^ 23 := by ring
    rw [h_eq, Nat.add_mul_div_right _ _ (by decide : (0 : Nat) < 2 ^ 23)]
  rw [hkey]
  have hm' : m / 2 ^ 23 = 0 := Nat.div_eq_of_lt hm
  rw [hm', Nat.zero_add]
  -- Now we have (size * 2) % 2 = 1 ↔ False
  have : size * 2 % 2 = 0 := Nat.mul_mod_left _ 2
  simp [this]

/-- **T7 (full round-trip on canonical compact values).** Combining T3 and the
decomposition: round-tripping a canonically encoded compact value through
`(mantissa, sizeByte)` and `assembleCompact` is the identity. -/
theorem roundtrip_canonical (c : Nat) (hcan : isCanonical c) :
    assembleCompact (mantissa c) (sizeByte c) = c := by
  obtain ⟨h_lt, h_sign, _, _⟩ := hcan
  exact compact_decompose_recompose c h_lt h_sign

/-! ### A note on monotonicity

`toExpanded` is **not** monotone in the raw compact word `c`. Increasing `c`
by 1 may flip a low-mantissa bit (which raises the expanded target by `256^(size-3)`),
but it may also carry into the size byte (which raises the expanded target by
multiple orders of magnitude *and resets the mantissa to zero*). For example
`toExpanded 0x03ffffff = 0x7fffff * 256^0 = 0x7fffff` is larger than
`toExpanded 0x04000000 = 0 * 256^1 = 0`. So the implication
`c₁ ≤ c₂ → toExpanded c₁ ≤ toExpanded c₂` is **false** in general.

T8 (`toExpanded_mono_mantissa`) and T9 (`toExpanded_mono_size`) state the
correct per-axis monotonicity: holding either the size byte or the mantissa
fixed, the expanded target is monotone in the other axis. These are the
strongest correct monotonicity statements for this encoding. -/

/-- **T8 (monotonicity in mantissa, equal size).** Larger mantissa with the same
size byte gives a larger expanded target. -/
theorem toExpanded_mono_mantissa (m₁ m₂ size : Nat) (hm : m₁ ≤ m₂)
    (_ : OFFSET ≤ size) (hm₁ : m₁ < SIGN_BIT) (hm₂ : m₂ < SIGN_BIT) :
    toExpanded (assembleCompact m₁ size) ≤ toExpanded (assembleCompact m₂ size) := by
  unfold toExpanded
  have h1m := assembleCompact_mantissa m₁ size hm₁
  have h2m := assembleCompact_mantissa m₂ size hm₂
  have h1s : sizeByte (assembleCompact m₁ size) = size := by
    apply assembleCompact_sizeByte
    unfold SIGN_BIT at hm₁; omega
  have h2s : sizeByte (assembleCompact m₂ size) = size := by
    apply assembleCompact_sizeByte
    unfold SIGN_BIT at hm₂; omega
  rw [h1m, h2m, h1s, h2s]
  exact Nat.mul_le_mul_right _ hm

/-- **T9 (monotonicity in size, equal mantissa).** Larger size byte with the
same non-zero mantissa gives a larger expanded target. -/
theorem toExpanded_mono_size (m s₁ s₂ : Nat) (hs : s₁ ≤ s₂)
    (h₁ : OFFSET ≤ s₁) (hm : m < SIGN_BIT) :
    toExpanded (assembleCompact m s₁) ≤ toExpanded (assembleCompact m s₂) := by
  unfold toExpanded
  have h1m := assembleCompact_mantissa m s₁ hm
  have h2m := assembleCompact_mantissa m s₂ hm
  have h1s : sizeByte (assembleCompact m s₁) = s₁ := by
    apply assembleCompact_sizeByte
    unfold SIGN_BIT at hm; omega
  have h2s : sizeByte (assembleCompact m s₂) = s₂ := by
    apply assembleCompact_sizeByte
    unfold SIGN_BIT at hm; omega
  rw [h1m, h2m, h1s, h2s]
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_right (by unfold BASE; decide)
  omega

/-- **T10 (canonical compact values have sign bit clear).** -/
theorem canonical_sign_clear (c : Nat) (hcan : isCanonical c) : signBitSet c = false :=
  hcan.2.1

/-- **T11 (`toExpandedOpt` succeeds on canonical non-zero compact values).** For
a canonical compact value whose mantissa is non-zero, the option-wrapped
expansion returns `some _`. -/
theorem toExpandedOpt_some_of_canonical (c : Nat) (hcan : isCanonical c)
    (hnz : 0 < mantissa c) :
    toExpandedOpt c = some (toExpanded c) := by
  unfold toExpandedOpt
  rw [if_neg]
  · have hbase_pos : 0 < BASE ^ (sizeByte c - OFFSET) := by
      have hb : 0 < BASE := by unfold BASE; decide
      exact Nat.pow_pos hb
    have he : toExpanded c ≠ 0 := by
      unfold toExpanded
      have := Nat.mul_pos hnz hbase_pos
      omega
    simp [he]
  · rw [hcan.2.1]; simp

/-- **T12 (`toExpandedOpt` returns `none` when the sign bit is set).** -/
theorem toExpandedOpt_none_of_signed (c : Nat) (hs : signBitSet c = true) :
    toExpandedOpt c = none := by
  unfold toExpandedOpt
  simp [hs]

/-! ## Concrete-value witnesses -/

/-- The Zcash mainnet PoWLimit-derived compact value `0x1f07ffff`. The Zcash
mainnet PoWLimit is `2^243 - 1` (Zcash protocol spec, page 73). When passed
through `to_compact`, this yields size byte `0x1f = 31` and mantissa
`0x7ffff`. (`bits = 243`, `size = bits/8 + 1 = 31`, mantissa is `PoWLimit >>
(8 * (size - 3)) = (2^243 - 1) >> 224 = 2^19 - 1 = 0x7ffff`.)
Source: `zebra-chain/src/work/difficulty.rs:730` (mainnet PoWLimit). -/
def ZCASH_MAINNET_POWLIMIT_BITS : Nat := 0x1f07ffff

/-- The Bitcoin/Zcash compact representation `0x1d00ffff` — the original
Bitcoin mainnet minimum difficulty, used as a vector in the Rust tests.
Source: `zebra-chain/src/work/difficulty/tests/vectors.rs:193` -/
def BTC_MAINNET_BITS : Nat := 0x1d00ffff

/-- **T13 (concrete round-trip, `0x1f07ffff` — Zcash mainnet PoWLimit compact).**
The Zcash mainnet PoWLimit compact value has mantissa `0x7ffff` and size byte
`0x1f = 31`, and round-trips exactly. Note: this is the **bit-level**
decomposition only — see T13a for the matching expanded-target value. -/
theorem roundtrip_zcash_main :
    mantissa ZCASH_MAINNET_POWLIMIT_BITS = 0x7ffff ∧
    sizeByte ZCASH_MAINNET_POWLIMIT_BITS = 0x1f ∧
    assembleCompact 0x7ffff 0x1f = ZCASH_MAINNET_POWLIMIT_BITS ∧
    signBitSet ZCASH_MAINNET_POWLIMIT_BITS = false := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold mantissa ZCASH_MAINNET_POWLIMIT_BITS SIGN_BIT; decide
  · unfold sizeByte ZCASH_MAINNET_POWLIMIT_BITS; decide
  · unfold assembleCompact ZCASH_MAINNET_POWLIMIT_BITS; decide
  · unfold signBitSet ZCASH_MAINNET_POWLIMIT_BITS SIGN_BIT; decide

/-- **T13a (`0x1f07ffff` expands to `0x7ffff * 256^28`).** The Zcash PoWLimit
compact value expands to `0x7ffff * 256^(31 - 3) = 0x7ffff * 256^28`, which
equals `(2^19 - 1) * 256^28 = 2^243 - 256^28` — within `256^28` of the
mantissa-rounded `2^243` PoWLimit. (Rust's `bits_to_compact` derives `0x7ffff`
by shifting `2^243 - 1` right by `8 * 28 = 224` bits, so the expansion
recovers a slight under-approximation by design; that is the lossy step
introduced by the floating-point representation.)
Source: `zebra-chain/src/work/difficulty.rs:730`. -/
theorem toExpanded_zcash_main :
    toExpanded ZCASH_MAINNET_POWLIMIT_BITS = 0x7ffff * BASE ^ 28 := by
  unfold toExpanded
  have hm : mantissa ZCASH_MAINNET_POWLIMIT_BITS = 0x7ffff := (roundtrip_zcash_main).1
  have hs : sizeByte ZCASH_MAINNET_POWLIMIT_BITS = 0x1f := (roundtrip_zcash_main).2.1
  rw [hm, hs]
  unfold OFFSET
  rfl

/-- **T14 (concrete round-trip, `0x1d00ffff`).** The Bitcoin mainnet minimum
difficulty has mantissa `0xffff` and size byte `0x1d = 29`, and round-trips
exactly. Retained as a second cross-check vector. -/
theorem roundtrip_btc_main :
    mantissa BTC_MAINNET_BITS = 0xffff ∧
    sizeByte BTC_MAINNET_BITS = 0x1d ∧
    assembleCompact 0xffff 0x1d = BTC_MAINNET_BITS ∧
    signBitSet BTC_MAINNET_BITS = false := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold mantissa BTC_MAINNET_BITS SIGN_BIT; decide
  · unfold sizeByte BTC_MAINNET_BITS; decide
  · unfold assembleCompact BTC_MAINNET_BITS; decide
  · unfold signBitSet BTC_MAINNET_BITS SIGN_BIT; decide

/-- **T15 (`0x1d00ffff` expands to `0xffff * 256^26`).** Matches the Rust test
vector `u256_btc_main = U256::from(0xffff) << 208` (which is `0xffff * 2^208 =
0xffff * 256^26`).
Source: `zebra-chain/src/work/difficulty/tests/vectors.rs:194` -/
theorem toExpanded_btc_main : toExpanded BTC_MAINNET_BITS = 0xffff * BASE ^ 26 := by
  unfold toExpanded
  have hm : mantissa BTC_MAINNET_BITS = 0xffff := (roundtrip_btc_main).1
  have hs : sizeByte BTC_MAINNET_BITS = 0x1d := (roundtrip_btc_main).2.1
  rw [hm, hs]
  unfold OFFSET
  rfl

/-- **T16 (`toExpandedOpt` on `0x1d00ffff`).** The option-wrapped expansion of
the Bitcoin mainnet difficulty is non-zero, so it returns `some _`. -/
theorem toExpandedOpt_btc_main :
    toExpandedOpt BTC_MAINNET_BITS = some (0xffff * BASE ^ 26) := by
  have hexp : toExpanded BTC_MAINNET_BITS = 0xffff * BASE ^ 26 := toExpanded_btc_main
  have hsig : signBitSet BTC_MAINNET_BITS = false := (roundtrip_btc_main).2.2.2
  unfold toExpandedOpt
  rw [if_neg (by rw [hsig]; decide)]
  have hne : 0xffff * BASE ^ 26 ≠ 0 := by unfold BASE; decide
  rw [hexp]
  simp [hne]

/-! ## Bonus theorems -/

/-- **B1 (mantissa-bound is the 23-bit mantissa range).** -/
theorem mantissa_range (c : Nat) : mantissa c < 2 ^ 23 := by
  have h := mantissa_lt_sign_bit c
  unfold SIGN_BIT at h
  exact h

/-- **B2 (`assembleCompact` is monotone in the size byte for any fixed mantissa).**
Larger size byte gives a larger compact word. -/
theorem assembleCompact_mono_size (m s₁ s₂ : Nat) (hs : s₁ ≤ s₂) :
    assembleCompact m s₁ ≤ assembleCompact m s₂ := by
  unfold assembleCompact
  have : s₁ * 2 ^ 24 ≤ s₂ * 2 ^ 24 := Nat.mul_le_mul_right _ hs
  omega

/-- **B3 (`assembleCompact` is monotone in the mantissa for any fixed size byte).** -/
theorem assembleCompact_mono_mantissa (m₁ m₂ s : Nat) (hm : m₁ ≤ m₂) :
    assembleCompact m₁ s ≤ assembleCompact m₂ s := by
  unfold assembleCompact; omega

/-- **B4 (signBitSet branches cleanly on the bit 23 quotient).** -/
theorem signBitSet_iff (c : Nat) :
    signBitSet c = true ↔ (c / SIGN_BIT) % 2 = 1 := by
  unfold signBitSet
  by_cases h : (c / SIGN_BIT) % 2 = 1
  · simp [h]
  · simp [h]

/-- **B5 (`toExpandedOpt` is consistent with `toExpanded`).** When `toExpandedOpt`
returns `some v`, `v` equals `toExpanded`. -/
theorem toExpandedOpt_eq_toExpanded (c : Nat) (v : Nat)
    (h : toExpandedOpt c = some v) : v = toExpanded c := by
  unfold toExpandedOpt at h
  by_cases hsign : signBitSet c
  · simp [hsign] at h
  · simp [hsign] at h
    by_cases hzero : toExpanded c = 0
    · simp [hzero] at h
    · simp [hzero] at h
      exact h.symm

/-! ## Coverage for the Rust normalisation branches

Findings 9–10 and the medium-severity coverage gaps at FINDINGS lines 611–612
("`e ∈ {30, 31, 32+, <0}` cases unmodelled") motivated the
`toExpandedFullModel` function above. The following theorems pin its
behaviour on each Rust branch. -/

/-- **N1 (`toExpandedFullModel` rejects sign-bit-set words).** Mirrors the
Rust early return at `difficulty.rs:198-200`. -/
theorem fullModel_none_of_signed (c : Nat) (hs : signBitSet c = true) :
    toExpandedFullModel c = none := by
  unfold toExpandedFullModel
  simp [hs]

/-- **N2 (`toExpandedFullModel` rejects overflow size bytes `≥ 35`).** Mirrors the
Rust match arm `(_, e) if e ≥ 32 → return None` at `difficulty.rs:221`,
where `e = sizeByte - 3`, so `e ≥ 32 ⟺ sizeByte ≥ 35`. -/
theorem fullModel_none_of_overflow_size (c : Nat) (hs : signBitSet c = false)
    (h : sizeByte c ≥ 35) :
    toExpandedFullModel c = none := by
  unfold toExpandedFullModel
  simp [hs, h]

/-- **N3 (`toExpandedFullModel` rejects `sizeByte = 34` with mantissa > 0xff).**
Mirrors the Rust match arm `(m, e) if (e == 31 && m > u8::MAX.into()) → None`
at `difficulty.rs:224`. -/
theorem fullModel_none_of_e31_large_mantissa (c : Nat) (hs : signBitSet c = false)
    (hsize : sizeByte c = 34) (hmant : mantissa c > 0xff) :
    toExpandedFullModel c = none := by
  unfold toExpandedFullModel
  simp [hs, hsize, hmant]

/-- **N4 (`toExpandedFullModel` applies the `e = 31` shift for small mantissa).**
Mirrors `(m, e) if (e == 31 && m ≤ u8::MAX.into()) → (m << 16, e - 2)` at
`difficulty.rs:225`; the result is `m * 2^16 * 256^29`. -/
theorem fullModel_e31_shift (c : Nat) (hs : signBitSet c = false)
    (hsize : sizeByte c = 34) (hmant : mantissa c ≤ 0xff) (hnz : 0 < mantissa c) :
    toExpandedFullModel c = some (mantissa c * 2 ^ 16 * BASE ^ 29) := by
  unfold toExpandedFullModel
  have hnot : ¬ mantissa c > 0xff := by omega
  have hm_ne : mantissa c ≠ 0 := Nat.pos_iff_ne_zero.mp hnz
  have hbase_ne : BASE ≠ 0 := by unfold BASE; decide
  simp [hs, hsize, hnot, hm_ne, hbase_ne]

/-- **N5 (`toExpandedFullModel` rejects `sizeByte = 33` with mantissa > 0xffff).**
Mirrors `(m, e) if (e == 30 && m > u16::MAX.into()) → None` at
`difficulty.rs:226`. -/
theorem fullModel_none_of_e30_large_mantissa (c : Nat) (hs : signBitSet c = false)
    (hsize : sizeByte c = 33) (hmant : mantissa c > 0xffff) :
    toExpandedFullModel c = none := by
  unfold toExpandedFullModel
  simp [hs, hsize, hmant]

/-- **N6 (`toExpandedFullModel` applies the `e = 30` shift for small mantissa).**
Mirrors `(m, e) if (e == 30 && m ≤ u16::MAX.into()) → (m << 8, e - 1)` at
`difficulty.rs:227`; the result is `m * 2^8 * 256^29`. -/
theorem fullModel_e30_shift (c : Nat) (hs : signBitSet c = false)
    (hsize : sizeByte c = 33) (hmant : mantissa c ≤ 0xffff) (hnz : 0 < mantissa c) :
    toExpandedFullModel c = some (mantissa c * 2 ^ 8 * BASE ^ 29) := by
  unfold toExpandedFullModel
  have hnot : ¬ mantissa c > 0xffff := by omega
  have hm_ne : mantissa c ≠ 0 := Nat.pos_iff_ne_zero.mp hnz
  have hbase_ne : BASE ≠ 0 := by unfold BASE; decide
  simp [hs, hsize, hnot, hm_ne, hbase_ne]

/-- **N7 (`toExpandedFullModel` applies the underflow shift for `sizeByte < 3`).**
Mirrors `(m, e) if e < 0 → (m >> (|e|*8), 0)` at `difficulty.rs:232`. With
`e = sizeByte - 3`, `e < 0` means `sizeByte ∈ {0, 1, 2}`, and the shift amount
is `|e|*8 = (3 - sizeByte) * 8`. The result is `mantissa >> ((3-sizeByte)*8)`,
provided that shift doesn't zero out the mantissa. -/
theorem fullModel_underflow_shift (c : Nat) (hs : signBitSet c = false)
    (hsize : sizeByte c < OFFSET)
    (hnz : 0 < mantissa c / 2 ^ ((OFFSET - sizeByte c) * 8)) :
    toExpandedFullModel c = some (mantissa c / 2 ^ ((OFFSET - sizeByte c) * 8)) := by
  unfold toExpandedFullModel
  have hge : ¬ sizeByte c ≥ 35 := by unfold OFFSET at hsize; omega
  have hne34 : sizeByte c ≠ 34 := by unfold OFFSET at hsize; omega
  have hne33 : sizeByte c ≠ 33 := by unfold OFFSET at hsize; omega
  have hne : mantissa c / 2 ^ ((OFFSET - sizeByte c) * 8) ≠ 0 := Nat.pos_iff_ne_zero.mp hnz
  simp [hs, hge, hne34, hne33, hsize, hne]

/-- **N8 (`toExpandedFullModel` matches `toExpanded` on the canonical no-shift range).**
For canonical compact values (sign clear, `sizeByte ∈ [3, 32]`, mantissa
non-zero), the full model agrees with the simple `toExpanded` formula. -/
theorem fullModel_eq_toExpanded_on_canonical (c : Nat) (hcan : isCanonical c)
    (hnz : 0 < mantissa c) :
    toExpandedFullModel c = some (toExpanded c) := by
  obtain ⟨_, hs, hlo, hhi⟩ := hcan
  unfold toExpandedFullModel
  have hge : ¬ sizeByte c ≥ 35 := by omega
  have hne34 : sizeByte c ≠ 34 := by omega
  have hne33 : sizeByte c ≠ 33 := by omega
  have hgeOff : ¬ sizeByte c < OFFSET := by omega
  have hbasepos : 0 < BASE ^ (sizeByte c - OFFSET) :=
    Nat.pow_pos (by unfold BASE; decide)
  have hne : mantissa c * BASE ^ (sizeByte c - OFFSET) ≠ 0 := by
    have := Nat.mul_pos hnz hbasepos
    omega
  unfold toExpanded
  simp [hs, hge, hne34, hne33, hgeOff, hne]

/-- **N9 (the canonical no-shift size byte range is `[3, 32]`).** Direct
restatement of `isCanonical`'s bounds; documents that the previous bound
`≤ 29` was wrong (it excluded size bytes 30, 31, 32 which are all
canonical no-shift). -/
theorem isCanonical_sizeByte_range (c : Nat) (hcan : isCanonical c) :
    OFFSET ≤ sizeByte c ∧ sizeByte c ≤ 32 :=
  ⟨hcan.2.2.1, hcan.2.2.2⟩

/-- **N10 (sizeByte 32 is canonical for sign-clear words).** The new upper
bound `32` includes the previously-excluded boundary. With sign clear and
sizeByte = 32, the word is canonical iff it fits in 32 bits — which it
always does because `sizeByte = c / 2^24 = 32` plus a sign-clear constraint
implies `c < 33 * 2^24 < 2^32`. -/
theorem isCanonical_at_sizeByte_32 (c : Nat) (hsz : sizeByte c = 32)
    (hs : signBitSet c = false) (hc32 : c < U32_LIMIT) : isCanonical c := by
  refine ⟨hc32, hs, ?_, ?_⟩
  · unfold OFFSET; omega
  · omega

/-- **N11 (`assembleCompact` builds a canonical word at the new boundary
sizeByte = 32).** Assembling with a sub-`SIGN_BIT` mantissa and size = 32
yields a canonical compact word, witnessing that the widened range is
non-empty. -/
theorem assembleCompact_canonical_at_size_32 (m : Nat) (hm : m < SIGN_BIT) :
    isCanonical (assembleCompact m 32) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold assembleCompact SIGN_BIT U32_LIMIT at *
    have h1 : (32 : Nat) * 2 ^ 24 = 2 ^ 29 := by decide
    have h2 : m < 2 ^ 23 := hm
    have h3 : (2 : Nat) ^ 23 < 2 ^ 32 := by decide
    have h4 : (2 : Nat) ^ 29 + 2 ^ 23 < 2 ^ 32 := by decide
    omega
  · exact assembleCompact_sign_clear m 32 hm
  · have h := assembleCompact_sizeByte m 32 (by unfold SIGN_BIT at hm; omega)
    rw [h]; unfold OFFSET; omega
  · have h := assembleCompact_sizeByte m 32 (by unfold SIGN_BIT at hm; omega)
    rw [h]

end Zebra.CompactDifficulty
