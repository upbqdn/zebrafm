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

For a **canonically-encoded** value `c` (sign bit clear, size byte ≥ 3 — the
range that does not trigger overflow normalisation in the Rust source), the
expanded target threshold is

```text
  to_expanded(c) = mantissa × 256^(size - 3)
```

For the inverse direction (`to_compact`) the production code asserts on zero
and panics on overflow, then encodes the value back as `mantissa + (size << 24)`.

We model:
  * `CompactDifficulty` as a `Nat` with the implicit invariant `< 2^32`;
  * the expanded target as a `Nat` (it can grow up to `≈ 2^248` but `Nat` is
    unbounded, so this is faithful);
  * `toExpanded` as a `Nat`-valued helper for the canonical range, plus an
    `Option Nat` wrapper that returns `none` on the rejected (sign-bit-set)
    encodings — matching the Rust early-return.

The Rust source has additional logic for `size ∈ {30, 31}` overflow/underflow
normalisation, but every value in the canonical range used by consensus
(post-difficulty-adjustment difficulties, the genesis PoWLimit, etc.) has
`size ≥ 3` and is well-defined by the simple formula above. We prove the
round-trip on that canonical range.

Source: `zebra-chain/src/work/difficulty.rs:159` (`impl CompactDifficulty`),
        `zebra-chain/src/work/difficulty.rs:460` (`impl ExpandedDifficulty::to_compact`).
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

/-- A compact value is **canonically encoded** iff the sign bit is clear and
the size byte is in the no-overflow-normalisation range `[OFFSET, 29]`. (At
`size ∈ {30, 31}` the Rust code applies a normalising shift; here we restrict
to the safe range that matches the natural `mantissa × 256^(size - 3)` formula.) -/
def isCanonical (c : Nat) : Prop :=
  c < U32_LIMIT ∧
  signBitSet c = false ∧
  OFFSET ≤ sizeByte c ∧
  sizeByte c ≤ 29

/-! ## Encoder and decoder -/

/-- `to_expanded` for a canonical compact value: `mantissa × 256^(size - 3)`.
Source: `zebra-chain/src/work/difficulty.rs:186` (`pub fn to_expanded`) -/
def toExpanded (c : Nat) : Nat :=
  mantissa c * BASE ^ (sizeByte c - OFFSET)

/-- `Option`-wrapped `toExpanded`: returns `none` for the rejected (sign-bit-set)
encodings, and `none` for zero results. This matches the Rust early-return on
sign bit set and on zero result.
Source: `zebra-chain/src/work/difficulty.rs:186` -/
def toExpandedOpt (c : Nat) : Option Nat :=
  if signBitSet c then
    none
  else
    let e := toExpanded c
    if e = 0 then none else some e

/-- `to_compact`: given a target threshold modelled as `mantissa × 256^(size - 3)`
with `mantissa` in the canonical mantissa range `[1, UNSIGNED_MANTISSA_MASK]` and
`size ∈ [OFFSET, 29]`, recover the compact 32-bit word.
Source: `zebra-chain/src/work/difficulty.rs:460` (`pub fn to_compact`) -/
def toCompact (m : Nat) (size : Nat) : Nat :=
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
`toExpanded`/`toCompactFromExpanded` round-trip — that would require a `bits()`
computation on the expanded `Nat`, which is out of scope for this module. This
theorem shows that for any compact word `c < 2^32` with the sign bit clear,
splitting `c` into its low-23-bit mantissa and high-8-bit size byte and then
recombining via `m + size * 2^24` recovers `c` exactly. It is the
encoder/decoder consistency lemma at the bit level, supporting T4–T7 below.
Source: `zebra-chain/src/work/difficulty.rs:198` (early-return on signed),
        `zebra-chain/src/work/difficulty.rs:205` (mantissa extraction),
        `zebra-chain/src/work/difficulty.rs:211` (size extraction). -/
theorem compact_decompose_recompose (c : Nat) (h : c < U32_LIMIT)
    (hs : signBitSet c = false) :
    toCompact (mantissa c) (sizeByte c) = c := by
  unfold toCompact
  have hd := decomposition c h
  simp [hs] at hd
  omega

/-- **T4 (the compact word reconstructed from `(mantissa, size)`).** Constructing
a compact value from a mantissa `< SIGN_BIT` and a size byte `< 256` then
extracting the components recovers `(m, s)`. -/
theorem toCompact_mantissa (m size : Nat) (hm : m < SIGN_BIT) :
    mantissa (toCompact m size) = m := by
  unfold mantissa toCompact SIGN_BIT at *
  have : (m + size * 2 ^ 24) % 2 ^ 23 = m % 2 ^ 23 := by
    have : size * 2 ^ 24 = (size * 2) * 2 ^ 23 := by ring
    rw [this, Nat.add_mul_mod_self_right]
  rw [this]
  exact Nat.mod_eq_of_lt hm

theorem toCompact_sizeByte (m size : Nat) (hm : m < 2 ^ 24) :
    sizeByte (toCompact m size) = size := by
  unfold sizeByte toCompact
  have hpow : (0 : Nat) < 2 ^ 24 := by decide
  rw [Nat.add_mul_div_right _ _ hpow, Nat.div_eq_of_lt hm, Nat.zero_add]

/-- **T5 (round-trip from `(mantissa, size)` to compact and back).** -/
theorem roundtrip_components (m size : Nat) (hm : m < SIGN_BIT) :
    mantissa (toCompact m size) = m ∧ sizeByte (toCompact m size) = size := by
  refine ⟨toCompact_mantissa m size hm, toCompact_sizeByte m size ?_⟩
  unfold SIGN_BIT at hm
  have : (2 : Nat) ^ 23 < 2 ^ 24 := by decide
  omega

/-- **T6 (sign bit clear after `toCompact` for a sub-`SIGN_BIT` mantissa).**
Because the mantissa is `< SIGN_BIT = 2^23`, the only contribution to bit 23
of the reconstructed word comes from `size * 2^24`, which is always even at
the bit-23 position. Therefore the sign bit is clear for any size byte. -/
theorem toCompact_sign_clear (m size : Nat) (hm : m < SIGN_BIT) :
    signBitSet (toCompact m size) = false := by
  unfold signBitSet toCompact SIGN_BIT at *
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
`(mantissa, sizeByte)` and `toCompact` is the identity. -/
theorem roundtrip_canonical (c : Nat) (hcan : isCanonical c) :
    toCompact (mantissa c) (sizeByte c) = c := by
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
    toExpanded (toCompact m₁ size) ≤ toExpanded (toCompact m₂ size) := by
  unfold toExpanded
  have h1m := toCompact_mantissa m₁ size hm₁
  have h2m := toCompact_mantissa m₂ size hm₂
  have h1s : sizeByte (toCompact m₁ size) = size := by
    apply toCompact_sizeByte
    unfold SIGN_BIT at hm₁; omega
  have h2s : sizeByte (toCompact m₂ size) = size := by
    apply toCompact_sizeByte
    unfold SIGN_BIT at hm₂; omega
  rw [h1m, h2m, h1s, h2s]
  exact Nat.mul_le_mul_right _ hm

/-- **T9 (monotonicity in size, equal mantissa).** Larger size byte with the
same non-zero mantissa gives a larger expanded target. -/
theorem toExpanded_mono_size (m s₁ s₂ : Nat) (hs : s₁ ≤ s₂)
    (h₁ : OFFSET ≤ s₁) (hm : m < SIGN_BIT) :
    toExpanded (toCompact m s₁) ≤ toExpanded (toCompact m s₂) := by
  unfold toExpanded
  have h1m := toCompact_mantissa m s₁ hm
  have h2m := toCompact_mantissa m s₂ hm
  have h1s : sizeByte (toCompact m s₁) = s₁ := by
    apply toCompact_sizeByte
    unfold SIGN_BIT at hm; omega
  have h2s : sizeByte (toCompact m s₂) = s₂ := by
    apply toCompact_sizeByte
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
`0x1f = 31`, and round-trips exactly. -/
theorem roundtrip_zcash_main :
    mantissa ZCASH_MAINNET_POWLIMIT_BITS = 0x7ffff ∧
    sizeByte ZCASH_MAINNET_POWLIMIT_BITS = 0x1f ∧
    toCompact 0x7ffff 0x1f = ZCASH_MAINNET_POWLIMIT_BITS ∧
    signBitSet ZCASH_MAINNET_POWLIMIT_BITS = false := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold mantissa ZCASH_MAINNET_POWLIMIT_BITS SIGN_BIT; decide
  · unfold sizeByte ZCASH_MAINNET_POWLIMIT_BITS; decide
  · unfold toCompact ZCASH_MAINNET_POWLIMIT_BITS; decide
  · unfold signBitSet ZCASH_MAINNET_POWLIMIT_BITS SIGN_BIT; decide

/-- **T14 (concrete round-trip, `0x1d00ffff`).** The Bitcoin mainnet minimum
difficulty has mantissa `0xffff` and size byte `0x1d = 29`, and round-trips
exactly. Retained as a second cross-check vector. -/
theorem roundtrip_btc_main :
    mantissa BTC_MAINNET_BITS = 0xffff ∧
    sizeByte BTC_MAINNET_BITS = 0x1d ∧
    toCompact 0xffff 0x1d = BTC_MAINNET_BITS ∧
    signBitSet BTC_MAINNET_BITS = false := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold mantissa BTC_MAINNET_BITS SIGN_BIT; decide
  · unfold sizeByte BTC_MAINNET_BITS; decide
  · unfold toCompact BTC_MAINNET_BITS; decide
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

/-- **B2 (`toCompact` is monotone in the size byte for any fixed mantissa).**
Larger size byte gives a larger compact word. -/
theorem toCompact_mono_size (m s₁ s₂ : Nat) (hs : s₁ ≤ s₂) :
    toCompact m s₁ ≤ toCompact m s₂ := by
  unfold toCompact
  have : s₁ * 2 ^ 24 ≤ s₂ * 2 ^ 24 := Nat.mul_le_mul_right _ hs
  omega

/-- **B3 (`toCompact` is monotone in the mantissa for any fixed size byte).** -/
theorem toCompact_mono_mantissa (m₁ m₂ s : Nat) (hm : m₁ ≤ m₂) :
    toCompact m₁ s ≤ toCompact m₂ s := by
  unfold toCompact; omega

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

end Zebra.CompactDifficulty
