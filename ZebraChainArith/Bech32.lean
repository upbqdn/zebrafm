import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bech32 (BIP-173) checksum properties

Zebra consumes Bech32 indirectly through the `bech32` / `bech32m` crates used by
`zcash_address` and friends (see `zebra-chain/src/primitives/`). The encoding
is specified by BIP-173:

  * The data part is a sequence of 5-bit values in `GF(32)`.
  * A `polymod` function computes a checksum using a fixed degree-6 generator
    polynomial.
  * The checksum is exactly 6 characters long, and the human-readable part
    (HRP) is separated from the data part by the character `'1'` (ASCII 49).

We model 5-bit values as `Nat`s with the invariant `< 32`, the polymod state as
a `Nat` (the BIP-173 reference implementation uses a 30-bit integer), and the
HRP/data parts as `List Nat`. We do not encode the bit-twiddling of the actual
Galois-field multiplication; instead we model `polymod` as a fold that is *by
construction* a pure function of its byte inputs, and prove the structural
invariants the spec demands.

Reference: BIP-173 (https://github.com/bitcoin/bips/blob/master/bip-0173.mediawiki)
and `zebra-chain/src/primitives/zcash_history.rs`.
-/

namespace Zebra.Bech32

/-! ## Constants -/

/-- The Bech32 separator character: ASCII `'1'` = `49`.
Source: BIP-173 ("the separator, which is always `1`"). -/
def SEPARATOR : Nat := 49

/-- The required length of the Bech32 checksum, in 5-bit characters.
Source: BIP-173 ("a 6-character checksum"). -/
def CHECKSUM_LENGTH : Nat := 6

/-- The Bech32 charset has 32 symbols (5 bits each).
Source: BIP-173. -/
def CHARSET_SIZE : Nat := 32

/-- Initial state of the polymod register, per BIP-173. -/
def POLYMOD_INIT : Nat := 1

/-- The five generator constants for the Bech32 polymod step, modulo `2^30`.
Source: BIP-173 reference implementation `bech32_polymod`. -/
def GEN : List Nat :=
  [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3]

/-! ## The polymod step -/

/-- The bit-mask `2^30 - 1` that clamps the polymod register to 30 bits. -/
def MASK30 : Nat := 1073741823 -- 2^30 - 1

/-- One step of the Bech32 polymod fold, modelling the per-value mixing of the
BIP-173 reference implementation. The exact GF(32) multiplication is abstracted
to the simpler "mix value into clamped register" operation that preserves the
structural properties we care about (purely determined by `(c, v)`, and stays
within `[0, MASK30]`).

Source: BIP-173 reference `bech32_polymod`. -/
def polymodStep (c v : Nat) : Nat :=
  ((c * 32 + v) % (MASK30 + 1))

/-- The full polymod: fold `polymodStep` over the input list, starting from the
initial register state. This is purely a function of the input list. -/
def polymod (values : List Nat) : Nat :=
  values.foldl polymodStep POLYMOD_INIT

/-! ## Encode-side helpers -/

/-- The HRP-expansion phase of Bech32: each HRP byte contributes its high 3 bits
followed by all its low 5 bits, joined by a `0` separator. We model this with a
shape predicate (length is `2 * hrp.length + 1`). -/
def hrpExpand (hrp : List Nat) : List Nat :=
  hrp.map (fun c => c / 32) ++ [0] ++ hrp.map (fun c => c % 32)

/-- A complete Bech32 string is `hrp ++ ['1'] ++ data ++ checksum`. We model
`encode` as that concatenation. -/
def encode (hrp data checksum : List Nat) : List Nat :=
  hrp ++ [SEPARATOR] ++ data ++ checksum

/-! ## Theorems -/

/-- **T1.** `polymod` is a pure function of its input bytes: equal inputs give
equal outputs. (Trivial in Lean, but it witnesses the BIP-173 claim that the
checksum depends only on the data, not on any hidden state.) -/
theorem polymod_deterministic (xs ys : List Nat) (h : xs = ys) :
    polymod xs = polymod ys := by
  rw [h]

/-- **T2.** `polymod` of the empty list is the initial register value `1`. -/
theorem polymod_nil : polymod [] = POLYMOD_INIT := rfl

/-- **T3.** `polymod` is always strictly less than `2^30` (the spec's 30-bit
register width). The base case is `POLYMOD_INIT = 1 < 2^30`; the step uses
`% (MASK30 + 1)`. -/
theorem polymod_lt_2pow30 (xs : List Nat) : polymod xs < MASK30 + 1 := by
  unfold polymod
  -- Show the invariant holds for the fold by induction on `xs`, generalising
  -- the accumulator.
  suffices h : ∀ (acc : Nat) (l : List Nat),
      acc < MASK30 + 1 → l.foldl polymodStep acc < MASK30 + 1 by
    exact h POLYMOD_INIT xs (by unfold POLYMOD_INIT MASK30; omega)
  intro acc l
  induction l generalizing acc with
  | nil => intro h; simpa using h
  | cons x xs ih =>
    intro _
    apply ih
    unfold polymodStep
    exact Nat.mod_lt _ (by unfold MASK30; omega)

/-- **T4.** `polymod` extends by `foldl`: appending a value just runs one more
`polymodStep`. -/
theorem polymod_snoc (xs : List Nat) (v : Nat) :
    polymod (xs ++ [v]) = polymodStep (polymod xs) v := by
  unfold polymod
  rw [List.foldl_append]
  rfl

/-- **T5.** `polymod` distributes over list concatenation via a fold continuation.
This is the structural lemma that lets you compute the checksum incrementally. -/
theorem polymod_append (xs ys : List Nat) :
    polymod (xs ++ ys) = ys.foldl polymodStep (polymod xs) := by
  unfold polymod
  rw [List.foldl_append]

/-- **T6.** The `hrpExpand` of an HRP of length `n` has length `2*n + 1`.
Source: BIP-173 (HRP expansion produces `2*len(hrp) + 1` values). -/
theorem hrpExpand_length (hrp : List Nat) :
    (hrpExpand hrp).length = 2 * hrp.length + 1 := by
  unfold hrpExpand
  simp [List.length_append, List.length_map]
  ring

/-- **T7.** `encode` length: `|hrp| + 1 + |data| + |checksum|`. -/
theorem encode_length (hrp data checksum : List Nat) :
    (encode hrp data checksum).length =
      hrp.length + 1 + data.length + checksum.length := by
  unfold encode
  simp [List.length_append]
  ring

/-- **T8.** The separator in every encoded Bech32 string is `'1'` (ASCII 49):
dropping the HRP prefix leaves a list whose head is `SEPARATOR`. -/
theorem encode_separator_after_hrp
    (hrp data checksum : List Nat) :
    (encode hrp data checksum).drop hrp.length = SEPARATOR :: (data ++ checksum) := by
  unfold encode
  simp [List.append_assoc]

/-- **T9.** If we feed a 6-character checksum to `encode`, the encoded string
ends with that checksum. This is the "checksum length is 6" claim from the
BIP-173 spec, made concrete: a well-formed encoding has its last 6 characters
equal to the checksum. -/
theorem encode_checksum_suffix
    (hrp data checksum : List Nat)
    (_h : checksum.length = CHECKSUM_LENGTH) :
    (encode hrp data checksum).drop (hrp.length + 1 + data.length) = checksum := by
  unfold encode
  -- Reassociate so the "prefix" is `(hrp ++ [SEPARATOR] ++ data)` of length
  -- `hrp.length + 1 + data.length`, then `List.drop_left` finishes.
  have e1 : hrp ++ [SEPARATOR] ++ data ++ checksum
          = (hrp ++ [SEPARATOR] ++ data) ++ checksum := by
    simp [List.append_assoc]
  rw [e1]
  have hlen : (hrp ++ [SEPARATOR] ++ data).length
                = hrp.length + 1 + data.length := by
    simp [List.length_append]
    ring
  rw [← hlen]
  exact List.drop_left

/-- **T10.** `encode` is injective in the data part for fixed HRP and checksum
of equal length (a non-malleability property at the structural level): if two
encodings agree, the data parts must agree. -/
theorem encode_injective_data
    (hrp d1 d2 checksum : List Nat)
    (_hlen : d1.length = d2.length)
    (h : encode hrp d1 checksum = encode hrp d2 checksum) :
    d1 = d2 := by
  unfold encode at h
  -- Reassociate so the shared prefix `hrp ++ [SEPARATOR]` is one block.
  have h' : (hrp ++ [SEPARATOR]) ++ (d1 ++ checksum)
          = (hrp ++ [SEPARATOR]) ++ (d2 ++ checksum) := by
    rw [show (hrp ++ [SEPARATOR]) ++ (d1 ++ checksum)
          = hrp ++ [SEPARATOR] ++ d1 ++ checksum by simp [List.append_assoc],
        show (hrp ++ [SEPARATOR]) ++ (d2 ++ checksum)
          = hrp ++ [SEPARATOR] ++ d2 ++ checksum by simp [List.append_assoc]]
    exact h
  -- Cancel the shared prefix.
  have h2 : d1 ++ checksum = d2 ++ checksum :=
    List.append_cancel_left h'
  -- Cancel the shared suffix.
  exact List.append_cancel_right h2

/-! ## Bonus theorems -/

/-- **B1.** `SEPARATOR` is the ASCII code of `'1'`. -/
theorem separator_is_one : SEPARATOR = 49 := rfl

/-- **B2.** `CHECKSUM_LENGTH` is exactly 6. -/
theorem checksum_length_is_six : CHECKSUM_LENGTH = 6 := rfl

/-- **B3.** `CHARSET_SIZE` is exactly 32 (5 bits per character). -/
theorem charset_size_is_32 : CHARSET_SIZE = 32 := rfl

/-- **B4.** A polymod step is bounded by `MASK30`. -/
theorem polymodStep_lt (c v : Nat) : polymodStep c v < MASK30 + 1 := by
  unfold polymodStep
  exact Nat.mod_lt _ (by unfold MASK30; omega)

/-- **B5.** `hrpExpand` is non-empty (it always contains the central `0`). -/
theorem hrpExpand_nonempty (hrp : List Nat) : hrpExpand hrp ≠ [] := by
  unfold hrpExpand
  intro h
  have := congrArg List.length h
  simp [List.length_append, List.length_map] at this

/-- **B6.** Encoding is non-empty whenever HRP is non-empty (or there is any
data/checksum), because of the embedded separator: even with empty `hrp`,
`data`, `checksum`, the encoding still contains `[SEPARATOR]`. -/
theorem encode_nonempty (hrp data checksum : List Nat) :
    encode hrp data checksum ≠ [] := by
  unfold encode
  intro h
  have := congrArg List.length h
  simp [List.length_append] at this

end Zebra.Bech32
