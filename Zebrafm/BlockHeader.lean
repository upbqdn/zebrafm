import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Block header layout from `zebra-chain/src/block/header.rs` and
`zebra-chain/src/block/serialize.rs`

The Zcash block `Header` is a fixed-shape record:

  * `version: u32`           (4 bytes, little-endian)
  * `previous_block_hash`    (32 bytes)
  * `merkle_root`            (32 bytes)
  * `commitment_bytes`       (32 bytes)
  * `time: u32`              (4 bytes, little-endian)
  * `difficulty_threshold`   (4 bytes, little-endian)
  * `nonce`                  (32 bytes — Zcash, not the 4-byte Bitcoin nonce)
  * `solution`               (Equihash; CompactSize-prefixed variable bytes)

This module covers the **fixed-size 140-byte prefix only**.  The Equihash
`solution` is intentionally not modelled here; it has its own coverage in
`EquihashSolution.lean` and `EquihashParams.lean`.  Any time the words
"encoder", "decoder", or "round-trip" appear below, they refer to the
fixed-size prefix only.  Consult the source `serialize.rs` for the full
`Header` encoder which appends `self.solution.zcash_serialize(...)`.

We model:
  * the seven fixed fields as `Nat` (for the four `u32`s) and `List Nat`
    (for the three 32-byte arrays),
  * the encoder as a concatenation of little-endian byte sequences,
  * `check_version` as a `Prop` matching Rust's two-arm rejection
    (`high bit set` and `version < 4`),
  * the decoder as a partial function that succeeds when there are at
    least 140 bytes available *and* `check_version` succeeds.

We prove:
  * the encoder always produces exactly 140 bytes (T2),
  * round-trip of every `u32` field through `toLE4`/`fromLE4` (T3-T5),
  * the encoder's `version` prefix is the first 4 bytes (T6),
  * `HEADER_FIXED_SIZE` decomposes as the seven field widths (T7),
  * `check_version` rejects every `version` with the high bit set (T8)
    and every `version < 4` (T9),
  * `check_version` accepts exactly versions in `[4, 2^31)` (T10),
  * the decoder's three structural rejection paths (T11a-c),
  * the fixed-prefix round-trip
    `decodeFixed (encodeFixed h) = some (h, [])` for every well-formed
    header (T11),
  * the encoder is injective on the whole record (T12) and on each
    individual field (T13-T19).
-/

namespace Zebra.BlockHeader

/-- `u32::MAX`. -/
def U32_MAX : Nat := 4_294_967_295

/-- The Zcash accepted block version.
Source: `zebra-chain/src/block/header.rs:159` (`pub const ZCASH_BLOCK_VERSION: u32 = 4`) -/
def ZCASH_BLOCK_VERSION : Nat := 4

/-- The size in bytes of the fixed-size portion of a Zcash block header
(everything except the Equihash solution).

`4 (version) + 32 (prev_hash) + 32 (merkle_root) + 32 (commitment_bytes)
 + 4 (time) + 4 (difficulty) + 32 (nonce) = 140`.
Source: `zebra-chain/src/block/serialize.rs:64` (`impl ZcashSerialize for Header`) -/
def HEADER_FIXED_SIZE : Nat := 140

/-- The block header record (fixed-size portion; the Equihash `solution`
field is omitted because it has a variable-length encoding and is modelled
separately in `EquihashSolution.lean`).
Source: `zebra-chain/src/block/header.rs:27` (`pub struct Header`) -/
structure Header where
  version : Nat
  prevHash : List Nat
  merkleRoot : List Nat
  commitment : List Nat
  time : Nat
  bits : Nat
  nonce : List Nat
  deriving Repr, DecidableEq

/-! ## Little-endian 4-byte helpers -/

/-- Little-endian 4-byte encoding of a `u32`-shaped `Nat`. -/
def toLE4 (n : Nat) : List Nat :=
  [n % 256, (n / 256) % 256, (n / 65536) % 256, (n / 16777216) % 256]

/-- Little-endian 4-byte decoding. -/
def fromLE4 (b0 b1 b2 b3 : Nat) : Nat :=
  b0 + b1 * 256 + b2 * 65536 + b3 * 16777216

/-! ## Encoder -/

/-- Encode the fixed-size portion of a header as a flat byte list.
The seven fields are concatenated in protocol order. If any of the three
32-byte fields has the wrong length the encoder simply emits that field's
actual contents — round-trip lemmas below restrict attention to
well-formed inputs.

Note: this omits the Equihash `solution` (a CompactSize-prefixed variable
suffix).  See module-level docs.
Source: `zebra-chain/src/block/serialize.rs:64` (`fn zcash_serialize`) -/
def encodeFixed (h : Header) : List Nat :=
  toLE4 h.version
    ++ h.prevHash
    ++ h.merkleRoot
    ++ h.commitment
    ++ toLE4 h.time
    ++ toLE4 h.bits
    ++ h.nonce

/-! ## `check_version` -/

/-- `check_version` from `serialize.rs:36`.  Returns `true` iff the version
field would pass Zebra's two-arm filter:

  * the high bit must be clear (`v >> 31 == 0`, i.e. `v < 2^31`), and
  * the version must be at least `ZCASH_BLOCK_VERSION = 4`.

Note that Rust's first arm rejects `v >> 31 != 0`, which for any `u32`
value is equivalent to `v ≥ 2^31`.

Source: `zebra-chain/src/block/serialize.rs:36-62`. -/
def check_version (v : Nat) : Bool :=
  decide (v < 2 ^ 31) && decide (ZCASH_BLOCK_VERSION ≤ v)

/-! ## Well-formedness predicate -/

/-- A header is well-formed when:
  * the four 32-byte fields each have length 32,
  * the four `u32` fields fit in `[0, U32_MAX]`,
  * `check_version h.version` holds.
Source: `zebra-chain/src/block/serialize.rs:36` (`fn check_version`). -/
structure WellFormed (h : Header) : Prop where
  prevLen : h.prevHash.length = 32
  merkleLen : h.merkleRoot.length = 32
  commitLen : h.commitment.length = 32
  nonceLen : h.nonce.length = 32
  versionMin : ZCASH_BLOCK_VERSION ≤ h.version
  versionMax : h.version < 2 ^ 31
  timeMax : h.time ≤ U32_MAX
  bitsMax : h.bits ≤ U32_MAX

/-! ## Decoder

The decoder takes a `List Nat` and tries to parse the first 140 bytes as a
fixed header prefix.  It

  * fails (returns `none`) if fewer than 140 bytes are available, and
  * fails if `check_version` rejects the decoded version,

mirroring Rust's `zcash_deserialize` at `serialize.rs:86`. -/

/-- `true` iff the prefix has at least 32 bytes available; otherwise the
caller is expected to fail. -/
def has32 (xs : List Nat) : Bool := decide (32 ≤ xs.length)

/-- Decode the fixed 140-byte prefix of a header.  Returns the header and
any unused trailing bytes.

The decoder fails (returns `none`) when:
  * fewer than 4 bytes are present for the version,
  * `check_version` rejects the decoded version,
  * any of the three 32-byte field reads runs out of bytes,
  * fewer than 4 bytes are present for `time` or `bits`,
  * fewer than 32 bytes are present for `nonce`.

Mirrors `zcash_deserialize` in `serialize.rs:86-108` (modulo the omitted
`solution` parse step). -/
def decodeFixed : List Nat → Option (Header × List Nat)
  | v0 :: v1 :: v2 :: v3 :: rest =>
      let version := fromLE4 v0 v1 v2 v3
      if !check_version version then none
      else if !has32 rest then none
      else
        let prev := rest.take 32
        let rest := rest.drop 32
        if !has32 rest then none
        else
          let merkle := rest.take 32
          let rest := rest.drop 32
          if !has32 rest then none
          else
            let commit := rest.take 32
            let rest := rest.drop 32
            match rest with
            | t0 :: t1 :: t2 :: t3 ::
              b0 :: b1 :: b2 :: b3 :: rest =>
                let time := fromLE4 t0 t1 t2 t3
                let bits := fromLE4 b0 b1 b2 b3
                if !has32 rest then none
                else
                  let nonce := rest.take 32
                  let rest := rest.drop 32
                  some ({ version, prevHash := prev, merkleRoot := merkle,
                          commitment := commit, time, bits, nonce }, rest)
            | _ => none
  | _ => none

/-! ## Theorems -/

/-- Little-endian round-trip on 4 bytes for any `u32` input. -/
private theorem le4_roundtrip (n : Nat) (h : n ≤ U32_MAX) :
    fromLE4 (n % 256) ((n / 256) % 256) ((n / 65536) % 256) ((n / 16777216) % 256) = n := by
  unfold fromLE4 U32_MAX at *; omega

/-- **T1.** `toLE4` always produces exactly 4 bytes. -/
theorem toLE4_length (n : Nat) : (toLE4 n).length = 4 := by
  simp [toLE4]

/-- **T2.** The encoder produces exactly `HEADER_FIXED_SIZE` (140) bytes on
any well-formed header. -/
theorem encodeFixed_length (h : Header) (hw : WellFormed h) :
    (encodeFixed h).length = HEADER_FIXED_SIZE := by
  unfold encodeFixed HEADER_FIXED_SIZE
  simp [List.length_append, toLE4_length,
        hw.prevLen, hw.merkleLen, hw.commitLen, hw.nonceLen]

/-- **T3.** Round-trip on the `version` field: encoding the version as
4 little-endian bytes and decoding them recovers the original value, for
any well-formed header. -/
theorem version_roundtrip (h : Header) (hw : WellFormed h) :
    fromLE4
      (h.version % 256)
      ((h.version / 256) % 256)
      ((h.version / 65536) % 256)
      ((h.version / 16777216) % 256) = h.version := by
  have hlt : h.version < 2 ^ 31 := hw.versionMax
  have hle : h.version ≤ U32_MAX := by
    unfold U32_MAX; omega
  exact le4_roundtrip h.version hle

/-- **T4.** Round-trip on the `time` field. -/
theorem time_roundtrip (h : Header) (hw : WellFormed h) :
    fromLE4
      (h.time % 256)
      ((h.time / 256) % 256)
      ((h.time / 65536) % 256)
      ((h.time / 16777216) % 256) = h.time :=
  le4_roundtrip h.time hw.timeMax

/-- **T5.** Round-trip on the `bits` (difficulty) field. -/
theorem bits_roundtrip (h : Header) (hw : WellFormed h) :
    fromLE4
      (h.bits % 256)
      ((h.bits / 256) % 256)
      ((h.bits / 65536) % 256)
      ((h.bits / 16777216) % 256) = h.bits :=
  le4_roundtrip h.bits hw.bitsMax

/-- **T6.** Field-offset pin: the four little-endian version bytes appear
first in the encoded byte stream, at offsets 0..3. -/
theorem encode_version_prefix (h : Header) :
    (encodeFixed h).take 4 = toLE4 h.version := by
  unfold encodeFixed toLE4
  rfl

/-- **T7.** `HEADER_FIXED_SIZE` decomposes as `4 + 32*3 + 4 + 4 + 32`,
matching the Rust layout exactly. -/
theorem header_size_decomposition :
    HEADER_FIXED_SIZE = 4 + 32 + 32 + 32 + 4 + 4 + 32 := by
  unfold HEADER_FIXED_SIZE; rfl

/-! ### `check_version` characterisation -/

/-- **T8.** `check_version` rejects every version with the high bit set.
This is the first arm of Rust's `check_version` (`v >> 31 != 0`). -/
theorem check_version_rejects_high_bit (v : Nat) (h : 2 ^ 31 ≤ v) :
    check_version v = false := by
  unfold check_version
  have hnot : ¬ v < 2 ^ 31 := Nat.not_lt.mpr h
  rw [decide_eq_false hnot, Bool.false_and]

/-- **T9.** `check_version` rejects every version below 4.
This is the second arm of Rust's `check_version`
(`v < ZCASH_BLOCK_VERSION`). -/
theorem check_version_rejects_below_min (v : Nat) (h : v < ZCASH_BLOCK_VERSION) :
    check_version v = false := by
  unfold check_version
  have hnot : ¬ ZCASH_BLOCK_VERSION ≤ v := Nat.not_le.mpr h
  rw [decide_eq_false hnot, Bool.and_false]

/-- **T10.** `check_version` is exactly the predicate
`ZCASH_BLOCK_VERSION ≤ v ∧ v < 2^31`. -/
theorem check_version_iff (v : Nat) :
    check_version v = true ↔ (ZCASH_BLOCK_VERSION ≤ v ∧ v < 2 ^ 31) := by
  unfold check_version
  simp [Bool.and_eq_true, decide_eq_true_eq, And.comm]

/-! ### Decoder pin-down

The decoder's parse failures on the three structural rejection paths are
proved as separate theorems so callers don't have to inspect the body. -/

/-- **T11a.** The decoder rejects any input shorter than 4 bytes
(insufficient to read the `version` prefix). -/
theorem decode_short_version (bytes : List Nat) (h : bytes.length < 4) :
    decodeFixed bytes = none := by
  match bytes, h with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl
  | [_, _, _], _ => rfl

/-- **T11b.** The decoder rejects any 4-byte-prefixed input whose decoded
version has the high bit set. -/
theorem decode_rejects_high_bit
    (v0 v1 v2 v3 : Nat) (rest : List Nat)
    (h : 2 ^ 31 ≤ fromLE4 v0 v1 v2 v3) :
    decodeFixed (v0 :: v1 :: v2 :: v3 :: rest) = none := by
  have hv : check_version (fromLE4 v0 v1 v2 v3) = false :=
    check_version_rejects_high_bit _ h
  simp [decodeFixed, hv]

/-- **T11c.** The decoder rejects any 4-byte-prefixed input whose decoded
version is below `ZCASH_BLOCK_VERSION = 4`. -/
theorem decode_rejects_below_min
    (v0 v1 v2 v3 : Nat) (rest : List Nat)
    (h : fromLE4 v0 v1 v2 v3 < ZCASH_BLOCK_VERSION) :
    decodeFixed (v0 :: v1 :: v2 :: v3 :: rest) = none := by
  have hv : check_version (fromLE4 v0 v1 v2 v3) = false :=
    check_version_rejects_below_min _ h
  simp [decodeFixed, hv]

/-! ### Round-trip -/

/-- `List.take n` of a list of length `≥ n` keeps its semantics; here the
list has length exactly 32. -/
private theorem take_32_of_exact (xs : List Nat) (h : xs.length = 32) :
    xs.take 32 = xs := by
  apply List.take_of_length_le
  omega

/-- `List.drop 32` of a 32-element list is empty. -/
private theorem drop_32_of_exact (xs : List Nat) (h : xs.length = 32) :
    xs.drop 32 = [] := by
  apply List.drop_eq_nil_of_le
  omega

/-- `take 32 (front ++ rest) = front` when `front` is exactly 32 bytes. -/
private theorem take32_append (front rest : List Nat)
    (h : front.length = 32) :
    (front ++ rest).take 32 = front := by
  rw [List.take_append_of_le_length (by omega), take_32_of_exact front h]

/-- `drop 32 (front ++ rest) = rest` when `front` is exactly 32 bytes. -/
private theorem drop32_append (front rest : List Nat)
    (h : front.length = 32) :
    (front ++ rest).drop 32 = rest := by
  rw [List.drop_append_of_le_length (by omega), drop_32_of_exact front h,
      List.nil_append]

/-- `has32` is `true` when the 32-byte prefix is present. -/
private theorem has32_append (front rest : List Nat)
    (h : front.length = 32) :
    has32 (front ++ rest) = true := by
  unfold has32
  rw [List.length_append, h]
  simp

/-- **T11.** Fixed-prefix round-trip: for every well-formed header,
encoding the fixed portion and then decoding it recovers exactly the
original header with no leftover bytes.

This is the central correctness statement for the model: it says the
encoder/decoder pair agrees on the set of well-formed headers and that
the fixed prefix is unambiguous. -/
theorem encode_decode_roundtrip (h : Header) (hw : WellFormed h) :
    decodeFixed (encodeFixed h) = some (h, []) := by
  have hck : check_version h.version = true := by
    rw [check_version_iff]
    exact ⟨hw.versionMin, hw.versionMax⟩
  have hv := version_roundtrip h hw
  have ht := time_roundtrip h hw
  have hb := bits_roundtrip h hw
  -- The encoded list as a right-nested cons of the four version bytes
  -- followed by `prevHash ++ merkleRoot ++ commitment ++ toLE4 time
  -- ++ toLE4 bits ++ nonce`.
  have hshape :
      encodeFixed h
        = (h.version % 256)
          :: ((h.version / 256) % 256)
          :: ((h.version / 65536) % 256)
          :: ((h.version / 16777216) % 256)
          :: (h.prevHash ++ (h.merkleRoot ++ (h.commitment
              ++ (toLE4 h.time ++ (toLE4 h.bits ++ h.nonce))))) := by
    unfold encodeFixed toLE4
    simp [List.append_assoc, List.cons_append]
  rw [hshape]
  -- After this `change`, the decoder will reduce the version match arm
  -- and the inner steps proceed by simple ite-true / ite-false collapses.
  change (let version := fromLE4
                        (h.version % 256) ((h.version / 256) % 256)
                        ((h.version / 65536) % 256) ((h.version / 16777216) % 256)
        if !check_version version then none
        else if !has32 (h.prevHash ++ (h.merkleRoot ++ (h.commitment
                          ++ (toLE4 h.time ++ (toLE4 h.bits ++ h.nonce)))))
             then none
        else
          let prev :=
            (h.prevHash ++ (h.merkleRoot ++ (h.commitment
              ++ (toLE4 h.time ++ (toLE4 h.bits ++ h.nonce))))).take 32
          let rest :=
            (h.prevHash ++ (h.merkleRoot ++ (h.commitment
              ++ (toLE4 h.time ++ (toLE4 h.bits ++ h.nonce))))).drop 32
          if !has32 rest then none
          else
            let merkle := rest.take 32
            let rest := rest.drop 32
            if !has32 rest then none
            else
              let commit := rest.take 32
              let rest := rest.drop 32
              match rest with
              | t0 :: t1 :: t2 :: t3 ::
                b0 :: b1 :: b2 :: b3 :: rest =>
                  let time := fromLE4 t0 t1 t2 t3
                  let bits := fromLE4 b0 b1 b2 b3
                  if !has32 rest then none
                  else
                    let nonce := rest.take 32
                    let rest := rest.drop 32
                    some ({ version, prevHash := prev, merkleRoot := merkle,
                            commitment := commit, time, bits, nonce }, rest)
              | _ => none)
       = some (h, [])
  -- Reduce the version computation.  After `hv`, the `let version := ...`
  -- binder still holds `version`; `change` peels it.
  rw [hv]
  change (if !check_version h.version then none
        else if !has32 (h.prevHash ++ (h.merkleRoot ++ (h.commitment
                          ++ (toLE4 h.time ++ (toLE4 h.bits ++ h.nonce)))))
             then none
        else
          let prev :=
            (h.prevHash ++ (h.merkleRoot ++ (h.commitment
              ++ (toLE4 h.time ++ (toLE4 h.bits ++ h.nonce))))).take 32
          let rest :=
            (h.prevHash ++ (h.merkleRoot ++ (h.commitment
              ++ (toLE4 h.time ++ (toLE4 h.bits ++ h.nonce))))).drop 32
          if !has32 rest then none
          else
            let merkle := rest.take 32
            let rest := rest.drop 32
            if !has32 rest then none
            else
              let commit := rest.take 32
              let rest := rest.drop 32
              match rest with
              | t0 :: t1 :: t2 :: t3 ::
                b0 :: b1 :: b2 :: b3 :: rest =>
                  let time := fromLE4 t0 t1 t2 t3
                  let bits := fromLE4 b0 b1 b2 b3
                  if !has32 rest then none
                  else
                    let nonce := rest.take 32
                    let rest := rest.drop 32
                    some ({ version := h.version, prevHash := prev,
                            merkleRoot := merkle, commitment := commit,
                            time, bits, nonce }, rest)
              | _ => none)
       = some (h, [])
  rw [hck]
  -- The "version check" `if !true` collapses.
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  -- Step through prev: `has32` is true; take/drop extract prevHash and rest.
  rw [has32_append h.prevHash _ hw.prevLen,
      take32_append h.prevHash _ hw.prevLen,
      drop32_append h.prevHash _ hw.prevLen]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  -- Step through merkle.
  rw [has32_append h.merkleRoot _ hw.merkleLen,
      take32_append h.merkleRoot _ hw.merkleLen,
      drop32_append h.merkleRoot _ hw.merkleLen]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  -- Step through commitment.
  rw [has32_append h.commitment _ hw.commitLen,
      take32_append h.commitment _ hw.commitLen,
      drop32_append h.commitment _ hw.commitLen]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  -- Now `rest` is `toLE4 h.time ++ (toLE4 h.bits ++ h.nonce)`.  Expand
  -- `toLE4`s to expose the 8 cons cells the inner match consumes.
  have hexp : toLE4 h.time ++ (toLE4 h.bits ++ h.nonce)
            = (h.time % 256) :: ((h.time / 256) % 256)
              :: ((h.time / 65536) % 256) :: ((h.time / 16777216) % 256)
              :: (h.bits % 256) :: ((h.bits / 256) % 256)
              :: ((h.bits / 65536) % 256) :: ((h.bits / 16777216) % 256)
              :: h.nonce := by
    unfold toLE4
    simp [List.cons_append]
  rw [hexp]
  -- The inner match reduces against the 9 explicit cons cells.  The
  -- result of the beta-step is shown explicitly.
  change (if !has32 h.nonce then none
        else
          some ({ version := h.version, prevHash := h.prevHash,
                  merkleRoot := h.merkleRoot, commitment := h.commitment,
                  time := fromLE4 (h.time % 256) ((h.time / 256) % 256)
                                  ((h.time / 65536) % 256) ((h.time / 16777216) % 256),
                  bits := fromLE4 (h.bits % 256) ((h.bits / 256) % 256)
                                  ((h.bits / 65536) % 256) ((h.bits / 16777216) % 256),
                  nonce := h.nonce.take 32 }, h.nonce.drop 32))
       = some (h, [])
  -- Substitute `fromLE4` for time and bits.
  rw [ht, hb]
  -- Final nonce check.
  have hnonce_has : has32 h.nonce = true := by
    unfold has32
    rw [hw.nonceLen]; simp
  rw [hnonce_has]
  simp only [Bool.not_true, Bool.false_eq_true, if_false]
  rw [take_32_of_exact h.nonce hw.nonceLen, drop_32_of_exact h.nonce hw.nonceLen]

/-! ### Injectivity, derived from round-trip

The encoder's injectivity over well-formed headers is the natural
consequence of the round-trip theorem.  We derive the whole-record
injectivity statement, then read per-field injectivity off it. -/

/-- **T12.** The encoder is injective on well-formed headers. -/
theorem encode_injective (h₁ h₂ : Header)
    (hw₁ : WellFormed h₁) (hw₂ : WellFormed h₂)
    (heq : encodeFixed h₁ = encodeFixed h₂) :
    h₁ = h₂ := by
  have e1 := encode_decode_roundtrip h₁ hw₁
  have e2 := encode_decode_roundtrip h₂ hw₂
  rw [heq] at e1
  -- Now `e1 : decodeFixed (encodeFixed h₂) = some (h₁, [])`
  -- and `e2 : decodeFixed (encodeFixed h₂) = some (h₂, [])`.
  have hpair : (h₁, ([] : List Nat)) = (h₂, ([] : List Nat)) := by
    have := e1.symm.trans e2
    exact Option.some.inj this
  exact (Prod.mk.injEq ..).mp hpair |>.1

/-- **T13.** Two well-formed headers with identical encodings have
identical `version` fields. -/
theorem encode_injective_version (h₁ h₂ : Header)
    (hw₁ : WellFormed h₁) (hw₂ : WellFormed h₂)
    (heq : encodeFixed h₁ = encodeFixed h₂) :
    h₁.version = h₂.version := by
  rw [encode_injective h₁ h₂ hw₁ hw₂ heq]

/-- **T14.** `time` is recoverable. -/
theorem encode_injective_time (h₁ h₂ : Header)
    (hw₁ : WellFormed h₁) (hw₂ : WellFormed h₂)
    (heq : encodeFixed h₁ = encodeFixed h₂) :
    h₁.time = h₂.time := by
  rw [encode_injective h₁ h₂ hw₁ hw₂ heq]

/-- **T15.** `bits` is recoverable. -/
theorem encode_injective_bits (h₁ h₂ : Header)
    (hw₁ : WellFormed h₁) (hw₂ : WellFormed h₂)
    (heq : encodeFixed h₁ = encodeFixed h₂) :
    h₁.bits = h₂.bits := by
  rw [encode_injective h₁ h₂ hw₁ hw₂ heq]

/-- **T16.** `prevHash` is recoverable. -/
theorem encode_injective_prevHash (h₁ h₂ : Header)
    (hw₁ : WellFormed h₁) (hw₂ : WellFormed h₂)
    (heq : encodeFixed h₁ = encodeFixed h₂) :
    h₁.prevHash = h₂.prevHash := by
  rw [encode_injective h₁ h₂ hw₁ hw₂ heq]

/-- **T17.** `merkleRoot` is recoverable. -/
theorem encode_injective_merkleRoot (h₁ h₂ : Header)
    (hw₁ : WellFormed h₁) (hw₂ : WellFormed h₂)
    (heq : encodeFixed h₁ = encodeFixed h₂) :
    h₁.merkleRoot = h₂.merkleRoot := by
  rw [encode_injective h₁ h₂ hw₁ hw₂ heq]

/-- **T18.** `commitment` is recoverable. -/
theorem encode_injective_commitment (h₁ h₂ : Header)
    (hw₁ : WellFormed h₁) (hw₂ : WellFormed h₂)
    (heq : encodeFixed h₁ = encodeFixed h₂) :
    h₁.commitment = h₂.commitment := by
  rw [encode_injective h₁ h₂ hw₁ hw₂ heq]

/-- **T19.** `nonce` is recoverable. -/
theorem encode_injective_nonce (h₁ h₂ : Header)
    (hw₁ : WellFormed h₁) (hw₂ : WellFormed h₂)
    (heq : encodeFixed h₁ = encodeFixed h₂) :
    h₁.nonce = h₂.nonce := by
  rw [encode_injective h₁ h₂ hw₁ hw₂ heq]

end Zebra.BlockHeader
