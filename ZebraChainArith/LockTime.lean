import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# LockTime serialisation from `zebra-chain/src/transaction/lock_time.rs`

The `LockTime` field of a Bitcoin/Zcash transaction is a single u32 that is
interpreted by magnitude:

  * `n < 500_000_000` → a block-height lock,
  * `n ≥ 500_000_000` → a Unix-timestamp lock.

Serialisation is the raw little-endian u32; deserialisation branches on the
threshold.

We model:
  * the value as `Nat` (with `n ≤ u32::MAX = 2^32 - 1`),
  * the wire bytes as `List Nat` (each byte modelled as a `Nat`),
  * the enum as a `Sum` (`heightOrTime`) inhabited by one of the two branches.
-/

namespace Zebra.LockTime

/-- The Bitcoin/Zcash lock-time / timestamp threshold. -/
def MIN_TIMESTAMP : Nat := 500_000_000

/-- `u32::MAX`: the upper bound on a LockTime value. -/
def U32_MAX : Nat := 4_294_967_295

/-- A `LockTime`: either a block-height lock or a timestamp lock. -/
inductive LockTime
  | height (n : Nat)
  | time   (t : Nat)
  deriving DecidableEq, Repr

/-! ## Helpers -/

/-- Little-endian 4-byte encoding. -/
def toLE4 (n : Nat) : List Nat :=
  [n % 256, (n / 256) % 256, (n / 65536) % 256, (n / 16777216) % 256]

/-- Little-endian 4-byte decoding. -/
def fromLE4 (b0 b1 b2 b3 : Nat) : Nat :=
  b0 + b1 * 256 + b2 * 65536 + b3 * 16777216

/-! ## Encoder and decoder -/

/-- `LockTime::zcash_serialize`: writes the underlying u32 as little-endian
bytes. The encoder is total over both branches because the wire format is
the same. -/
def encode : LockTime → List Nat
  | .height n => toLE4 n
  | .time   t => toLE4 t

/-- `LockTime::zcash_deserialize`: reads 4 LE bytes and branches on the
`MIN_TIMESTAMP` threshold. -/
def decode (bytes : List Nat) : Option (LockTime × List Nat) :=
  match bytes with
  | b0 :: b1 :: b2 :: b3 :: rest =>
    let n := fromLE4 b0 b1 b2 b3
    if n < MIN_TIMESTAMP then
      some (.height n, rest)
    else
      some (.time n, rest)
  | _ => none

/-! ## Theorems -/

/-- A helper: little-endian round-trip on 4 bytes for any u32 input. -/
private theorem le4_roundtrip (n : Nat) (h : n ≤ U32_MAX) :
    fromLE4 (n % 256) ((n / 256) % 256) ((n / 65536) % 256) ((n / 16777216) % 256) = n := by
  unfold fromLE4 U32_MAX at *; omega

/-- **T1.** Encoder length is exactly 4 bytes for any input. -/
theorem encode_length (lt : LockTime) : (encode lt).length = 4 := by
  cases lt <;> simp [encode, toLE4]

/-- **T2.** Round-trip on a height-locked value within the valid range. -/
theorem roundtrip_height (n : Nat) (h1 : n < MIN_TIMESTAMP) (h2 : n ≤ U32_MAX) :
    decode (encode (.height n)) = some (.height n, []) := by
  show decode (toLE4 n) = some (.height n, [])
  unfold toLE4 decode
  have hrt := le4_roundtrip n h2
  simp [hrt, h1]

/-- **T3.** Round-trip on a timestamp-locked value at or above the threshold. -/
theorem roundtrip_time (t : Nat) (h1 : MIN_TIMESTAMP ≤ t) (h2 : t ≤ U32_MAX) :
    decode (encode (.time t)) = some (.time t, []) := by
  show decode (toLE4 t) = some (.time t, [])
  unfold toLE4 decode
  have hrt := le4_roundtrip t h2
  have hge : ¬ t < MIN_TIMESTAMP := by omega
  simp [hrt, hge]

/-- **T4.** Round-trip universal: for any valid LockTime, encoding then
decoding recovers the original. -/
theorem roundtrip_universal (lt : LockTime) (h : ∀ n, lt = .height n → n ≤ U32_MAX)
    (h' : ∀ t, lt = .time t → t ≤ U32_MAX)
    (hValidH : ∀ n, lt = .height n → n < MIN_TIMESTAMP)
    (hValidT : ∀ t, lt = .time t → MIN_TIMESTAMP ≤ t) :
    decode (encode lt) = some (lt, []) := by
  cases lt with
  | height n =>
    exact roundtrip_height n (hValidH n rfl) (h n rfl)
  | time t =>
    exact roundtrip_time t (hValidT t rfl) (h' t rfl)

/-- **T5.** The decoder is total: it returns `Some` for any 4-byte input
and `None` for shorter input. -/
theorem decode_total (bytes : List Nat) :
    (decode bytes).isSome ∨ decode bytes = none := by
  rcases h : decode bytes with _ | _
  · right; rfl
  · left; simp

/-- **T6.** The decoder rejects fewer-than-4-byte input. -/
theorem decode_empty : decode [] = none := rfl
theorem decode_one (b0 : Nat) : decode [b0] = none := rfl
theorem decode_two (b0 b1 : Nat) : decode [b0, b1] = none := rfl
theorem decode_three (b0 b1 b2 : Nat) : decode [b0, b1, b2] = none := rfl

end Zebra.LockTime
