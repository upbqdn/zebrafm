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

/-- The Bitcoin/Zcash lock-time / timestamp threshold
(`LockTime::MIN_TIMESTAMP` in Rust). -/
def MIN_TIMESTAMP : Nat := 500_000_000

/-- `u32::MAX`: the upper bound on a LockTime value, and also the upper bound
on `LockTime::Time` (`LockTime::MAX_TIMESTAMP` in Rust). -/
def U32_MAX : Nat := 4_294_967_295

/-- `LockTime::MAX_HEIGHT` in Rust: the largest value that the `Height` variant
may carry. The Rust enum makes no syntactic distinction (both variants wrap a
`u32`-sized value), but a value `≥ MIN_TIMESTAMP` written into a `Height`
variant will decode back as `Time` (see `height_collides_above_threshold`),
so the `MAX_HEIGHT = MIN_TIMESTAMP - 1` invariant is the user's
responsibility. -/
def MAX_HEIGHT : Nat := MIN_TIMESTAMP - 1

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

/-- **T2b.** Round-trip on a height-locked value, stated with the tighter
`MAX_HEIGHT` bound that mirrors the Rust `LockTime::MAX_HEIGHT` invariant.
This implies the U32 bound on `n` (since `MAX_HEIGHT < U32_MAX`) and the
threshold bound. -/
theorem roundtrip_height_strict (n : Nat) (h : n ≤ MAX_HEIGHT) :
    decode (encode (.height n)) = some (.height n, []) := by
  unfold MAX_HEIGHT at h
  have h1 : n < MIN_TIMESTAMP := by
    unfold MIN_TIMESTAMP at *; omega
  have h2 : n ≤ U32_MAX := by
    unfold MIN_TIMESTAMP U32_MAX at *; omega
  exact roundtrip_height n h1 h2

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

/-- **T5.** The decoder accepts any input of at least 4 bytes. This is the
non-trivial direction: it shows that no 4-byte prefix can defeat `decode`,
which matches the Rust deserializer's freedom from input-validation
panics on the prefix length. -/
theorem decode_succeeds_on_4bytes
    (b0 b1 b2 b3 : Nat) (rest : List Nat) :
    (decode (b0 :: b1 :: b2 :: b3 :: rest)).isSome := by
  show (if fromLE4 b0 b1 b2 b3 < MIN_TIMESTAMP
        then some (LockTime.height (fromLE4 b0 b1 b2 b3), rest)
        else some (LockTime.time (fromLE4 b0 b1 b2 b3), rest)).isSome = true
  split <;> rfl

/-- **T6.** The decoder rejects fewer-than-4-byte input. -/
theorem decode_empty : decode [] = none := rfl
theorem decode_one (b0 : Nat) : decode [b0] = none := rfl
theorem decode_two (b0 b1 : Nat) : decode [b0, b1] = none := rfl
theorem decode_three (b0 b1 b2 : Nat) : decode [b0, b1, b2] = none := rfl

/-- **T7.** Variant collision at the threshold: writing `n ≥ MIN_TIMESTAMP`
into a `Height` value and round-tripping recovers a `Time` value, not the
original `Height`. This is the semantic gap noted in the Rust source
(`Height` values above `MAX_HEIGHT` cannot be distinguished from `Time`
values on the wire), and explains why `MAX_HEIGHT = MIN_TIMESTAMP - 1` is
a user-side invariant rather than a type-level one. -/
theorem height_collides_above_threshold
    (n : Nat) (h1 : MIN_TIMESTAMP ≤ n) (h2 : n ≤ U32_MAX) :
    decode (encode (.height n)) = some (.time n, []) := by
  show decode (toLE4 n) = some (.time n, [])
  unfold toLE4 decode
  have hrt := le4_roundtrip n h2
  have hnlt : ¬ n < MIN_TIMESTAMP := by omega
  simp [hrt, hnlt]

/-- **T8.** Concrete collision witness at the threshold itself: encoding
`Height 500_000_000` and decoding yields `Time 500_000_000`. This is the
smallest input where the collision is observable. -/
theorem height_collision_at_min_timestamp :
    decode (encode (.height MIN_TIMESTAMP)) = some (.time MIN_TIMESTAMP, []) := by
  apply height_collides_above_threshold MIN_TIMESTAMP (le_refl _)
  unfold MIN_TIMESTAMP U32_MAX; omega

/-- **T9.** Totality of the `Time` branch decoder for any in-range Nat.
In Rust this is `Utc.timestamp_opt(n, 0).single().expect(...)`, which has
a panic site that is statically unreachable because every `u32` Unix
timestamp falls in `Utc`'s representable range. Our `Nat` model carries
no chrono dependency, so totality reduces to "the threshold branch
returns `some`" — which we discharge here as a witness that the model
faithfully reflects the panic-freedom of the Rust deserializer for all
in-range inputs. -/
theorem decode_time_branch_total (n : Nat)
    (h1 : MIN_TIMESTAMP ≤ n) (h2 : n ≤ U32_MAX) :
    decode (toLE4 n) = some (.time n, []) := by
  unfold toLE4 decode
  have hrt := le4_roundtrip n h2
  have hnlt : ¬ n < MIN_TIMESTAMP := by omega
  simp [hrt, hnlt]

end Zebra.LockTime
