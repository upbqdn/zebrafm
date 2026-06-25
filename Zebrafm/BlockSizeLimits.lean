import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Block size limits from `zebra-chain/src/block/serialize.rs` and
`zebra-chain/src/serialization/zcash_serialize.rs`

Zcash deserialisation enforces two byte-length bounds on incoming data:

  * `MAX_BLOCK_BYTES = 2_000_000` — the maximum size of a block (and, post-Sapling,
    of a transaction).
  * `MAX_PROTOCOL_MESSAGE_LEN = 2 * 1024 * 1024 = 2_097_152` — the maximum size of
    a network protocol message.

Both limits are encoded as `≤`-checks on a `usize` or `u64`. We model the
checked size as `Nat` and the predicates as ordinary `Bool`/`Prop` conjunctions.

The `sizeCheck` helper captures the common shape of these guard-rails:
"accept iff the candidate size is `≤ bound`". We prove that it is monotone in
the bound, monotone (anti-tone) in the candidate, exactly bounds the accepted
set, and is consistent with the two named limits.
-/

namespace Zebra.BlockSizeLimits

/-- `MAX_BLOCK_BYTES`: maximum size of a Zcash block, in bytes.
Source: `zebra-chain/src/block/serialize.rs:24` -/
def MAX_BLOCK_BYTES : Nat := 2_000_000

/-- `MAX_PROTOCOL_MESSAGE_LEN`: maximum size of a Zcash protocol message.
Source: `zebra-chain/src/serialization/zcash_serialize.rs:11` -/
def MAX_PROTOCOL_MESSAGE_LEN : Nat := 2 * 1024 * 1024

/-- The generic "size ≤ bound" predicate used by the deserialiser to guard
allocations and `Read::take` calls.
Source: `zebra-chain/src/block/serialize.rs:158` (`reader.take(MAX_BLOCK_BYTES)`)
and `zebra-chain/src/serialization/zcash_deserialize.rs` (length checks). -/
def sizeCheck (size bound : Nat) : Bool := size ≤ bound

/-- Specialisation: accept iff `size ≤ MAX_BLOCK_BYTES`. -/
def blockSizeOk (size : Nat) : Bool := sizeCheck size MAX_BLOCK_BYTES

/-- Specialisation: accept iff `size ≤ MAX_PROTOCOL_MESSAGE_LEN`. -/
def protocolMessageSizeOk (size : Nat) : Bool :=
  sizeCheck size MAX_PROTOCOL_MESSAGE_LEN

/-! ## Theorems -/

/-- **T1.** `sizeCheck` accepts iff the size is within the bound. -/
theorem sizeCheck_iff (size bound : Nat) :
    sizeCheck size bound = true ↔ size ≤ bound := by
  unfold sizeCheck
  exact decide_eq_true_iff

/-- **T2.** `sizeCheck` rejects every size strictly above the bound. -/
theorem sizeCheck_reject_above (size bound : Nat) (h : bound < size) :
    sizeCheck size bound = false := by
  unfold sizeCheck
  exact decide_eq_false (by omega)

/-- **T3.** `sizeCheck` is monotone in the bound: a larger bound accepts every
size the smaller bound accepts. -/
theorem sizeCheck_monotone_bound (size b₁ b₂ : Nat) (hb : b₁ ≤ b₂)
    (h : sizeCheck size b₁ = true) : sizeCheck size b₂ = true := by
  rw [sizeCheck_iff] at h ⊢
  exact h.trans hb

/-- **T4.** `sizeCheck` is anti-tone in the size: a smaller size is accepted
whenever a larger one is. -/
theorem sizeCheck_antitone_size (s₁ s₂ bound : Nat) (hs : s₁ ≤ s₂)
    (h : sizeCheck s₂ bound = true) : sizeCheck s₁ bound = true := by
  rw [sizeCheck_iff] at h ⊢
  exact hs.trans h

/-- **T5.** The two named limits satisfy `MAX_BLOCK_BYTES ≤ MAX_PROTOCOL_MESSAGE_LEN`,
so anything that fits in a block also fits in a protocol message. -/
theorem block_le_protocol :
    MAX_BLOCK_BYTES ≤ MAX_PROTOCOL_MESSAGE_LEN := by
  unfold MAX_BLOCK_BYTES MAX_PROTOCOL_MESSAGE_LEN
  decide

/-- **T6.** Every accepted block fits in a protocol message. -/
theorem blockOk_implies_protocolOk (size : Nat)
    (h : blockSizeOk size = true) : protocolMessageSizeOk size = true := by
  unfold blockSizeOk protocolMessageSizeOk at *
  exact sizeCheck_monotone_bound size _ _ block_le_protocol h

/-- **T7.** The boundary value is exactly the largest accepted size. -/
theorem sizeCheck_at_bound (bound : Nat) : sizeCheck bound bound = true := by
  rw [sizeCheck_iff]

/-- **T8.** One past the bound is rejected. -/
theorem sizeCheck_just_above (bound : Nat) :
    sizeCheck (bound + 1) bound = false := by
  exact sizeCheck_reject_above _ _ (by omega)

/-! ## Bonus theorems -/

/-- **B1.** The named constants have their expected concrete values. -/
theorem MAX_BLOCK_BYTES_value : MAX_BLOCK_BYTES = 2_000_000 := rfl

/-- **B2.** `MAX_PROTOCOL_MESSAGE_LEN = 2_097_152`. -/
theorem MAX_PROTOCOL_MESSAGE_LEN_value :
    MAX_PROTOCOL_MESSAGE_LEN = 2_097_152 := by decide

/-- **B3.** The slack between the two limits is `97_152` bytes. -/
theorem protocol_minus_block :
    MAX_PROTOCOL_MESSAGE_LEN - MAX_BLOCK_BYTES = 97_152 := by decide

/-- **B4.** Zero size is always accepted (trivially fits any bound). -/
theorem sizeCheck_zero (bound : Nat) : sizeCheck 0 bound = true := by
  rw [sizeCheck_iff]; exact Nat.zero_le _

/-- **B5.** `blockSizeOk` is decidable as a closed proposition on the boundary. -/
theorem blockSizeOk_at_max : blockSizeOk MAX_BLOCK_BYTES = true := by
  unfold blockSizeOk; exact sizeCheck_at_bound _

/-- **B6.** `protocolMessageSizeOk` rejects `MAX_PROTOCOL_MESSAGE_LEN + 1`. -/
theorem protocolMessageSizeOk_just_above :
    protocolMessageSizeOk (MAX_PROTOCOL_MESSAGE_LEN + 1) = false := by
  unfold protocolMessageSizeOk; exact sizeCheck_just_above _

end Zebra.BlockSizeLimits
