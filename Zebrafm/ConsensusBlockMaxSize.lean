import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Consensus block max-byte-size check

The 2 MB block-size cap is the oldest, hardest consensus rule a Zebra full
validator enforces. Quoting `zebra-chain/src/block/serialize.rs:151-158`:

> # Consensus
>
> > The size of a block MUST be less than or equal to 2000000 bytes.
>
> https://zips.z.cash/protocol/protocol.pdf#blockheader
>
> ```rust
> // If the limit is reached, we'll get an UnexpectedEof error
> let limited_reader = &mut reader.take(MAX_BLOCK_BYTES);
> ```

The cap itself is defined at `zebra-chain/src/block/serialize.rs:24`:

```rust
pub const MAX_BLOCK_BYTES: u64 = 2_000_000;
```

This module models that *consensus-level* enforcement: a serialized block —
modelled as a `List Nat` (its byte body) — is accepted iff its length is
`≤ MAX_BLOCK_BYTES`. This is distinct from the sibling
`Zebrafm.BlockSizeLimits` module:

* `BlockSizeLimits` reasons about the abstract `sizeCheck size bound`
  predicate over a generic `Nat` size.
* This module pins the actual *block* check to a `List Nat`-valued
  byte body (matching `reader.take(MAX_BLOCK_BYTES)`), and proves the
  consensus rule in terms of `List.length`. It also wires the rule into
  a compound `blockCheck` that pairs the byte cap with a second
  bounded-resource cap (sigops, modelled after
  `zebra-consensus/src/block.rs:141`'s `MAX_BLOCK_SIGOPS = 20_000`), so
  the byte-cap projection can be shown sound under composition.

Concrete vectors below match the `zebra-chain/src/block/tests/vectors.rs`
acceptance/rejection vectors at lines `338`, `354`, `375`, `389`.
-/

namespace Zebra.ConsensusBlockMaxSize

/-! ## Constants -/

/-- `MAX_BLOCK_BYTES`: the upstream byte cap on a serialized block body.
Source: `zebra-chain/src/block/serialize.rs:24`. -/
def MAX_BLOCK_BYTES : Nat := 2_000_000

/-- A representative *genesis-block* serialized size. The Bitcoin/Zcash
genesis block headers serialize to a few hundred bytes; we use a concrete
small-block witness `≤ 2000` bytes to stand in for "any genesis-sized
block". The exact byte count of the Zcash mainnet genesis block is on the
order of 1 kB. -/
def GENESIS_REPRESENTATIVE_BYTES : Nat := 2_000

/-- `MAX_BLOCK_SIGOPS`: the per-block legacy sigops cap, enforced
alongside the byte cap by `zebra-consensus`.
Source: `zebra-consensus/src/block.rs:141`. -/
def MAX_BLOCK_SIGOPS : Nat := 20_000

/-! ## The byte-cap check -/

/-- The Rust check, modelled directly: a serialized block body fits iff
its length is `≤ MAX_BLOCK_BYTES`. This is the same predicate
`reader.take(MAX_BLOCK_BYTES)` enforces in
`zebra-chain/src/block/serialize.rs:158`. -/
def passesSizeCheck (body : List Nat) : Bool :=
  decide (body.length ≤ MAX_BLOCK_BYTES)

/-- A compound block check pairing the byte cap with a sigops cap.
Mirrors the composition pattern in `zebra-consensus/src/block.rs:320`
where the sigops check sits next to the byte cap. We model the sigops as a
plain `Nat` parameter rather than parsing the body — the algebraic
content here is the composition behaviour, not the parser. -/
def blockCheck (body : List Nat) (sigops : Nat) : Bool :=
  passesSizeCheck body && decide (sigops ≤ MAX_BLOCK_SIGOPS)

/-! ## Theorems -/

/-- **T1 (iff form).** The byte-cap check is exactly the inequality
`body.length ≤ MAX_BLOCK_BYTES`. -/
theorem passesSizeCheck_iff (body : List Nat) :
    passesSizeCheck body = true ↔ body.length ≤ MAX_BLOCK_BYTES := by
  unfold passesSizeCheck
  exact decide_eq_true_iff

/-- **T2 (≤ MAX_BLOCK_BYTES accepted).** Any serialized body whose length is
at most `MAX_BLOCK_BYTES` passes the size check. This is the positive half
of the consensus rule "The size of a block MUST be less than or equal to
2000000 bytes". -/
theorem at_or_below_max_accepted (body : List Nat)
    (h : body.length ≤ MAX_BLOCK_BYTES) :
    passesSizeCheck body = true := by
  rw [passesSizeCheck_iff]; exact h

/-- **T3 (length + 1 rejected).** A body one byte longer than the cap is
rejected. This is the "limit + 1 fails" vector demanded by the task: any
body that exceeds `MAX_BLOCK_BYTES` by even a single byte triggers the
`UnexpectedEof` failure path of `reader.take(MAX_BLOCK_BYTES)`. -/
theorem just_above_max_rejected (body : List Nat)
    (h : body.length = MAX_BLOCK_BYTES + 1) :
    passesSizeCheck body = false := by
  unfold passesSizeCheck
  rw [h]
  exact decide_eq_false (by omega)

/-- **T4 (every overlong body rejected).** Stronger form of T3: any body
strictly above the cap, regardless of how far above, is rejected. -/
theorem above_max_rejected (body : List Nat)
    (h : MAX_BLOCK_BYTES < body.length) :
    passesSizeCheck body = false := by
  unfold passesSizeCheck
  exact decide_eq_false (by omega)

/-- **T5 (antitone in body length).** Shortening a body never invalidates
it: if a longer prefix-or-superset passes, every shorter list does too.
Useful for reasoning about partial parses. -/
theorem passesSizeCheck_antitone (b₁ b₂ : List Nat)
    (hlen : b₁.length ≤ b₂.length)
    (h : passesSizeCheck b₂ = true) :
    passesSizeCheck b₁ = true := by
  rw [passesSizeCheck_iff] at h ⊢
  exact hlen.trans h

/-- **T6 (monotone in cap).** The byte-cap predicate is monotone in the
cap: extending the cap can only enlarge the accepted set. This is the
algebraic content of "raising `MAX_BLOCK_BYTES` is backward compatible";
it pairs the lower-level `decide`-cap monotonicity with the named
constant. -/
theorem cap_monotone (body : List Nat) (capLow capHi : Nat)
    (hcap : capLow ≤ capHi)
    (h : decide (body.length ≤ capLow) = true) :
    decide (body.length ≤ capHi) = true := by
  have hlen : body.length ≤ capLow := of_decide_eq_true h
  exact decide_eq_true (hlen.trans hcap)

/-! ## Concrete acceptance / rejection vectors -/

/-- **T7 (genesis-sized accepted).** A genesis-sized representative body
(here taken as `2_000` bytes — well above the actual Zcash genesis block
serialization length and well below `MAX_BLOCK_BYTES`) is accepted.
Mirrors `zebra-chain/src/block/tests/vectors.rs:338` asserting
`data.len() <= MAX_BLOCK_BYTES as usize` for sub-cap blocks. -/
theorem genesis_sized_accepted (body : List Nat)
    (h : body.length = GENESIS_REPRESENTATIVE_BYTES) :
    passesSizeCheck body = true := by
  rw [passesSizeCheck_iff, h]
  unfold GENESIS_REPRESENTATIVE_BYTES MAX_BLOCK_BYTES
  decide

/-- **T8 (max-sized exactly accepted).** A body of length *exactly*
`MAX_BLOCK_BYTES` is accepted (the boundary is inclusive). Matches the
`<=` in `data.len() <= MAX_BLOCK_BYTES as usize` at
`block/tests/vectors.rs:338,375`. -/
theorem max_sized_accepted (body : List Nat)
    (h : body.length = MAX_BLOCK_BYTES) :
    passesSizeCheck body = true := by
  rw [passesSizeCheck_iff, h]

/-- **T9 (oversize rejection vector).** Matches
`block/tests/vectors.rs:354,389`: a body strictly above the cap is
rejected. Stated as a concrete pin at the canonical witness
`MAX_BLOCK_BYTES + 1`. -/
theorem oversize_vector_rejected (body : List Nat)
    (h : body.length = MAX_BLOCK_BYTES + 1) :
    passesSizeCheck body = false :=
  just_above_max_rejected body h

/-! ## Composition with the sigops cap -/

/-- **T10 (compound accept).** The compound `blockCheck` accepts iff
both the byte cap and the sigops cap accept. This is the propositional
form of the `&&` in `blockCheck`'s definition. -/
theorem blockCheck_iff (body : List Nat) (sigops : Nat) :
    blockCheck body sigops = true ↔
      (body.length ≤ MAX_BLOCK_BYTES ∧ sigops ≤ MAX_BLOCK_SIGOPS) := by
  unfold blockCheck
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨h1, h2⟩
    rw [passesSizeCheck_iff] at h1
    exact ⟨h1, of_decide_eq_true h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [passesSizeCheck_iff]; exact h1
    · exact decide_eq_true h2

/-- **T11 (compound projects to byte cap).** If the compound check accepts,
the byte cap alone accepts. This is the soundness direction needed when
the byte cap is queried in isolation by a downstream caller (e.g. the
deserializer in `zebra-chain` runs only the byte cap; the sigops cap is
re-checked in `zebra-consensus`). -/
theorem blockCheck_implies_size (body : List Nat) (sigops : Nat)
    (h : blockCheck body sigops = true) :
    passesSizeCheck body = true := by
  rw [blockCheck_iff] at h
  rw [passesSizeCheck_iff]
  exact h.1

/-- **T12 (compound rejects on byte cap alone).** If the byte cap rejects,
the compound check rejects, *regardless of the sigops count*. The
deserializer enforces the byte cap before sigops counting can even
happen, so this is the "size cap is final" invariant. -/
theorem blockCheck_rejects_oversize (body : List Nat) (sigops : Nat)
    (h : MAX_BLOCK_BYTES < body.length) :
    blockCheck body sigops = false := by
  unfold blockCheck
  rw [above_max_rejected body h]
  simp

/-! ## Concrete-value pins -/

/-- **B1 (numerical value).** Pins `MAX_BLOCK_BYTES` so any future
constant-change in `zebra-chain/src/block/serialize.rs:24` breaks the
build. -/
theorem MAX_BLOCK_BYTES_value : MAX_BLOCK_BYTES = 2_000_000 := rfl

/-- **B2 (sigops value).** Pins the sigops cap from
`zebra-consensus/src/block.rs:141`. -/
theorem MAX_BLOCK_SIGOPS_value : MAX_BLOCK_SIGOPS = 20_000 := rfl

/-- **B3 (genesis representative is well below cap).** The slack between
the genesis-sized vector and the cap is the expected ~2 MB minus 2 kB.
Pin it so a future constant edit cannot silently push the genesis
witness above the cap. -/
theorem genesis_well_below_cap :
    MAX_BLOCK_BYTES - GENESIS_REPRESENTATIVE_BYTES = 1_998_000 := by decide

/-- **B4 (empty body accepted).** A zero-length body trivially fits — the
`reader.take(MAX_BLOCK_BYTES)` cap never triggers on an empty stream. -/
theorem empty_body_accepted : passesSizeCheck [] = true := by
  rw [passesSizeCheck_iff]; exact Nat.zero_le _

/-- **B5 (compound check on genesis-sized + tiny sigops).** A genesis-sized
body with no sigops passes the compound check. This is the canonical
"happy-path" vector for downstream callers that want to test the
composition. -/
theorem compound_genesis_happy_path (body : List Nat)
    (h : body.length = GENESIS_REPRESENTATIVE_BYTES) :
    blockCheck body 0 = true := by
  rw [blockCheck_iff, h]
  refine ⟨?_, Nat.zero_le _⟩
  unfold GENESIS_REPRESENTATIVE_BYTES MAX_BLOCK_BYTES
  decide

end Zebra.ConsensusBlockMaxSize
