import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Equihash parameters from `zebra-chain/src/work/equihash.rs`

Zcash's Equihash proof-of-work is parameterised by `(n, k) = (200, 9)` on
Mainnet and Testnet. The hard-coded constants in
`zebra-chain/src/work/equihash.rs` follow directly from these parameters:

  * The solution length (`SOLUTION_SIZE = 1344`) is the encoded length of
    `2^k` k-bit indices, each padded to `n/(k+1) + 1` bits, packed into
    bytes:

    `solutionLengthBytes(n, k) = 2^k * (n / (k+1) + 1) / 8`

    For `(n, k) = (200, 9)`: `2^9 * (200/10 + 1) / 8 = 512 * 21 / 8 = 1344`.
    Source: `zebra-chain/src/work/equihash.rs:31`
    (`pub(crate) const SOLUTION_SIZE: usize = 1344`).

  * On the wire the solution is preceded by a 3-byte CompactSize prefix
    (`0xfd 0x40 0x05`, the band-2 encoding for `1344`), so the total wire
    size is `3 + 1344 = 1347` bytes.
    Source: `zebra-chain/src/work/equihash.rs:257`
    (`impl ZcashSerialize for Solution`).

  * Equihash's birthday-collision count at the leaves is `2^(k+1) = 1024`
    (a chain of `k` collision rounds doubles the input width each round,
    so the number of leaves is `2^(k+1)`).
    Source: `zebra-chain/src/work/equihash.rs:76-78` (`let n = 200; let k = 9;`).

  * The verifier-input length (`Solution::INPUT_LENGTH`) is exactly
    `4 + 32 * 3 + 4 * 2 = 108` bytes — the part of the block header that
    is held constant during the solver run (version + 3 hashes + 2
    32-bit timestamp/difficulty fields, excluding the 32-byte nonce and
    solution).
    Source: `zebra-chain/src/work/equihash.rs:60`
    (`pub const INPUT_LENGTH: usize = 4 + 32 * 3 + 4 * 2`).

This module models the parameters as `Nat` constants and proves:
  * the solution-length formula evaluates to the documented `1344`,
  * the total wire size is `1347`,
  * the collision count is `1024`,
  * the verifier input length is `108`,
  * a handful of consequences (positivity, divisibility, monotonicity).
-/

namespace Zebra.EquihashParams

/-- Equihash parameter `n` (the bit length of each round's hash output).
Source: `zebra-chain/src/work/equihash.rs:76` (`let n = 200;`). -/
def N : Nat := 200

/-- Equihash parameter `k` (the number of collision rounds).
Source: `zebra-chain/src/work/equihash.rs:77` (`let k = 9;`). -/
def K : Nat := 9

/-- The hard-coded Mainnet/Testnet solution length, in bytes.
Source: `zebra-chain/src/work/equihash.rs:31`
(`pub(crate) const SOLUTION_SIZE: usize = 1344`). -/
def SOLUTION_SIZE : Nat := 1344

/-- The Regtest solution length, in bytes.
Source: `zebra-chain/src/work/equihash.rs:34`
(`pub(crate) const REGTEST_SOLUTION_SIZE: usize = 36`). -/
def REGTEST_SOLUTION_SIZE : Nat := 36

/-- The portion of the block header used as the verifier's input.
`4 + 32 * 3 + 4 * 2 = 108` bytes: version, 3 hashes (previous block,
merkle root, sapling root), and 2 32-bit fields (time, bits) — but **not**
the 32-byte nonce or the solution.
Source: `zebra-chain/src/work/equihash.rs:60`
(`pub const INPUT_LENGTH: usize = 4 + 32 * 3 + 4 * 2`). -/
def INPUT_LENGTH : Nat := 4 + 32 * 3 + 4 * 2

/-- The CompactSize wire-prefix length for a 1344-byte payload (band-2:
tag `0xfd` plus the two little-endian length bytes).
Source: see `EquihashSolution.lean` (the canonical prefix is
`[0xfd, 0x40, 0x05]`). -/
def PREFIX_BYTES : Nat := 3

/-- The total wire size of a Mainnet/Testnet Equihash solution: 3-byte
CompactSize prefix + 1344-byte payload. -/
def WIRE_SIZE : Nat := PREFIX_BYTES + SOLUTION_SIZE

/-- The Equihash solution-length formula:

  `solutionLengthBytes(n, k) = 2^k * (n / (k+1) + 1) / 8`

This is the bit-packed length of `2^k` indices, each `n/(k+1) + 1` bits
wide, packed into bytes. For `(n, k) = (200, 9)` the formula evaluates to
`1344`, matching the hard-coded `SOLUTION_SIZE`. -/
def solutionLengthBytes (n k : Nat) : Nat :=
  2^k * (n / (k + 1) + 1) / 8

/-- The Equihash birthday-collision count: `2^(k+1)`. For Zcash's `k = 9`
this is `1024`, the number of leaves at the bottom of the collision tree. -/
def collisionCount (k : Nat) : Nat := 2 ^ (k + 1)

/-! ## Theorems -/

/-- **T1 (concrete `N` and `K`).** The Equihash parameters are `n = 200`
and `k = 9`, matching the literal constants in the Rust source's `check`
function. -/
theorem N_eq : N = 200 := rfl

theorem K_eq : K = 9 := rfl

/-- **T2 (collision-count concrete).** For `k = 9`, the collision count
is `2^10 = 1024`. -/
theorem collisionCount_K : collisionCount K = 1024 := by
  unfold collisionCount K; decide

/-- **T3 (collision count is `2 * 2^k`).** A useful algebraic identity:
the collision count equals twice the number of solution indices. -/
theorem collisionCount_eq_two_mul (k : Nat) :
    collisionCount k = 2 * 2 ^ k := by
  unfold collisionCount
  rw [pow_succ]; ring

/-- **T4 (solution-length formula evaluates to 1344).** The Rust constant
`SOLUTION_SIZE = 1344` is *exactly* `solutionLengthBytes(200, 9) =
2^9 * (200/10 + 1) / 8 = 512 * 21 / 8`. This is the wave-3 anti-magic-number
proof: `1344` is not arbitrary, it falls out of the `(n, k) = (200, 9)`
parameters. -/
theorem solutionLengthBytes_NK :
    solutionLengthBytes N K = SOLUTION_SIZE := by
  unfold solutionLengthBytes N K SOLUTION_SIZE; decide

/-- **T5 (intermediate factorisation).** The interior of the
solution-length formula at `(N, K)` equals `512 * 21 = 10752`, which then
divides by `8` to give `1344`. Records the documented arithmetic
"`512 * 21 / 8 = 1344`" in the task description. -/
theorem solutionLengthBytes_intermediate :
    2 ^ K * (N / (K + 1) + 1) = 10752 := by
  unfold N K; decide

theorem solution_intermediate_div :
    10752 / 8 = SOLUTION_SIZE := by
  unfold SOLUTION_SIZE; decide

/-- **T6 (wire-size concrete).** With the 3-byte CompactSize prefix
`[0xfd, 0x40, 0x05]`, the total wire size of a Mainnet/Testnet Equihash
solution is exactly `1347` bytes. -/
theorem wire_size : WIRE_SIZE = 1347 := by
  unfold WIRE_SIZE PREFIX_BYTES SOLUTION_SIZE; rfl

/-- **T7 (wire-size formula).** Equivalently, `WIRE_SIZE = 3 + 1344`. -/
theorem wire_size_decomposition : WIRE_SIZE = 3 + 1344 := by
  unfold WIRE_SIZE PREFIX_BYTES SOLUTION_SIZE; rfl

/-- **T8 (verifier input length).** The verifier's input is exactly
`108` bytes, decomposed as `4 + 32*3 + 4*2`. -/
theorem input_length_concrete : INPUT_LENGTH = 108 := by
  unfold INPUT_LENGTH; rfl

/-- **T9 (verifier input excludes nonce + solution).** The verifier
input excludes the 32-byte nonce and the 1344-byte solution; together
with these, the total header size is `108 + 32 + 1344 = 1484` bytes.
This pins the header-size invariant used in `Solution::check`. -/
theorem header_size :
    INPUT_LENGTH + 32 + SOLUTION_SIZE = 1484 := by
  unfold INPUT_LENGTH SOLUTION_SIZE; rfl

/-- **T10 (solution-size positivity).** The solution length is strictly
positive. (Trivial but rules out the degenerate "empty solution" parse
class — the deserialiser must always consume at least `SOLUTION_SIZE`
bytes after the length prefix.) -/
theorem solution_size_pos : 0 < SOLUTION_SIZE := by
  unfold SOLUTION_SIZE; decide

/-- **T11 (regtest solution-size positivity).** The Regtest solution
length is also strictly positive. -/
theorem regtest_solution_size_pos : 0 < REGTEST_SOLUTION_SIZE := by
  unfold REGTEST_SOLUTION_SIZE; decide

/-- **T12 (mainnet > regtest).** A Mainnet/Testnet solution is strictly
larger than a Regtest solution. The two never collide on length, which
is the property `Solution::from_bytes` relies on for variant
discrimination.
Source: `zebra-chain/src/work/equihash.rs:96-113`. -/
theorem solution_size_gt_regtest :
    REGTEST_SOLUTION_SIZE < SOLUTION_SIZE := by
  unfold SOLUTION_SIZE REGTEST_SOLUTION_SIZE; decide

/-- **T13 (solution size is divisible by 8).** `1344 = 168 * 8`. This is
*why* the bit-packed formula `2^k * (n/(k+1) + 1) / 8` produces an
integer: the numerator is divisible by 8. -/
theorem solution_size_div_8 :
    SOLUTION_SIZE % 8 = 0 := by
  unfold SOLUTION_SIZE; decide

/-- **T14 (numerator divisible by 8 at NK).** The pre-division numerator
of the solution-length formula at `(N, K)` is `10752`, which is
divisible by 8 — making the formula's `/ 8` a clean integer division. -/
theorem numerator_div_8 :
    (2 ^ K * (N / (K + 1) + 1)) % 8 = 0 := by
  unfold N K; decide

/-- **T15 (collision count is a power of 2).** `collisionCount k =
2^(k+1)` is a power of two by definition. We expose it as `Nat.pow 2`
for downstream `Nat.pow_succ` / `Nat.pow_le_pow_right` rewrites. -/
theorem collisionCount_pow (k : Nat) :
    collisionCount k = Nat.pow 2 (k + 1) := rfl

/-- **T16 (collision-count monotonicity in `k`).** Increasing `k` weakly
increases the collision count — the proof is a straightforward
`Nat.pow_le_pow_right` lift through `(· + 1)`. -/
theorem collisionCount_monotone {k₁ k₂ : Nat} (hle : k₁ ≤ k₂) :
    collisionCount k₁ ≤ collisionCount k₂ := by
  unfold collisionCount
  exact Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right hle 1)

/-- **T17 (wire-size strictly larger than payload).** The CompactSize
prefix is non-empty, so the wire size is strictly larger than the
solution payload. -/
theorem wire_size_gt_solution : SOLUTION_SIZE < WIRE_SIZE := by
  unfold WIRE_SIZE PREFIX_BYTES; omega

/-- **T18 (`n / (k+1)` at `(200, 9)`).** The bit-width per index minus 1
is `n / (k+1) = 200 / 10 = 20`, so each index is `21` bits wide. -/
theorem index_bit_width :
    N / (K + 1) = 20 := by
  unfold N K; decide

/-- **T19 (number of indices).** `2^K = 512` — the number of `(k+1)`-bit
indices packed into a solution. -/
theorem num_indices : 2 ^ K = 512 := by
  unfold K; decide

/-- **T20 (collision count and index count agree at `K`).** At `K = 9`,
the collision count (`2^(K+1) = 1024`) is exactly twice the number of
indices (`2^K = 512`). -/
theorem collisionCount_eq_double_indices :
    collisionCount K = 2 * 2 ^ K := collisionCount_eq_two_mul K

/-- **T21 (collision count is even).** A consequence of T3 — useful for
"two indices collide per round" downstream invariants. -/
theorem collisionCount_even (k : Nat) : collisionCount k % 2 = 0 := by
  rw [collisionCount_eq_two_mul]
  exact Nat.mul_mod_right 2 (2 ^ k)

end Zebra.EquihashParams
