import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Equihash parameters from `zebra-chain/src/work/equihash.rs`

Zcash's Equihash proof-of-work is parameterised by `(n, k) = (200, 9)` on
Mainnet and Testnet, and by `(n, k) = (48, 5)` on Regtest. The hard-coded
constants in `zebra-chain/src/work/equihash.rs` follow directly from these
parameters:

  * The solution length (`SOLUTION_SIZE = 1344`) is the encoded length of
    `2^k` k-bit indices, each padded to `n/(k+1) + 1` bits, packed into
    bytes:

    `solutionLengthBytes(n, k) = 2^k * (n / (k+1) + 1) / 8`

    For `(n, k) = (200, 9)`: `2^9 * (200/10 + 1) / 8 = 512 * 21 / 8 = 1344`.
    For `(n, k) = (48, 5)`:  `2^5 * (48/6 + 1) / 8  = 32 * 9 / 8   = 36`.
    Source: `zebra-chain/src/work/equihash.rs:31`
    (`pub(crate) const SOLUTION_SIZE: usize = 1344`) and
    `zebra-chain/src/work/equihash.rs:34`
    (`pub(crate) const REGTEST_SOLUTION_SIZE: usize = 36`).

  * On the wire the solution is preceded by a `CompactSize` prefix.
    For the Mainnet/Testnet 1344-byte payload this is the 3-byte band-2
    encoding `[0xfd, 0x40, 0x05]`, so the total wire size is
    `3 + 1344 = 1347` bytes.
    Source: `zebra-chain/src/work/equihash.rs:257`
    (`impl ZcashSerialize for Solution`).

  * The verifier-input length (`Solution::INPUT_LENGTH`) is exactly
    `4 + 32 * 3 + 4 * 2 = 108` bytes — the part of the block header that
    is held constant during the solver run (version + 3 hashes
    [previous block, merkle root, `commitment_bytes`] + 2 32-bit
    timestamp/difficulty fields, excluding the 32-byte nonce and
    solution).
    Source: `zebra-chain/src/work/equihash.rs:60`
    (`pub const INPUT_LENGTH: usize = 4 + 32 * 3 + 4 * 2`),
    `zebra-chain/src/block/header.rs:43-77`.

This module models the parameters as `Nat` constants and proves:
  * the solution-length formula evaluates to `1344` at `(200, 9)` and
    `36` at `(48, 5)`,
  * the total Mainnet wire size is `1347`,
  * the number of indices in a solution is `2^k = 512` (Mainnet/Testnet),
  * the collision bit length (`n / (k+1)`) and per-index bit width
    (`n / (k+1) + 1`) at both parameter pairs,
  * the verifier input length is `108`,
  * a handful of consequences (positivity, divisibility, monotonicity,
    Mainnet ≠ Regtest length).

## What this module does *not* model

The original Equihash algorithm's collision tree has depth `k`, and
intermediate quantities such as the per-round collision width and the
total hash work are *not* mirrored as `Nat` constants here — they are
not represented as named constants in `zebra-chain/src/work/equihash.rs`
either. The Lean side stays scoped to the byte-level constants and
formulas that the Rust file actually exposes.
-/

namespace Zebra.EquihashParams

/-! ## Mainnet / Testnet parameters -/

/-- Equihash parameter `n` for Mainnet/Testnet.
Source: `zebra-chain/src/work/equihash.rs:76` (`let n = 200;`). -/
def N : Nat := 200

/-- Equihash parameter `k` for Mainnet/Testnet.
Source: `zebra-chain/src/work/equihash.rs:77` (`let k = 9;`). -/
def K : Nat := 9

/-- The hard-coded Mainnet/Testnet solution length, in bytes.
Source: `zebra-chain/src/work/equihash.rs:31`
(`pub(crate) const SOLUTION_SIZE: usize = 1344`). -/
def SOLUTION_SIZE : Nat := 1344

/-! ## Regtest parameters -/

/-- The hard-coded Regtest solution length, in bytes.
Source: `zebra-chain/src/work/equihash.rs:34`
(`pub(crate) const REGTEST_SOLUTION_SIZE: usize = 36`). -/
def REGTEST_SOLUTION_SIZE : Nat := 36

/-- Equihash parameter `n` for Regtest. Not a named constant in
`zebra-chain/src/work/equihash.rs`; the value `48` is the standard
zcashd Regtest setting and is the unique `n` (under the `equihash`
crate's parameter validity rules: `n % 8 = 0`, `k ≥ 3`, `k < n`,
`n % (k+1) = 0`) for which `solutionLengthBytes(n, 5) = 36`. -/
def REGTEST_N : Nat := 48

/-- Equihash parameter `k` for Regtest. Not a named constant in
`zebra-chain/src/work/equihash.rs`; see `REGTEST_N`. -/
def REGTEST_K : Nat := 5

/-! ## Verifier input + wire prefix -/

/-- The portion of the block header used as the verifier's input.
`4 + 32 * 3 + 4 * 2 = 108` bytes: version, 3 hashes (previous block,
merkle root, `commitment_bytes`), and 2 32-bit fields (time, bits) —
but **not** the 32-byte nonce or the solution.
Source: `zebra-chain/src/work/equihash.rs:60`
(`pub const INPUT_LENGTH: usize = 4 + 32 * 3 + 4 * 2`);
`zebra-chain/src/block/header.rs:43-77` for the field layout. -/
def INPUT_LENGTH : Nat := 4 + 32 * 3 + 4 * 2

/-- The CompactSize wire-prefix length for a 1344-byte payload (band-2:
tag `0xfd` plus the two little-endian length bytes).
Source: see `EquihashSolution.lean` (the canonical prefix is
`[0xfd, 0x40, 0x05]`). -/
def PREFIX_BYTES : Nat := 3

/-- The total wire size of a Mainnet/Testnet Equihash solution: 3-byte
CompactSize prefix + 1344-byte payload. -/
def WIRE_SIZE : Nat := PREFIX_BYTES + SOLUTION_SIZE

/-! ## Derived quantities -/

/-- The Equihash solution-length formula:

  `solutionLengthBytes(n, k) = 2^k * (n / (k+1) + 1) / 8`

This is the bit-packed length of `2^k` indices, each `n/(k+1) + 1` bits
wide, packed into bytes. For `(n, k) = (200, 9)` the formula evaluates to
`1344`, matching the hard-coded `SOLUTION_SIZE`; for `(n, k) = (48, 5)`
it evaluates to `36`, matching `REGTEST_SOLUTION_SIZE`. -/
def solutionLengthBytes (n k : Nat) : Nat :=
  2^k * (n / (k + 1) + 1) / 8

/-- The number of indices in an Equihash solution: `2^k`. This is the
literature's `2^k`, not the leaf count of a collision tree. -/
def numIndices (k : Nat) : Nat := 2 ^ k

/-- The Equihash collision bit length: `n / (k + 1)`. This matches the
`equihash` crate's `Params::collision_bit_length` function.
Source: `equihash-0.3.0/src/params.rs:27-29` (`fn collision_bit_length`). -/
def collisionBitLength (n k : Nat) : Nat := n / (k + 1)

/-- The bit width per packed index: `collisionBitLength n k + 1`,
i.e. the second factor in `solutionLengthBytes`. -/
def indexBitWidth (n k : Nat) : Nat := collisionBitLength n k + 1

/-! ## Theorems -/

/-! ### Mainnet/Testnet constants -/

/-- The Equihash parameters are `n = 200` and `k = 9` on Mainnet/Testnet,
matching the literal constants in the Rust source's `Solution::check`
function. -/
theorem N_eq : N = 200 := rfl

theorem K_eq : K = 9 := rfl

/-- The Rust constant `SOLUTION_SIZE = 1344` is *exactly*
`solutionLengthBytes(200, 9) = 2^9 * (200/10 + 1) / 8 = 512 * 21 / 8`.
This is the anti-magic-number proof: `1344` is not arbitrary, it falls
out of the `(n, k) = (200, 9)` parameters. -/
theorem solutionLengthBytes_NK :
    solutionLengthBytes N K = SOLUTION_SIZE := by
  unfold solutionLengthBytes N K SOLUTION_SIZE; decide

/-- The interior of the solution-length formula at `(N, K)` equals
`512 * 21 = 10752`, which then divides by `8` to give `1344`. Records
the documented arithmetic "`512 * 21 / 8 = 1344`". -/
theorem solutionLengthBytes_intermediate :
    2 ^ K * (N / (K + 1) + 1) = 10752 := by
  unfold N K; decide

theorem solution_intermediate_div :
    10752 / 8 = SOLUTION_SIZE := by
  unfold SOLUTION_SIZE; decide

/-! ### Regtest constants -/

/-- The Rust constant `REGTEST_SOLUTION_SIZE = 36` falls out of
`solutionLengthBytes(48, 5) = 2^5 * (48/6 + 1) / 8 = 32 * 9 / 8 = 36`. -/
theorem solutionLengthBytes_REGTEST :
    solutionLengthBytes REGTEST_N REGTEST_K = REGTEST_SOLUTION_SIZE := by
  unfold solutionLengthBytes REGTEST_N REGTEST_K REGTEST_SOLUTION_SIZE
  decide

/-- The Regtest intermediate arithmetic: `32 * 9 = 288`, then `288 / 8 = 36`. -/
theorem solutionLengthBytes_REGTEST_intermediate :
    2 ^ REGTEST_K * (REGTEST_N / (REGTEST_K + 1) + 1) = 288 := by
  unfold REGTEST_N REGTEST_K; decide

theorem regtest_intermediate_div :
    288 / 8 = REGTEST_SOLUTION_SIZE := by
  unfold REGTEST_SOLUTION_SIZE; decide

/-- The Regtest parameters satisfy the `equihash` crate's validity rules
(see `Params::new` in `equihash-0.3.0/src/params.rs`):
`n % 8 = 0`, `k ≥ 3`, `k < n`, `n % (k+1) = 0`. -/
theorem regtest_params_valid :
    REGTEST_N % 8 = 0 ∧ 3 ≤ REGTEST_K ∧ REGTEST_K < REGTEST_N ∧
      REGTEST_N % (REGTEST_K + 1) = 0 := by
  unfold REGTEST_N REGTEST_K; decide

/-- The Mainnet/Testnet parameters satisfy the same validity rules. -/
theorem main_params_valid :
    N % 8 = 0 ∧ 3 ≤ K ∧ K < N ∧ N % (K + 1) = 0 := by
  unfold N K; decide

/-! ### Wire size -/

/-- With the 3-byte CompactSize prefix `[0xfd, 0x40, 0x05]`, the total
wire size of a Mainnet/Testnet Equihash solution is exactly `1347` bytes. -/
theorem wire_size : WIRE_SIZE = 1347 := by
  unfold WIRE_SIZE PREFIX_BYTES SOLUTION_SIZE; rfl

/-- Equivalently, `WIRE_SIZE = 3 + 1344`. -/
theorem wire_size_decomposition : WIRE_SIZE = 3 + 1344 := by
  unfold WIRE_SIZE PREFIX_BYTES SOLUTION_SIZE; rfl

/-- The CompactSize prefix is non-empty, so the wire size is strictly
larger than the solution payload. -/
theorem wire_size_gt_solution : SOLUTION_SIZE < WIRE_SIZE := by
  unfold WIRE_SIZE PREFIX_BYTES; omega

/-! ### Verifier input -/

/-- The verifier's input is exactly `108` bytes, decomposed as
`4 + 32*3 + 4*2`. -/
theorem input_length_concrete : INPUT_LENGTH = 108 := by
  unfold INPUT_LENGTH; rfl

/-- The verifier input excludes the 32-byte nonce and the 1344-byte
solution; together with these, the total header size is
`108 + 32 + 1344 = 1484` bytes. This pins the header-size invariant used
in `Solution::check`. -/
theorem header_size :
    INPUT_LENGTH + 32 + SOLUTION_SIZE = 1484 := by
  unfold INPUT_LENGTH SOLUTION_SIZE; rfl

/-! ### Positivity, divisibility, and length discrimination -/

/-- The Mainnet/Testnet solution length is strictly positive — rules out
the degenerate empty solution parse class. -/
theorem solution_size_pos : 0 < SOLUTION_SIZE := by
  unfold SOLUTION_SIZE; decide

/-- The Regtest solution length is also strictly positive. -/
theorem regtest_solution_size_pos : 0 < REGTEST_SOLUTION_SIZE := by
  unfold REGTEST_SOLUTION_SIZE; decide

/-- A Mainnet/Testnet solution is strictly larger than a Regtest
solution. The two never collide on length, which is the property
`Solution::from_bytes` relies on for variant discrimination.
Source: `zebra-chain/src/work/equihash.rs:96-113`. -/
theorem solution_size_gt_regtest :
    REGTEST_SOLUTION_SIZE < SOLUTION_SIZE := by
  unfold SOLUTION_SIZE REGTEST_SOLUTION_SIZE; decide

/-- `1344 = 168 * 8`. This is *why* the bit-packed formula
`2^k * (n/(k+1) + 1) / 8` produces an integer at `(200, 9)`: the
numerator is divisible by 8. -/
theorem solution_size_div_8 : SOLUTION_SIZE % 8 = 0 := by
  unfold SOLUTION_SIZE; decide

/-- The pre-division numerator of the solution-length formula at `(N, K)`
is `10752`, which is divisible by 8 — making the formula's `/ 8` a
clean integer division. -/
theorem numerator_div_8 :
    (2 ^ K * (N / (K + 1) + 1)) % 8 = 0 := by
  unfold N K; decide

/-- The Regtest pre-division numerator `288` is also divisible by 8. -/
theorem regtest_numerator_div_8 :
    (2 ^ REGTEST_K * (REGTEST_N / (REGTEST_K + 1) + 1)) % 8 = 0 := by
  unfold REGTEST_N REGTEST_K; decide

/-! ### Real Equihash quantities at `(N, K) = (200, 9)` -/

/-- The number of indices in a Mainnet/Testnet solution is `2^K = 512`. -/
theorem numIndices_K : numIndices K = 512 := by
  unfold numIndices K; decide

/-- The collision bit length at `(N, K)` is `N / (K+1) = 200 / 10 = 20`.
This matches the `equihash` crate's `Params::collision_bit_length` at
`(200, 9)`. -/
theorem collisionBitLength_NK : collisionBitLength N K = 20 := by
  unfold collisionBitLength N K; decide

/-- The per-index bit width at `(N, K)` is `21`. -/
theorem indexBitWidth_NK : indexBitWidth N K = 21 := by
  unfold indexBitWidth collisionBitLength N K; decide

/-- The number of indices in a Regtest solution is `2^5 = 32`. -/
theorem numIndices_REGTEST : numIndices REGTEST_K = 32 := by
  unfold numIndices REGTEST_K; decide

/-- The Regtest collision bit length: `48 / 6 = 8`. -/
theorem collisionBitLength_REGTEST :
    collisionBitLength REGTEST_N REGTEST_K = 8 := by
  unfold collisionBitLength REGTEST_N REGTEST_K; decide

/-- The Regtest per-index bit width: `9`. -/
theorem indexBitWidth_REGTEST :
    indexBitWidth REGTEST_N REGTEST_K = 9 := by
  unfold indexBitWidth collisionBitLength REGTEST_N REGTEST_K; decide

/-! ### Index count: monotonicity and parity -/

/-- `numIndices` is monotone in `k`. -/
theorem numIndices_monotone {k₁ k₂ : Nat} (hle : k₁ ≤ k₂) :
    numIndices k₁ ≤ numIndices k₂ := by
  unfold numIndices
  exact Nat.pow_le_pow_right (by decide) hle

/-- For `k ≥ 1`, the number of indices is even (`2^k` is even when
`k ≥ 1`). -/
theorem numIndices_even {k : Nat} (hk : 1 ≤ k) : numIndices k % 2 = 0 := by
  unfold numIndices
  -- `2^k = 2^(k-1) * 2` for `k ≥ 1`, and `n * 2 % 2 = 0`.
  have hk' : k = (k - 1) + 1 := by omega
  rw [hk', pow_succ, Nat.mul_mod_left]

/-- The solution-length formula is *factored* as
`numIndices k * indexBitWidth n k / 8`, matching the natural reading of
`2^k * (n/(k+1) + 1) / 8`. -/
theorem solutionLengthBytes_factored (n k : Nat) :
    solutionLengthBytes n k = numIndices k * indexBitWidth n k / 8 := by
  unfold solutionLengthBytes numIndices indexBitWidth collisionBitLength
  rfl

end Zebra.EquihashParams
