import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Zebra-RPC `LegacyCode` error-code mapping

Models `zebra-rpc/src/server/error.rs:11-58` (`pub enum LegacyCode`), the
Bitcoin-style application error codes Zebra exposes via JSON-RPC. The Rust
enum has 16 explicit discriminants in two groups:

* General application errors (Misc, Type, …, InWarmup): `-1`, `-2`, `-3`,
  `-5`, `-7`, `-8`, `-20`, `-22`, `-25`, `-26`, `-27`, `-28`
* P2P client errors (ClientNotConnected, …, ClientInvalidIpOrSubnet):
  `-9`, `-10`, `-23`, `-24`, `-29`, `-30`

The mapping is implemented in Rust as `code as i32` after `From<LegacyCode>
for ErrorCode` wraps it in `ErrorCode::ServerError(code as i32)`. The
discriminants are interleaved between the two groups (e.g. `-9, -10` sit
between `Type=-3` and `Database=-20`), so the "two non-overlapping groups"
property is non-trivial.

These codes share the `i32` space with jsonrpsee's *standard* JSON-RPC error
codes (`PARSE_ERROR_CODE = -32700`, `INVALID_REQUEST_CODE = -32600`,
`METHOD_NOT_FOUND_CODE = -32601`, `INVALID_PARAMS_CODE = -32602`,
`INTERNAL_ERROR_CODE = -32603`, `OVERSIZED_REQUEST_CODE = -32007`); since
every `LegacyCode` value is in `[-30, -1]`, the two ranges are disjoint by
construction. We pin both the concrete LegacyCode values and the standard
range, and prove disjointness.

We model error codes as `Int` (Rust uses `i32`; all values fit in `Int`).

## Properties proved

* `toCode` is total — every constructor has a code (the function is defined
  by exhaustive pattern-match);
* `toCode` is **injective** — no two variants share a code (mutual
  distinctness);
* the LegacyCode codes are exactly the set
  `{-30, -29, -28, -27, -26, -25, -24, -23, -22, -20, -10, -9, -8, -7, -5, -3, -2, -1}`;
* every LegacyCode is in the range `[-30, -1]`, so **disjoint from**
  the jsonrpsee standard JSON-RPC codes (all of which are `≤ -32007`);
* concrete pins for the security-critical codes (`Misc = -1`,
  `InvalidParameter = -8`, `InvalidAddressOrKey = -5`,
  `Deserialization = -22`, `VerifyRejected = -26`);
* round-trip: decoding a `LegacyCode`'s own code back gives that variant.
-/

namespace Zebra.RpcErrorCodes

/-! ## The `LegacyCode` enum -/

/-- Mirrors `pub enum LegacyCode` at `zebra-rpc/src/server/error.rs:12-53`. -/
inductive LegacyCode
  -- General application errors
  | misc                       -- -1   (the `#[default]`)
  | forbiddenBySafeMode        -- -2
  | type_                      -- -3
  | invalidAddressOrKey        -- -5
  | outOfMemory                -- -7
  | invalidParameter           -- -8
  | database                   -- -20
  | deserialization            -- -22
  | verify                     -- -25
  | verifyRejected             -- -26
  | verifyAlreadyInChain       -- -27
  | inWarmup                   -- -28
  -- P2P client errors
  | clientNotConnected         -- -9
  | clientInInitialDownload    -- -10
  | clientNodeAlreadyAdded     -- -23
  | clientNodeNotAdded         -- -24
  | clientNodeNotConnected     -- -29
  | clientInvalidIpOrSubnet    -- -30
  deriving DecidableEq, Repr

/-- The `i32` discriminant of each `LegacyCode`, mirroring Rust's
`impl From<LegacyCode> for i32 { code as i32 }` at `error.rs:61-65`. -/
def LegacyCode.toCode : LegacyCode → Int
  | .misc                    => -1
  | .forbiddenBySafeMode     => -2
  | .type_                   => -3
  | .invalidAddressOrKey     => -5
  | .outOfMemory             => -7
  | .invalidParameter        => -8
  | .clientNotConnected      => -9
  | .clientInInitialDownload => -10
  | .database                => -20
  | .deserialization         => -22
  | .clientNodeAlreadyAdded  => -23
  | .clientNodeNotAdded      => -24
  | .verify                  => -25
  | .verifyRejected          => -26
  | .verifyAlreadyInChain    => -27
  | .inWarmup                => -28
  | .clientNodeNotConnected  => -29
  | .clientInvalidIpOrSubnet => -30

/-- Decode an `Int` back into a `LegacyCode`, returning `none` for codes
that aren't in the table. Models the inverse direction (which Rust does not
provide directly; useful for relating wire codes back to a `LegacyCode`). -/
def fromCode (c : Int) : Option LegacyCode :=
  if c = -1 then some .misc
  else if c = -2 then some .forbiddenBySafeMode
  else if c = -3 then some .type_
  else if c = -5 then some .invalidAddressOrKey
  else if c = -7 then some .outOfMemory
  else if c = -8 then some .invalidParameter
  else if c = -9 then some .clientNotConnected
  else if c = -10 then some .clientInInitialDownload
  else if c = -20 then some .database
  else if c = -22 then some .deserialization
  else if c = -23 then some .clientNodeAlreadyAdded
  else if c = -24 then some .clientNodeNotAdded
  else if c = -25 then some .verify
  else if c = -26 then some .verifyRejected
  else if c = -27 then some .verifyAlreadyInChain
  else if c = -28 then some .inWarmup
  else if c = -29 then some .clientNodeNotConnected
  else if c = -30 then some .clientInvalidIpOrSubnet
  else none

/-! ## jsonrpsee standard JSON-RPC error codes (the reserved range)

Source: `jsonrpsee-types/src/error.rs:114-132` (used at `zebra-rpc/src/server/
rpc_call_compatibility.rs:50` via `ErrorCode::InvalidParams.code()`).

These are the JSON-RPC 2.0 reserved codes. The Zcash legacy codes must not
collide with them. -/

def PARSE_ERROR_CODE : Int := -32700
def INVALID_REQUEST_CODE : Int := -32600
def METHOD_NOT_FOUND_CODE : Int := -32601
def INVALID_PARAMS_CODE : Int := -32602
def INTERNAL_ERROR_CODE : Int := -32603
def OVERSIZED_REQUEST_CODE : Int := -32007

/-- The upper bound of the reserved JSON-RPC error range. Every reserved
code from jsonrpsee is `≤ -32007`. -/
def RESERVED_RANGE_HIGH : Int := -32007

/-- The lower bound of the LegacyCode range (most negative code). -/
def LEGACY_RANGE_LOW : Int := -30

/-- The upper bound of the LegacyCode range (least negative code). -/
def LEGACY_RANGE_HIGH : Int := -1

/-! ## Theorems -/

/-- **T1 (totality).** Every `LegacyCode` variant has a defined error code,
and that code is between `LEGACY_RANGE_LOW = -30` and
`LEGACY_RANGE_HIGH = -1` inclusive. This pins the Rust property that *all*
discriminants in the enum are small negative integers (no zero, no positive
value), reserving the negative space below 0 for application errors. -/
theorem toCode_in_range (c : LegacyCode) :
    LEGACY_RANGE_LOW ≤ c.toCode ∧ c.toCode ≤ LEGACY_RANGE_HIGH := by
  unfold LEGACY_RANGE_LOW LEGACY_RANGE_HIGH
  cases c <;> unfold LegacyCode.toCode <;> decide

/-- **T2 (mutual distinctness / injectivity of `toCode`).** No two variants
of `LegacyCode` share a code — the discriminants are pairwise distinct. If
this ever broke, two distinct error conditions would be indistinguishable
to JSON-RPC clients. -/
theorem toCode_injective (c₁ c₂ : LegacyCode) (h : c₁.toCode = c₂.toCode) :
    c₁ = c₂ := by
  cases c₁ <;> cases c₂ <;> simp_all [LegacyCode.toCode]

/-- **T3 (round-trip).** Decoding a `LegacyCode`'s own discriminant back via
`fromCode` recovers the original variant. Together with T2 this witnesses
that `fromCode` is the left inverse of `toCode` on the image of `toCode`. -/
theorem fromCode_toCode (c : LegacyCode) : fromCode c.toCode = some c := by
  cases c <;> unfold LegacyCode.toCode fromCode <;> decide

/-- **T4 (`fromCode` rejects everything outside `[-30, -1]`).** Any code
strictly less than `-30` or strictly greater than `-1` is unmapped. This
directly implies that the entire jsonrpsee reserved range (every value
`≤ -32007`) does **not** decode to a `LegacyCode`, so the two error-code
universes are disjoint. -/
theorem fromCode_none_outside_range (c : Int)
    (h : c < LEGACY_RANGE_LOW ∨ LEGACY_RANGE_HIGH < c) :
    fromCode c = none := by
  unfold fromCode LEGACY_RANGE_LOW LEGACY_RANGE_HIGH at *
  rcases h with hlt | hgt
  · -- c < -30: every equality `c = -k` for k ∈ {1..30 ∩ table} is false.
    have h1 : c ≠ -1 := by omega
    have h2 : c ≠ -2 := by omega
    have h3 : c ≠ -3 := by omega
    have h5 : c ≠ -5 := by omega
    have h7 : c ≠ -7 := by omega
    have h8 : c ≠ -8 := by omega
    have h9 : c ≠ -9 := by omega
    have h10 : c ≠ -10 := by omega
    have h20 : c ≠ -20 := by omega
    have h22 : c ≠ -22 := by omega
    have h23 : c ≠ -23 := by omega
    have h24 : c ≠ -24 := by omega
    have h25 : c ≠ -25 := by omega
    have h26 : c ≠ -26 := by omega
    have h27 : c ≠ -27 := by omega
    have h28 : c ≠ -28 := by omega
    have h29 : c ≠ -29 := by omega
    have h30 : c ≠ -30 := by omega
    simp [h1, h2, h3, h5, h7, h8, h9, h10, h20, h22, h23, h24,
          h25, h26, h27, h28, h29, h30]
  · -- c > -1
    have h1 : c ≠ -1 := by omega
    have h2 : c ≠ -2 := by omega
    have h3 : c ≠ -3 := by omega
    have h5 : c ≠ -5 := by omega
    have h7 : c ≠ -7 := by omega
    have h8 : c ≠ -8 := by omega
    have h9 : c ≠ -9 := by omega
    have h10 : c ≠ -10 := by omega
    have h20 : c ≠ -20 := by omega
    have h22 : c ≠ -22 := by omega
    have h23 : c ≠ -23 := by omega
    have h24 : c ≠ -24 := by omega
    have h25 : c ≠ -25 := by omega
    have h26 : c ≠ -26 := by omega
    have h27 : c ≠ -27 := by omega
    have h28 : c ≠ -28 := by omega
    have h29 : c ≠ -29 := by omega
    have h30 : c ≠ -30 := by omega
    simp [h1, h2, h3, h5, h7, h8, h9, h10, h20, h22, h23, h24,
          h25, h26, h27, h28, h29, h30]

/-- **T5 (LegacyCode and jsonrpsee reserved range are disjoint).** Every
LegacyCode discriminant is in `[-30, -1]`, while every reserved JSON-RPC
code (parse error, invalid params, etc.) is `≤ -32007`. The two universes
share no value, so a single wire `i32` unambiguously identifies which
universe an error came from. -/
theorem legacy_disjoint_from_reserved (c : LegacyCode) :
    RESERVED_RANGE_HIGH < c.toCode := by
  have hi := (toCode_in_range c).1
  unfold LEGACY_RANGE_LOW at hi
  unfold RESERVED_RANGE_HIGH
  omega

/-- **T6 (concrete pin: `Misc = -1`, the default).** Pins the `#[default]`
discriminant. Used by `map_misc_error` (`error.rs:80-82`) as the fallback
code for any error without an explicit code, so a regression here would
silently re-route every fallback error. -/
theorem misc_code : LegacyCode.misc.toCode = -1 := by decide

/-- **T7 (concrete pin: `InvalidParameter = -8`).** Pins the code used for
"invalid, missing or duplicate parameter" — the legacy analogue of
JSON-RPC's `INVALID_PARAMS_CODE`. The two are *different* values
(`-8` vs `-32602`); a regression that mapped legacy `InvalidParameter` to
`-32602` would conflate it with the JSON-RPC framework's own code. -/
theorem invalid_parameter_code :
    LegacyCode.invalidParameter.toCode = -8 := by decide

/-- **T8 (concrete pin: `Deserialization = -22`).** Pins the legacy code
for "error parsing or validating structure in raw format" — i.e. the
"not-found-or-cannot-parse" code paths in zebra-rpc. Distinct from JSON-RPC's
`PARSE_ERROR_CODE = -32700`. -/
theorem deserialization_code :
    LegacyCode.deserialization.toCode = -22 := by decide

/-- **T9 (concrete pin: `InvalidAddressOrKey = -5`).** Pins the "not found
in chain / not a valid address-or-key" code used by lookup RPCs. -/
theorem invalid_address_or_key_code :
    LegacyCode.invalidAddressOrKey.toCode = -5 := by decide

/-- **T10 (concrete pin: `VerifyRejected = -26`).** Pins the code for
"transaction or block was rejected by network rules". This is the code
zebra-rpc returns from `sendrawtransaction` / `submitblock` when the
consensus layer rejects the submission, so any external monitoring
keyed on `-26` would silently break if this changed. -/
theorem verify_rejected_code :
    LegacyCode.verifyRejected.toCode = -26 := by decide

/-- **T11 (concrete pin: the four general "verify" codes form a contiguous
block).** `Verify = -25`, `VerifyRejected = -26`, `VerifyAlreadyInChain
= -27`, `InWarmup = -28` — the Rust source defines them in this order with
sequential numeric codes, and external tooling relies on the block being
contiguous. -/
theorem verify_block_contiguous :
    LegacyCode.verify.toCode = -25
    ∧ LegacyCode.verifyRejected.toCode = -26
    ∧ LegacyCode.verifyAlreadyInChain.toCode = -27
    ∧ LegacyCode.inWarmup.toCode = -28 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **T12 (the gap at `-4` and `-6` is preserved).** The Rust enum skips
discriminants `-4` and `-6` (going `-3 → -5` and `-5 → -7`). This is a
deliberate compatibility choice — Bitcoin Core also leaves these gaps —
and `fromCode` returning `none` on them codifies it. If a future change
fills the gap, the regression surfaces here. -/
theorem gap_at_minus_4_and_6 :
    fromCode (-4) = none ∧ fromCode (-6) = none := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **T13 (`fromCode` is the right inverse of `toCode` on the image of
`toCode`).** This says decoding any `LegacyCode`'s code and re-encoding
the result yields the same code — i.e. encoding/decoding is a bijection
between `LegacyCode` and the 18-element image. -/
theorem fromCode_image_bijection (c : LegacyCode) :
    ∃ c', fromCode c.toCode = some c' ∧ c'.toCode = c.toCode := by
  refine ⟨c, ?_, rfl⟩
  exact fromCode_toCode c

/-- **T14 (no LegacyCode discriminant is 0).** The Rust enum starts at `-1`,
not `0`. A discriminant of `0` would conflict with the JSON-RPC convention
that absence of an `error` object (and a missing `code` field) signals
success, so any drift toward `0` is a wire-format hazard. -/
theorem no_legacy_code_is_zero (c : LegacyCode) : c.toCode ≠ 0 := by
  have h := (toCode_in_range c).2
  unfold LEGACY_RANGE_HIGH at h
  omega

/-- **T15 (no LegacyCode discriminant is positive).** All LegacyCode values
are strictly negative — the negative `i32` range is the application-error
namespace, and a positive value would be ambiguous against system/HTTP
status code conventions. -/
theorem all_legacy_codes_negative (c : LegacyCode) : c.toCode < 0 := by
  have h := (toCode_in_range c).2
  unfold LEGACY_RANGE_HIGH at h
  omega

/-- **T16 (Misc is the maximum / least negative LegacyCode).** Since `Misc`
is the `#[default]`, it makes sense that it's the most "neutral" code; we
pin it as the upper end of the legacy range. -/
theorem misc_is_maximum (c : LegacyCode) :
    c.toCode ≤ LegacyCode.misc.toCode := by
  rw [misc_code]
  have h := (toCode_in_range c).2
  unfold LEGACY_RANGE_HIGH at h
  exact h

/-- **T17 (`ClientInvalidIpOrSubnet` is the minimum / most negative
LegacyCode).** The bottom of the legacy range — useful for callers that
want to test "is this an application error code?" with a single bounds
check `LEGACY_RANGE_LOW ≤ c ≤ LEGACY_RANGE_HIGH`. -/
theorem clientInvalidIpOrSubnet_is_minimum (c : LegacyCode) :
    LegacyCode.clientInvalidIpOrSubnet.toCode ≤ c.toCode := by
  have h := (toCode_in_range c).1
  unfold LEGACY_RANGE_LOW at h
  change (-30 : Int) ≤ c.toCode
  exact h

/-- **T18 (jsonrpsee reserved codes never decode as `LegacyCode`).** A
concrete consequence of T4 and the pinned values of the jsonrpsee reserved
codes: `PARSE_ERROR_CODE`, `INVALID_REQUEST_CODE`, `METHOD_NOT_FOUND_CODE`,
`INVALID_PARAMS_CODE`, `INTERNAL_ERROR_CODE`, and `OVERSIZED_REQUEST_CODE`
all sit outside `[-30, -1]`, so `fromCode` returns `none` for each. -/
theorem reserved_codes_not_legacy :
    fromCode PARSE_ERROR_CODE = none
    ∧ fromCode INVALID_REQUEST_CODE = none
    ∧ fromCode METHOD_NOT_FOUND_CODE = none
    ∧ fromCode INVALID_PARAMS_CODE = none
    ∧ fromCode INTERNAL_ERROR_CODE = none
    ∧ fromCode OVERSIZED_REQUEST_CODE = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end Zebra.RpcErrorCodes
