import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Addr / Inv P2P message size caps

Zebra's P2P layer enforces hard upper bounds on the number of entries it accepts
in a single `addr` / `addrv2` message and in a single `inv` (received) message.
These caps are the first line of defence against memory-DoS via unbounded
preallocation when a peer sends an attacker-controlled list length.

The caps modelled here:

* `MAX_ADDR_MESSAGE_ENTRIES = 1000`
   — `zebra-network/src/constants.rs:301`, constant `MAX_ADDRS_IN_MESSAGE`
* `MAX_INV_IN_RECEIVED_MESSAGE = 50_000`
   — `zebra-network/src/protocol/external/inv.rs:190`. Same as zcashd's
   `MAX_INV_SZ` per the inline citation in that file.
* `MAX_TX_INV_IN_SENT_MESSAGE = 25_000`
   — `zebra-network/src/protocol/external/inv.rs:201`

The actual `inv` cap is not the static constant — Rust's
`impl TrustedPreallocate for InventoryHash::max_allocation` returns
`min(message_size_limit, MAX_INV_IN_RECEIVED_MESSAGE)`, where
`message_size_limit = (MAX_PROTOCOL_MESSAGE_LEN - 1) / MIN_INV_HASH_SIZE`.
We mirror that `min(..)` formula in `maxInvAllocation` below and use it as
the cap in `invTryFrom`.

We model each `try_from` cap function in the same style as
`Zebra.CompactSize.messageTryFrom`: it returns `some n` iff `n ≤ CAP`,
otherwise `none`.
-/

namespace Zebra.AddrMessageCap

/-! ## Constants -/

/-- Maximum number of address entries in an `addr` / `addrv2` message.
Source: `zebra-network/src/constants.rs:301` (`MAX_ADDRS_IN_MESSAGE`). -/
def MAX_ADDR_MESSAGE_ENTRIES : Nat := 1000

/-- Maximum protocol message body length in bytes.
Source: `zebra-chain/src/serialization/zcash_serialize.rs:11`
(`MAX_PROTOCOL_MESSAGE_LEN = 2 * 1024 * 1024`). Re-exported through
`zebra-network/src/protocol/external.rs:25`. -/
def MAX_PROTOCOL_MESSAGE_LEN : Nat := 2 * 1024 * 1024

/-- Minimum on-the-wire size of a single inventory hash.
Source: `zebra-network/src/protocol/external/inv.rs:180`
(`MIN_INV_HASH_SIZE = 36`). -/
def MIN_INV_HASH_SIZE : Nat := 36

/-- Static cap on inventory entries in a received `inv` message.
Source: `zebra-network/src/protocol/external/inv.rs:190`
(`MAX_INV_IN_RECEIVED_MESSAGE = 50_000`). The Rust docstring states this is
"same as `MAX_INV_SZ` in `zcashd`", so this constant is the canonical alias
for zcashd's cap; we do not model `MAX_INV_SZ` separately. -/
def MAX_INV_IN_RECEIVED_MESSAGE : Nat := 50000

/-- Maximum number of transaction inventory entries Zebra puts in a *sent*
`inv` message — kept `≤` zcashd's `MAX_INV_SZ` (= `MAX_INV_IN_RECEIVED_MESSAGE`).
Source: `zebra-network/src/protocol/external/inv.rs:201`
(`MAX_TX_INV_IN_SENT_MESSAGE = 25_000`). -/
def MAX_TX_INV_IN_SENT_MESSAGE : Nat := 25000

/-! ## Dynamic inv allocation cap

The Rust source enforces the *minimum* of the static
`MAX_INV_IN_RECEIVED_MESSAGE` and a derived per-message ceiling
`(MAX_PROTOCOL_MESSAGE_LEN - 1) / MIN_INV_HASH_SIZE`, reserving at least one
byte for the vector length prefix. This means the effective cap shrinks
automatically if `MAX_PROTOCOL_MESSAGE_LEN` is ever tightened, without having
to update `MAX_INV_IN_RECEIVED_MESSAGE`.

Source: `zebra-network/src/protocol/external/inv.rs:203-211`. -/

/-- Hash-count ceiling derived from the global protocol-message-length cap. -/
def messageSizeLimit : Nat := (MAX_PROTOCOL_MESSAGE_LEN - 1) / MIN_INV_HASH_SIZE

/-- Mirror of `<InventoryHash as TrustedPreallocate>::max_allocation()`:
`min(messageSizeLimit, MAX_INV_IN_RECEIVED_MESSAGE)`. -/
def maxInvAllocation : Nat := min messageSizeLimit MAX_INV_IN_RECEIVED_MESSAGE

/-! ## Cap functions

Each is a `try_from`-style guard: succeeds iff the count is within the cap. -/

/-- `addr` / `addrv2` entry-count cap. Mirrors the Rust check that rejects a
message claiming more than `MAX_ADDRS_IN_MESSAGE` entries before any
preallocation. -/
def addrTryFrom (n : Nat) : Option Nat :=
  if n ≤ MAX_ADDR_MESSAGE_ENTRIES then some n else none

/-- `inv` (received) entry-count cap. Uses the dynamic `maxInvAllocation`
formula, mirroring the Rust `TrustedPreallocate::max_allocation` impl. -/
def invTryFrom (n : Nat) : Option Nat :=
  if n ≤ maxInvAllocation then some n else none

/-- `inv` (outbound transaction) entry-count cap. -/
def txInvSentTryFrom (n : Nat) : Option Nat :=
  if n ≤ MAX_TX_INV_IN_SENT_MESSAGE then some n else none

/-! ## Concrete value pins for the dynamic cap

The wire constants resolve to specific integers; pin them so any future change
to `MAX_PROTOCOL_MESSAGE_LEN`, `MIN_INV_HASH_SIZE`, or
`MAX_INV_IN_RECEIVED_MESSAGE` breaks the build instead of silently shifting
the cap. -/

/-- `messageSizeLimit = (2 * 1024 * 1024 - 1) / 36 = 58_254`. -/
theorem messageSizeLimit_value : messageSizeLimit = 58254 := by
  unfold messageSizeLimit MAX_PROTOCOL_MESSAGE_LEN MIN_INV_HASH_SIZE
  decide

/-- Under the *current* `MAX_PROTOCOL_MESSAGE_LEN`, the static cap is the
binding one: `maxInvAllocation = 50_000`. This pins the Rust `min(..)` choice
so a regression in either operand surfaces immediately. -/
theorem maxInvAllocation_value : maxInvAllocation = 50000 := by
  unfold maxInvAllocation MAX_INV_IN_RECEIVED_MESSAGE
  rw [messageSizeLimit_value]
  decide

/-- The static `MAX_INV_IN_RECEIVED_MESSAGE = 50_000` is the active upper
bound today because the size-derived ceiling sits above it. If
`MAX_PROTOCOL_MESSAGE_LEN` ever shrinks below `36 * 50_000 + 1`, the dynamic
ceiling will start winning and `invTryFrom` will reject smaller counts than
the static constant suggests. -/
theorem static_cap_is_binding :
    MAX_INV_IN_RECEIVED_MESSAGE ≤ messageSizeLimit := by
  rw [messageSizeLimit_value]
  unfold MAX_INV_IN_RECEIVED_MESSAGE
  decide

/-! ## Cap iff theorems -/

/-- `addrTryFrom` succeeds iff `n ≤ MAX_ADDR_MESSAGE_ENTRIES`. -/
theorem addrTryFrom_iff (n : Nat) :
    (addrTryFrom n).isSome ↔ n ≤ MAX_ADDR_MESSAGE_ENTRIES := by
  unfold addrTryFrom
  by_cases h : n ≤ MAX_ADDR_MESSAGE_ENTRIES <;> simp [h]

/-- `invTryFrom` succeeds iff `n ≤ maxInvAllocation`. -/
theorem invTryFrom_iff (n : Nat) :
    (invTryFrom n).isSome ↔ n ≤ maxInvAllocation := by
  unfold invTryFrom
  by_cases h : n ≤ maxInvAllocation <;> simp [h]

/-- `txInvSentTryFrom` succeeds iff `n ≤ MAX_TX_INV_IN_SENT_MESSAGE`. -/
theorem txInvSentTryFrom_iff (n : Nat) :
    (txInvSentTryFrom n).isSome ↔ n ≤ MAX_TX_INV_IN_SENT_MESSAGE := by
  unfold txInvSentTryFrom
  by_cases h : n ≤ MAX_TX_INV_IN_SENT_MESSAGE <;> simp [h]

/-! ## Rejection / acceptance characterisations -/

/-- Any oversize address count is rejected — the DoS-prevention pin. -/
theorem addrTryFrom_rejects_overlimit (n : Nat)
    (h : MAX_ADDR_MESSAGE_ENTRIES < n) : addrTryFrom n = none := by
  unfold addrTryFrom
  have : ¬ n ≤ MAX_ADDR_MESSAGE_ENTRIES := by omega
  simp [this]

/-- Any oversize inv count is rejected — covers both the static-cap and
size-derived-cap rejection paths via the `min` in `maxInvAllocation`. -/
theorem invTryFrom_rejects_overlimit (n : Nat)
    (h : maxInvAllocation < n) : invTryFrom n = none := by
  unfold invTryFrom
  have : ¬ n ≤ maxInvAllocation := by omega
  simp [this]

/-- Any oversize sent-tx-inv count is rejected. -/
theorem txInvSentTryFrom_rejects_overlimit (n : Nat)
    (h : MAX_TX_INV_IN_SENT_MESSAGE < n) : txInvSentTryFrom n = none := by
  unfold txInvSentTryFrom
  have : ¬ n ≤ MAX_TX_INV_IN_SENT_MESSAGE := by omega
  simp [this]

/-- Accepting input echoes it back unchanged. -/
theorem addrTryFrom_valid (n : Nat) (h : n ≤ MAX_ADDR_MESSAGE_ENTRIES) :
    addrTryFrom n = some n := by
  unfold addrTryFrom; simp [h]

/-- Accepting input echoes it back unchanged. -/
theorem invTryFrom_valid (n : Nat) (h : n ≤ maxInvAllocation) :
    invTryFrom n = some n := by
  unfold invTryFrom; simp [h]

/-! ## Cross-cap relationships -/

/-- The outbound transaction-inv cap is below the *static* received-inv cap.
Since `MAX_INV_IN_RECEIVED_MESSAGE` is defined in the Rust source to equal
zcashd's `MAX_INV_SZ`, this is the invariant the Rust comment at
`inv.rs:198-201` asserts: Zebra never sends more than zcashd accepts. -/
theorem tx_inv_sent_le_inv_received_static :
    MAX_TX_INV_IN_SENT_MESSAGE ≤ MAX_INV_IN_RECEIVED_MESSAGE := by
  unfold MAX_TX_INV_IN_SENT_MESSAGE MAX_INV_IN_RECEIVED_MESSAGE
  decide

/-- The outbound transaction-inv cap is also below the *dynamic*
`maxInvAllocation` that Zebra itself enforces on inbound traffic. This is
strictly stronger than `tx_inv_sent_le_inv_received_static` whenever
`messageSizeLimit < MAX_INV_IN_RECEIVED_MESSAGE`. -/
theorem tx_inv_sent_le_max_inv_allocation :
    MAX_TX_INV_IN_SENT_MESSAGE ≤ maxInvAllocation := by
  rw [maxInvAllocation_value]
  unfold MAX_TX_INV_IN_SENT_MESSAGE
  decide

/-- Any addr count that passes its cap also fits under the inv cap — useful
for code paths that funnel both kinds of bounded collections through a single
preallocation limit. -/
theorem addr_le_inv (n : Nat) (h : n ≤ MAX_ADDR_MESSAGE_ENTRIES) :
    n ≤ maxInvAllocation := by
  rw [maxInvAllocation_value]
  unfold MAX_ADDR_MESSAGE_ENTRIES at h
  omega

/-! ## Memory-DoS bounds

Each accepted message consumes at most `cap * per_entry_size` bytes. Pin the
worst-case preallocation footprint so any cap change is visible in the model. -/

/-- A received `inv` message can force Zebra to preallocate at most
`50_000 * 36 = 1_800_000` bytes for the inventory-hash buffer. -/
theorem inv_preallocation_bytes_bound :
    maxInvAllocation * MIN_INV_HASH_SIZE ≤ 1800000 := by
  rw [maxInvAllocation_value]
  unfold MIN_INV_HASH_SIZE
  decide

/-- The whole inv-hash preallocation fits well inside one protocol message
body. (`1_800_000 ≤ 2_097_152`.) -/
theorem inv_preallocation_fits_message :
    maxInvAllocation * MIN_INV_HASH_SIZE ≤ MAX_PROTOCOL_MESSAGE_LEN := by
  rw [maxInvAllocation_value]
  unfold MIN_INV_HASH_SIZE MAX_PROTOCOL_MESSAGE_LEN
  decide

end Zebra.AddrMessageCap
