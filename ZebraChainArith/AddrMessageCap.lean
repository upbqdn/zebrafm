import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Addr / Inv P2P message size caps

Zebra's P2P layer enforces hard upper bounds on the number of entries it accepts
in a single `addr` / `addrv2` message and in a single `inv` (received) message.
These caps are the first line of defence against memory-DoS via unbounded
preallocation when a peer sends an attacker-controlled list length, mirroring
the `MAX_INV_SZ` constant from zcashd.

The caps modelled here:

* `MAX_ADDR_MESSAGE_ENTRIES = 1000`
   — `zebra-network/src/constants.rs:301`, constant `MAX_ADDRS_IN_MESSAGE`
* `MAX_INV_MESSAGE_ENTRIES = 50_000`
   — `zebra-network/src/protocol/external/inv.rs:190`,
     constant `MAX_INV_IN_RECEIVED_MESSAGE`
* `MAX_TX_INV_IN_SENT_MESSAGE = 25_000`
   — `zebra-network/src/protocol/external/inv.rs:201`

We model each `try_from` cap function in the same style as
`Zebra.CompactSize.messageTryFrom`: it returns `some n` iff `n ≤ CAP`,
otherwise `none`.
-/

namespace Zebra.AddrMessageCap

/-! ## Constants -/

/-- Maximum number of address entries in an `addr` / `addrv2` message.
Source: `zebra-network/src/constants.rs:301` (`MAX_ADDRS_IN_MESSAGE`) -/
def MAX_ADDR_MESSAGE_ENTRIES : Nat := 1000

/-- Maximum number of inventory entries in a *received* `inv` message.
Source: `zebra-network/src/protocol/external/inv.rs:190`
(`MAX_INV_IN_RECEIVED_MESSAGE`) -/
def MAX_INV_MESSAGE_ENTRIES : Nat := 50000

/-- Maximum number of transaction inventory entries Zebra puts in a *sent*
`inv` message — kept `≤` zcashd's `MAX_INV_SZ`.
Source: `zebra-network/src/protocol/external/inv.rs:201`
(`MAX_TX_INV_IN_SENT_MESSAGE`) -/
def MAX_TX_INV_IN_SENT_MESSAGE : Nat := 25000

/-! ## Cap functions

Each is a `try_from`-style guard: succeeds iff the count is within the cap. -/

/-- `addr` / `addrv2` entry-count cap. Mirrors the Rust check that rejects a
message claiming more than `MAX_ADDRS_IN_MESSAGE` entries before any
preallocation. -/
def addrTryFrom (n : Nat) : Option Nat :=
  if n ≤ MAX_ADDR_MESSAGE_ENTRIES then some n else none

/-- `inv` (received) entry-count cap. -/
def invTryFrom (n : Nat) : Option Nat :=
  if n ≤ MAX_INV_MESSAGE_ENTRIES then some n else none

/-- `inv` (outbound transaction) entry-count cap. -/
def txInvSentTryFrom (n : Nat) : Option Nat :=
  if n ≤ MAX_TX_INV_IN_SENT_MESSAGE then some n else none

/-! ## Theorems -/

/-- **T1 (addr cap iff).** `addrTryFrom` succeeds iff `n ≤ MAX_ADDR_MESSAGE_ENTRIES`. -/
theorem addrTryFrom_iff (n : Nat) :
    (addrTryFrom n).isSome ↔ n ≤ MAX_ADDR_MESSAGE_ENTRIES := by
  unfold addrTryFrom
  by_cases h : n ≤ MAX_ADDR_MESSAGE_ENTRIES <;> simp [h]

/-- **T2 (inv cap iff).** `invTryFrom` succeeds iff `n ≤ MAX_INV_MESSAGE_ENTRIES`. -/
theorem invTryFrom_iff (n : Nat) :
    (invTryFrom n).isSome ↔ n ≤ MAX_INV_MESSAGE_ENTRIES := by
  unfold invTryFrom
  by_cases h : n ≤ MAX_INV_MESSAGE_ENTRIES <;> simp [h]

/-- **T3 (tx-inv sent cap iff).** `txInvSentTryFrom` succeeds iff
`n ≤ MAX_TX_INV_IN_SENT_MESSAGE`. -/
theorem txInvSentTryFrom_iff (n : Nat) :
    (txInvSentTryFrom n).isSome ↔ n ≤ MAX_TX_INV_IN_SENT_MESSAGE := by
  unfold txInvSentTryFrom
  by_cases h : n ≤ MAX_TX_INV_IN_SENT_MESSAGE <;> simp [h]

/-- **T4 (addr cap rejects overlimit).** Any oversize address count is
rejected — this is the DoS-prevention pin. -/
theorem addrTryFrom_rejects_overlimit (n : Nat)
    (h : MAX_ADDR_MESSAGE_ENTRIES < n) : addrTryFrom n = none := by
  unfold addrTryFrom
  have : ¬ n ≤ MAX_ADDR_MESSAGE_ENTRIES := by omega
  simp [this]

/-- **T5 (inv cap rejects overlimit).** Any oversize inv count is rejected. -/
theorem invTryFrom_rejects_overlimit (n : Nat)
    (h : MAX_INV_MESSAGE_ENTRIES < n) : invTryFrom n = none := by
  unfold invTryFrom
  have : ¬ n ≤ MAX_INV_MESSAGE_ENTRIES := by omega
  simp [this]

/-- **T6 (tx-inv sent cap rejects overlimit).** -/
theorem txInvSentTryFrom_rejects_overlimit (n : Nat)
    (h : MAX_TX_INV_IN_SENT_MESSAGE < n) : txInvSentTryFrom n = none := by
  unfold txInvSentTryFrom
  have : ¬ n ≤ MAX_TX_INV_IN_SENT_MESSAGE := by omega
  simp [this]

/-- **T7 (addr cap identity on valid input).** Accepting input echoes it back. -/
theorem addrTryFrom_valid (n : Nat) (h : n ≤ MAX_ADDR_MESSAGE_ENTRIES) :
    addrTryFrom n = some n := by
  unfold addrTryFrom; simp [h]

/-- **T8 (inv cap identity on valid input).** -/
theorem invTryFrom_valid (n : Nat) (h : n ≤ MAX_INV_MESSAGE_ENTRIES) :
    invTryFrom n = some n := by
  unfold invTryFrom; simp [h]

/-- **T9 (tx-inv sent ≤ inv received).** The outbound transaction-inv cap is
strictly smaller than the inbound inv cap, matching the Rust invariant that
Zebra never sends more than zcashd would accept. -/
theorem tx_inv_sent_le_inv_received :
    MAX_TX_INV_IN_SENT_MESSAGE ≤ MAX_INV_MESSAGE_ENTRIES := by
  unfold MAX_TX_INV_IN_SENT_MESSAGE MAX_INV_MESSAGE_ENTRIES
  decide

/-- **T10 (addr ≤ inv).** Any addr count that passes its cap also fits under
the inv cap — useful for code paths that funnel both kinds of bounded
collections through a single preallocation limit. -/
theorem addr_le_inv (n : Nat) (h : n ≤ MAX_ADDR_MESSAGE_ENTRIES) :
    n ≤ MAX_INV_MESSAGE_ENTRIES := by
  unfold MAX_ADDR_MESSAGE_ENTRIES MAX_INV_MESSAGE_ENTRIES at *
  omega

/-- **T11 (cap is a fixed point: addr).** Passing the cap value itself is
accepted: it's the boundary case, not rejected. -/
theorem addrTryFrom_at_cap :
    addrTryFrom MAX_ADDR_MESSAGE_ENTRIES = some MAX_ADDR_MESSAGE_ENTRIES := by
  unfold addrTryFrom; simp

/-- **T12 (cap is a fixed point: inv).** -/
theorem invTryFrom_at_cap :
    invTryFrom MAX_INV_MESSAGE_ENTRIES = some MAX_INV_MESSAGE_ENTRIES := by
  unfold invTryFrom; simp

/-- **T13 (cap+1 rejected: addr).** The first value past the cap is rejected. -/
theorem addrTryFrom_cap_plus_one :
    addrTryFrom (MAX_ADDR_MESSAGE_ENTRIES + 1) = none := by
  apply addrTryFrom_rejects_overlimit
  omega

/-- **T14 (cap+1 rejected: inv).** -/
theorem invTryFrom_cap_plus_one :
    invTryFrom (MAX_INV_MESSAGE_ENTRIES + 1) = none := by
  apply invTryFrom_rejects_overlimit
  omega

end Zebra.AddrMessageCap
