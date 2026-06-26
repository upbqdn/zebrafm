import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Peer handshake: network-magic gating and version negotiation

This module models the two gates a Zcash peer connection must pass at the
network protocol layer:

1. **Magic-byte gating.** Every frame's 4-byte header magic must match the
   magic of the local node's network, otherwise the codec returns a parse
   error and the connection is dropped (`zebra-network/src/protocol/external/
   codec.rs:410-412`). The three magics are:

   * Mainnet  `0x24 0xe9 0x27 0x64`
   * Testnet  `0xfa 0x1a 0xf9 0xbf`
   * Regtest  `0xaa 0xe8 0x3f 0x5f`

   Sources: `zebra-chain/src/parameters/constants.rs:37-41` (the constants
   in `magics`), and `zebra-network/src/protocol/external/codec.rs:392-412`
   (the frame parser comparing the read magic against `network.magic()`).

2. **Version negotiation.** During the version/verack handshake Zebra
   computes the *negotiated* protocol version as

   `negotiated = min(CURRENT_NETWORK_PROTOCOL_VERSION, remote.version)`,

   but only after first rejecting peers below an obsolete-version floor
   `min_version = min_remote_for_height(network, height)`. That floor is
   itself

   `min_remote_for_height(net, h) = max(min_specified_for_height(net, h),
                                        INITIAL_MIN_NETWORK_PROTOCOL_VERSION[net])`

   Sources:
   - `zebra-network/src/peer/handshake.rs:750-777` (obsolete-version
     rejection at the floor);
   - `zebra-network/src/peer/handshake.rs:780` (`negotiated = min(local,
     remote)`);
   - `zebra-network/src/protocol/external/types.rs:33-50`
     (`min_remote_for_height` floor as `max(min_spec, initial_min)`);
   - `zebra-network/src/constants.rs:344`
     (`CURRENT_NETWORK_PROTOCOL_VERSION = 170_150`).

   NOTE: the wave description says "negotiated = max(local, remote)" — that
   is the historical Bitcoin convention, *not* what Zebra implements. The
   upstream uses `min`, because peers must speak a version both sides
   understand. We model the actual code.

This module is independent of `Zebrafm.MinNetworkVersion`, which already
covers the `min_specified_for_upgrade` table and the
`INITIAL_MIN_NETWORK_PROTOCOL_VERSION` map. Here we focus on the *handshake
arithmetic*: commutativity of the negotiation function, the floor
relationship that controls obsolete-version rejection, and the magic-byte
discriminators.
-/

namespace Zebra.NetworkHandshakeVersion

/-! ## Magic bytes -/

/-- A 4-byte network magic. Mirrors `pub struct Magic(pub [u8; 4])` from
`zebra-chain/src/parameters/network/magic.rs:13`. -/
structure Magic where
  b0 : Nat
  b1 : Nat
  b2 : Nat
  b3 : Nat
  deriving DecidableEq, Repr

/-- Mainnet magic. Source: `zebra-chain/src/parameters/constants.rs:37`,
`magics::MAINNET = Magic([0x24, 0xe9, 0x27, 0x64])`. -/
def MAINNET_MAGIC : Magic := ⟨0x24, 0xe9, 0x27, 0x64⟩

/-- Default-testnet magic. Source: `zebra-chain/src/parameters/constants.rs:39`,
`magics::TESTNET = Magic([0xfa, 0x1a, 0xf9, 0xbf])`. -/
def TESTNET_MAGIC : Magic := ⟨0xfa, 0x1a, 0xf9, 0xbf⟩

/-- Regtest magic. Source: `zebra-chain/src/parameters/constants.rs:41`,
`magics::REGTEST = Magic([0xaa, 0xe8, 0x3f, 0x5f])`. -/
def REGTEST_MAGIC : Magic := ⟨0xaa, 0xe8, 0x3f, 0x5f⟩

/-- Pack a magic's four bytes as a big-endian `u32`. The Rust debug format
prints the magic with `hex::encode`, which is big-endian byte order; the
`Magic(\"24e92764\")` debug strings in the unit test at
`zebra-chain/src/parameters/network/magic.rs:42-44` make this packing the
canonical numeric identity. -/
def Magic.toU32BE (m : Magic) : Nat :=
  m.b0 * 16777216 + m.b1 * 65536 + m.b2 * 256 + m.b3

/-- A magic is *valid as a byte sequence*: each byte is in `[0, 256)`. -/
def Magic.isByteArray (m : Magic) : Prop :=
  m.b0 < 256 ∧ m.b1 < 256 ∧ m.b2 < 256 ∧ m.b3 < 256

/-! ## Networks -/

/-- The three network kinds with distinct magics. Mirrors `enum
NetworkKind` insofar as it relates to magic dispatch
(`zebra-chain/src/parameters/network/magic.rs:21-29`). -/
inductive Net
  | mainnet
  | testnet
  | regtest
  deriving DecidableEq, Repr

/-- `Network::magic`. Source: `zebra-chain/src/parameters/network/magic.rs:23`. -/
def Net.magic : Net → Magic
  | .mainnet => MAINNET_MAGIC
  | .testnet => TESTNET_MAGIC
  | .regtest => REGTEST_MAGIC

/-! ## Codec frame-magic gate

The frame parser at `zebra-network/src/protocol/external/codec.rs:410-412`
reads four bytes into a `Magic` and compares against `self.builder.network.
magic()`. We model that comparison directly: a frame is accepted iff its
magic equals the local network's magic. -/

/-- `accept_frame_magic`: returns `true` iff the magic on the wire matches
the local network's magic. Mirrors the boolean of the `magic != … magic()`
check in `codec.rs:410`. -/
def acceptFrameMagic (localNet : Net) (m : Magic) : Bool :=
  decide (m = localNet.magic)

/-! ## Handshake version negotiation

We work over the underlying `u32` of `Version` (`zebra-network/src/protocol/
external/types.rs:18`, `pub struct Version(pub u32)`). All arithmetic is in
`Nat`; the bounds theorems below pin the `u32` constraint where it matters.

The negotiation function from `handshake.rs:780` is `min(local, remote)`.
The floor below which peers are rejected is `min_remote_for_height(net, h)`,
which is `max(min_spec, initial_min)` per `types.rs:49`. -/

/-- `Version::CURRENT_NETWORK_PROTOCOL_VERSION = 170_150`. Source:
`zebra-network/src/constants.rs:344`. -/
def CURRENT_NETWORK_PROTOCOL_VERSION : Nat := 170150

/-- The handshake's negotiated version: the minimum of Zebra's current
local version and the remote peer's advertised version. Source:
`zebra-network/src/peer/handshake.rs:780`. -/
def negotiate (localV remoteV : Nat) : Nat := min localV remoteV

/-- Concrete negotiation against `CURRENT_NETWORK_PROTOCOL_VERSION`. -/
def negotiateCurrent (remoteV : Nat) : Nat :=
  negotiate CURRENT_NETWORK_PROTOCOL_VERSION remoteV

/-- `min_remote_for_height` floor as `max(min_spec, initial_min)`. Source:
`zebra-network/src/protocol/external/types.rs:49`. -/
def minRemoteFloor (minSpec initialMin : Nat) : Nat := max minSpec initialMin

/-- Obsolete-version gate: `true` iff the peer's version is at or above the
floor. Source: `zebra-network/src/peer/handshake.rs:750`
(`if remote.version < min_version { return Err(ObsoleteVersion(..)) }`). -/
def acceptVersion (remoteV floor : Nat) : Bool := decide (floor ≤ remoteV)

/-! ## Theorems -/

/-! ### Magic-byte discriminators -/

/-- **T1 (the three magics are pairwise distinct).** No two networks share
a magic, so a single 4-byte header unambiguously identifies the chain.
This is the consensus-safety property that lets `codec.rs:410-412`
reject cross-network frames; if any two magics ever collided, a regtest
peer could feed mainnet a regtest message header and the parser would
proceed past the gate. -/
theorem magics_pairwise_distinct :
    MAINNET_MAGIC ≠ TESTNET_MAGIC ∧
    MAINNET_MAGIC ≠ REGTEST_MAGIC ∧
    TESTNET_MAGIC ≠ REGTEST_MAGIC := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **T2 (`Net.magic` is injective).** Networks with the same magic are
equal — equivalently, `magic` is a discriminator. Mirrors the practical
fact that `Network::magic` (`magic.rs:23-28`) returns distinct values on
distinct branches. -/
theorem net_magic_injective {a b : Net} (h : a.magic = b.magic) : a = b := by
  cases a <;> cases b <;> first | rfl | (exfalso; revert h; decide)

/-- **T3 (mainnet magic packs to `0x24e92764`).** Pinning the BE-packed
numeric identity that appears in the debug-format unit test at
`zebra-chain/src/parameters/network/magic.rs:42`
(`Magic(\"24e92764\")`). Any byte reordering or single-byte change would
break this value. -/
theorem mainnet_magic_u32 :
    MAINNET_MAGIC.toU32BE = 0x24e92764 := by
  unfold MAINNET_MAGIC Magic.toU32BE
  decide

/-- **T4 (testnet magic packs to `0xfa1af9bf`).** Pinning the BE-packed
numeric identity from `magic.rs:43`. -/
theorem testnet_magic_u32 :
    TESTNET_MAGIC.toU32BE = 0xfa1af9bf := by
  unfold TESTNET_MAGIC Magic.toU32BE
  decide

/-- **T5 (regtest magic packs to `0xaae83f5f`).** Pinning the BE-packed
numeric identity from `magic.rs:44`. -/
theorem regtest_magic_u32 :
    REGTEST_MAGIC.toU32BE = 0xaae83f5f := by
  unfold REGTEST_MAGIC Magic.toU32BE
  decide

/-- **T6 (every magic is a valid byte array).** Each component of each
magic is `< 256`, so `Magic` instantiations are well-formed `[u8; 4]`
values. This is the implicit invariant behind the Rust `[u8; 4]` type. -/
theorem all_magics_are_bytes :
    MAINNET_MAGIC.isByteArray ∧ TESTNET_MAGIC.isByteArray ∧
      REGTEST_MAGIC.isByteArray := by
  refine ⟨?_, ?_, ?_⟩
  · unfold Magic.isByteArray MAINNET_MAGIC; refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
  · unfold Magic.isByteArray TESTNET_MAGIC; refine ⟨?_, ?_, ?_, ?_⟩ <;> decide
  · unfold Magic.isByteArray REGTEST_MAGIC; refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **T7 (`u32` packing is bounded).** Each packed magic fits in a `u32`,
i.e. is strictly less than `2^32`. This is the implicit bound carried by
the `Magic.toU32BE` model. -/
theorem magics_fit_u32 :
    MAINNET_MAGIC.toU32BE < 2 ^ 32 ∧
    TESTNET_MAGIC.toU32BE < 2 ^ 32 ∧
    REGTEST_MAGIC.toU32BE < 2 ^ 32 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mainnet_magic_u32]; decide
  · rw [testnet_magic_u32]; decide
  · rw [regtest_magic_u32]; decide

/-! ### Frame-magic acceptance -/

/-- **T8 (a local node accepts its own magic).** The frame gate accepts
when the magic on the wire is the local network's magic. -/
theorem acceptFrameMagic_self (n : Net) :
    acceptFrameMagic n n.magic = true := by
  unfold acceptFrameMagic
  simp

/-- **T9 (a local node rejects every foreign magic).** For any pair of
*distinct* networks, the frame gate at one rejects the other's magic.
This is exactly the consensus-safety contract of `codec.rs:410-412`:
mainnet drops testnet frames, testnet drops regtest frames, etc. -/
theorem acceptFrameMagic_rejects_foreign {a b : Net} (hab : a ≠ b) :
    acceptFrameMagic a b.magic = false := by
  unfold acceptFrameMagic
  have hne : b.magic ≠ a.magic := fun h => hab (net_magic_injective h).symm
  simp [hne]

/-- **T10 (frame-magic acceptance is an exact discriminator).** The frame
gate's decision pins down which network the remote peer belongs to: if
the local node `a` accepts magic `m`, then `m = a.magic`, and hence the
"identifying network" of `m` is unique. -/
theorem acceptFrameMagic_iff (a : Net) (m : Magic) :
    acceptFrameMagic a m = true ↔ m = a.magic := by
  unfold acceptFrameMagic
  by_cases h : m = a.magic <;> simp [h]

/-! ### Version negotiation -/

/-- **T11 (negotiation is commutative).** The handshake produces the same
negotiated version regardless of which side is labelled "local" and which
"remote". This is the property a Zcash handshake needs in order to be
symmetric across the connection — both sides arrive at the same wire
protocol version. -/
theorem negotiate_comm (a b : Nat) : negotiate a b = negotiate b a := by
  unfold negotiate
  exact Nat.min_comm a b

/-- **T12 (negotiation is idempotent on agreement).** If both peers
advertise the same version, that's the negotiated version. -/
theorem negotiate_idem (v : Nat) : negotiate v v = v := by
  unfold negotiate
  exact Nat.min_self v

/-- **T13 (negotiation is associative).** Useful when more than two
participants must agree on the lowest common version. -/
theorem negotiate_assoc (a b c : Nat) :
    negotiate (negotiate a b) c = negotiate a (negotiate b c) := by
  unfold negotiate
  exact Nat.min_assoc a b c

/-- **T14 (negotiated ≤ both inputs).** The negotiated version is no
greater than either side's advertised version. So neither side ends up
speaking a protocol it didn't advertise. -/
theorem negotiate_le_both (localV remoteV : Nat) :
    negotiate localV remoteV ≤ localV ∧
    negotiate localV remoteV ≤ remoteV := by
  unfold negotiate
  exact ⟨Nat.min_le_left _ _, Nat.min_le_right _ _⟩

/-- **T15 (negotiation picks the lower side).** Exactly one of the two
arms of the negotiation `min` is taken: the negotiated version equals
either `localV` or `remoteV`. -/
theorem negotiate_eq_one_side (localV remoteV : Nat) :
    negotiate localV remoteV = localV ∨ negotiate localV remoteV = remoteV := by
  unfold negotiate
  by_cases h : localV ≤ remoteV
  · left; exact Nat.min_eq_left h
  · right
    exact Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_le h))

/-- **T16 (negotiateCurrent caps at the local version).** Against the
pinned `CURRENT_NETWORK_PROTOCOL_VERSION`, the negotiated version never
exceeds `170_150`. So the local node never gets pushed onto a wire
protocol newer than the code it's running. -/
theorem negotiateCurrent_le_current (remoteV : Nat) :
    negotiateCurrent remoteV ≤ CURRENT_NETWORK_PROTOCOL_VERSION := by
  unfold negotiateCurrent negotiate
  exact Nat.min_le_left _ _

/-- **T17 (negotiateCurrent is the remote when the remote is at most
current).** If the remote advertises a version `≤ 170_150`, the negotiated
version is the remote's. Equivalently: a remote running an older
protocol drags the connection down to that older protocol. -/
theorem negotiateCurrent_eq_remote
    (remoteV : Nat) (h : remoteV ≤ CURRENT_NETWORK_PROTOCOL_VERSION) :
    negotiateCurrent remoteV = remoteV := by
  unfold negotiateCurrent negotiate
  exact Nat.min_eq_right h

/-- **T18 (negotiateCurrent is current when the remote is at least
current).** If the remote advertises a version `≥ 170_150`, the
negotiated version stays at `CURRENT_NETWORK_PROTOCOL_VERSION` — Zebra
never advertises a version newer than its own. -/
theorem negotiateCurrent_eq_current
    (remoteV : Nat) (h : CURRENT_NETWORK_PROTOCOL_VERSION ≤ remoteV) :
    negotiateCurrent remoteV = CURRENT_NETWORK_PROTOCOL_VERSION := by
  unfold negotiateCurrent negotiate
  exact Nat.min_eq_left h

/-- **T19 (concrete current version fits in `u32`).** -/
theorem current_lt_u32 :
    CURRENT_NETWORK_PROTOCOL_VERSION < 2 ^ 32 := by
  unfold CURRENT_NETWORK_PROTOCOL_VERSION
  decide

/-! ### Obsolete-version floor -/

/-- **T20 (the floor dominates both inputs).** The obsolete-version floor
`max(min_spec, initial_min)` is at least each of the two protocol-version
bounds it merges. Source: `types.rs:49`. -/
theorem minRemoteFloor_dominates (ms im : Nat) :
    ms ≤ minRemoteFloor ms im ∧ im ≤ minRemoteFloor ms im := by
  unfold minRemoteFloor
  exact ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩

/-- **T21 (the floor is the lower of the two upper bounds: any version
above both bounds passes).** A peer at or above both `min_spec` and
`initial_min` is at or above their floor; converse holds too. -/
theorem above_floor_iff_above_both (remoteV ms im : Nat) :
    minRemoteFloor ms im ≤ remoteV ↔ ms ≤ remoteV ∧ im ≤ remoteV := by
  unfold minRemoteFloor
  constructor
  · intro h
    exact ⟨le_trans (Nat.le_max_left _ _) h, le_trans (Nat.le_max_right _ _) h⟩
  · intro ⟨h1, h2⟩
    exact Nat.max_le.mpr ⟨h1, h2⟩

/-- **T22 (`acceptVersion` matches the gate).** The accept-decision is
exactly the predicate `floor ≤ remoteV` — equivalently, *not* `remoteV <
floor`, which is the `if remote.version < min_version` test at
`handshake.rs:750`. -/
theorem acceptVersion_iff (remoteV floor : Nat) :
    acceptVersion remoteV floor = true ↔ floor ≤ remoteV := by
  unfold acceptVersion
  by_cases h : floor ≤ remoteV <;> simp [h]

/-- **T23 (any peer below the floor is rejected).** Strictly below the
floor ⇒ `acceptVersion = false`. This is the contrapositive of
`acceptVersion_iff` and corresponds to the early return at
`handshake.rs:750-777`. -/
theorem rejected_below_floor (remoteV floor : Nat) (h : remoteV < floor) :
    acceptVersion remoteV floor = false := by
  rw [Bool.eq_false_iff, Ne, acceptVersion_iff]
  omega

/-- **T24 (acceptance and negotiation chain).** If a peer is accepted at
floor `f` against `CURRENT_NETWORK_PROTOCOL_VERSION`, then the negotiated
version is at least `f`. So the negotiated version is itself at least the
obsolete-version floor — Zebra never silently negotiates a version below
the floor it just enforced.

Hypothesis: the floor is at most `CURRENT_NETWORK_PROTOCOL_VERSION` (true
in practice — the floor is bumped only after the local version table is,
and the `assert!` at `types.rs:41-47` forbids the opposite). -/
theorem negotiated_ge_floor_when_accepted
    (remoteV f : Nat)
    (hAcc : acceptVersion remoteV f = true)
    (hFloorLocal : f ≤ CURRENT_NETWORK_PROTOCOL_VERSION) :
    f ≤ negotiateCurrent remoteV := by
  have hRemote : f ≤ remoteV := (acceptVersion_iff remoteV f).mp hAcc
  unfold negotiateCurrent negotiate
  exact Nat.le_min.mpr ⟨hFloorLocal, hRemote⟩

/-- **T25 (rejection on floor change is monotone in the floor).** Raising
the floor can only reject more peers, never accept new ones. So the
NU-bump cycle (which only raises the floor) is monotone in obsolete-
peer rejection — there is no version `v` that was rejected at an old
floor and accepted at a strictly higher new floor. -/
theorem rejection_monotone_in_floor
    (remoteV f f' : Nat) (hff' : f ≤ f')
    (hRej : acceptVersion remoteV f = false) :
    acceptVersion remoteV f' = false := by
  rw [Bool.eq_false_iff, Ne, acceptVersion_iff] at hRej ⊢
  omega

/-- **T26 (acceptance is monotone in remote version).** Lowering the
floor or raising the remote version can only accept more peers. -/
theorem acceptance_monotone_in_remote
    (remoteV remoteV' f : Nat) (hv : remoteV ≤ remoteV')
    (hAcc : acceptVersion remoteV f = true) :
    acceptVersion remoteV' f = true := by
  rw [acceptVersion_iff] at hAcc ⊢
  omega

end Zebra.NetworkHandshakeVersion
