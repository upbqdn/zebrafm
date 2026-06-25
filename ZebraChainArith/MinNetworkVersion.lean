import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Minimum network protocol version progression

Models the `INITIAL_MIN_NETWORK_PROTOCOL_VERSION` constant and the
`Version::min_specified_for_upgrade` function from
`zebra-network/src/protocol/external/types.rs:88` and
`zebra-network/src/constants.rs:411`.

For each `NetworkUpgrade`, the protocol returns a minimum `Version` (a `u32`,
modelled as `Nat`). The key correctness property is that the minimum version
is **monotone non-decreasing** as upgrades activate, on each network.

We model a simplified enum of upgrades and the Mainnet/Testnet mapping. The
Testnet and Regtest branches in the Rust use the same numbers (per the
`is_default_testnet() || params.is_regtest()` guards), so we collapse them
into a single `Testnet` case.
-/

namespace Zebra.MinNetworkVersion

/-- The ordered list of network upgrades from genesis through NU7. The order
matches activation order and is consensus-critical.
Source: `zebra-chain/src/parameters/network_upgrade.rs` (`NetworkUpgrade`
enum) and `zebra-network/src/protocol/external/types.rs:92`. -/
inductive NU
  | beforeOverwinter
  | overwinter
  | sapling
  | blossom
  | heartwood
  | canopy
  | nu5
  | nu6
  | nu6_1
  | nu6_2
  | nu7
  deriving DecidableEq, Repr

/-- Network kind. Mainnet and (default) Testnet/Regtest have distinct minimum
version numbers. We collapse Testnet and Regtest since the Rust code uses the
same value for both via the `is_default_testnet() || is_regtest()` guard.
Source: `zebra-network/src/protocol/external/types.rs:88`. -/
inductive Net
  | mainnet
  | testnet
  deriving DecidableEq, Repr

/-- `Version::min_specified_for_upgrade(network, network_upgrade)` for
mainnet.
Source: `zebra-network/src/protocol/external/types.rs:88-136`. -/
def minSpecifiedMainnet : NU → Nat
  | .beforeOverwinter => 170002
  | .overwinter       => 170005
  | .sapling          => 170007
  | .blossom          => 170009
  | .heartwood        => 170011
  | .canopy           => 170013
  | .nu5              => 170100
  | .nu6              => 170120
  | .nu6_1            => 170140
  | .nu6_2            => 170150
  | .nu7              => 170170

/-- `Version::min_specified_for_upgrade(network, network_upgrade)` for the
default testnet (and regtest, which uses the same values).
Source: `zebra-network/src/protocol/external/types.rs:88-136`. -/
def minSpecifiedTestnet : NU → Nat
  | .beforeOverwinter => 170002
  | .overwinter       => 170003
  | .sapling          => 170007
  | .blossom          => 170008
  | .heartwood        => 170010
  | .canopy           => 170012
  | .nu5              => 170050
  | .nu6              => 170110
  | .nu6_1            => 170130
  | .nu6_2            => 170150
  | .nu7              => 170160

/-- Unified accessor by `Net`. -/
def minSpecified (net : Net) (nu : NU) : Nat :=
  match net with
  | .mainnet => minSpecifiedMainnet nu
  | .testnet => minSpecifiedTestnet nu

/-- A linear index over `NU` giving activation order. Used to express
"upgrade `a` activates no later than upgrade `b`". -/
def order : NU → Nat
  | .beforeOverwinter => 0
  | .overwinter       => 1
  | .sapling          => 2
  | .blossom          => 3
  | .heartwood        => 4
  | .canopy           => 5
  | .nu5              => 6
  | .nu6              => 7
  | .nu6_1            => 8
  | .nu6_2            => 9
  | .nu7              => 10

/-- `INITIAL_MIN_NETWORK_PROTOCOL_VERSION` table value: the current initial
minimum for each network, pinned to NU6.2 (per the source as of writing).
Source: `zebra-network/src/constants.rs:411`. -/
def INITIAL_MIN_NETWORK_PROTOCOL_VERSION (net : Net) : Nat :=
  minSpecified net .nu6_2

/-! ## Theorems -/

/-- **T1 (monotonicity, mainnet).** Mainnet minimum protocol version is
monotone non-decreasing along activation order. -/
theorem minSpecifiedMainnet_monotone (a b : NU) (h : order a ≤ order b) :
    minSpecifiedMainnet a ≤ minSpecifiedMainnet b := by
  cases a <;> cases b <;> first | decide | (simp [order] at h)

/-- **T2 (monotonicity, testnet).** Testnet minimum protocol version is
monotone non-decreasing along activation order. -/
theorem minSpecifiedTestnet_monotone (a b : NU) (h : order a ≤ order b) :
    minSpecifiedTestnet a ≤ minSpecifiedTestnet b := by
  cases a <;> cases b <;> first | decide | (simp [order] at h)

/-- **T3 (monotonicity, any net).** The unified accessor is monotone
non-decreasing along activation order, on either network. -/
theorem minSpecified_monotone (net : Net) (a b : NU) (h : order a ≤ order b) :
    minSpecified net a ≤ minSpecified net b := by
  cases net
  · exact minSpecifiedMainnet_monotone a b h
  · exact minSpecifiedTestnet_monotone a b h

/-- **T4 (mainnet ≥ testnet from Overwinter on).** From Overwinter onward,
the mainnet minimum is at least the testnet minimum (the testnet activates
its consensus rules earlier, so the testnet floor is the same or lower). -/
theorem mainnet_ge_testnet (nu : NU) :
    minSpecifiedTestnet nu ≤ minSpecifiedMainnet nu := by
  cases nu <;> decide

/-- **T5 (all versions fit in `u32`).** Every minimum protocol version is a
valid `u32`. -/
theorem minSpecified_lt_u32 (net : Net) (nu : NU) :
    minSpecified net nu < 2 ^ 32 := by
  cases net <;> cases nu <;> decide

/-- **T6 (initial minimum is concretely 170150 on mainnet).** The
`INITIAL_MIN_NETWORK_PROTOCOL_VERSION` for Mainnet equals NU6.2's minimum,
which is `170_150`. -/
theorem initial_mainnet_value :
    INITIAL_MIN_NETWORK_PROTOCOL_VERSION .mainnet = 170150 := rfl

/-- **T7 (initial minimum is concretely 170150 on testnet).** The
`INITIAL_MIN_NETWORK_PROTOCOL_VERSION` for Testnet equals NU6.2's minimum,
which is `170_150` — Mainnet and Testnet happen to agree at NU6.2. -/
theorem initial_testnet_value :
    INITIAL_MIN_NETWORK_PROTOCOL_VERSION .testnet = 170150 := rfl

/-- **T8 (initial minimum is at least the BeforeOverwinter floor).** The
initial minimum on any network is no lower than the BeforeOverwinter floor
of `170_002`. This is a sanity check that the table is non-degenerate. -/
theorem initial_ge_genesis_floor (net : Net) :
    170002 ≤ INITIAL_MIN_NETWORK_PROTOCOL_VERSION net := by
  cases net <;> decide

/-- **T9 (strict progress at every mainnet upgrade between consecutive
NUs).** Each consecutive pair of upgrades on mainnet has strictly increasing
minimum protocol version. -/
theorem mainnet_strict_consecutive :
    minSpecifiedMainnet .beforeOverwinter < minSpecifiedMainnet .overwinter ∧
    minSpecifiedMainnet .overwinter < minSpecifiedMainnet .sapling ∧
    minSpecifiedMainnet .sapling     < minSpecifiedMainnet .blossom ∧
    minSpecifiedMainnet .blossom     < minSpecifiedMainnet .heartwood ∧
    minSpecifiedMainnet .heartwood   < minSpecifiedMainnet .canopy ∧
    minSpecifiedMainnet .canopy      < minSpecifiedMainnet .nu5 ∧
    minSpecifiedMainnet .nu5         < minSpecifiedMainnet .nu6 ∧
    minSpecifiedMainnet .nu6         < minSpecifiedMainnet .nu6_1 ∧
    minSpecifiedMainnet .nu6_1       < minSpecifiedMainnet .nu6_2 ∧
    minSpecifiedMainnet .nu6_2       < minSpecifiedMainnet .nu7 := by
  decide

end Zebra.MinNetworkVersion
