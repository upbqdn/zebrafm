import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Minimum network protocol version progression

Models the `INITIAL_MIN_NETWORK_PROTOCOL_VERSION` constant and the
`Version::min_specified_for_upgrade` function from
`zebra-network/src/protocol/external/types.rs:88-136` and
`zebra-network/src/constants.rs:411`.

For each `NetworkUpgrade`, the protocol returns a minimum `Version` (a `u32`,
modelled as `Nat`). The key correctness property is that the minimum version
is **monotone non-decreasing** as upgrades activate, on each network.

We model an enum of upgrades that includes the Rust `Genesis` and
`BeforeOverwinter` variants (which share the same minimum, 170_002, per
`external/types.rs:93`).

We model three networks: Mainnet, default Testnet, and Regtest. The Rust
code differentiates Testnet from Regtest at Sapling only (170_007 vs
170_006); for every other upgrade the default Testnet and Regtest values
agree via the `is_default_testnet() || is_regtest()` guards.
Source: `zebra-network/src/protocol/external/types.rs:96-98` (Sapling
differentiation), `:99-127` (collapsed Testnet/Regtest branches).
-/

namespace Zebra.MinNetworkVersion

/-- The ordered list of network upgrades from genesis through NU7. The order
matches activation order and is consensus-critical.

Note: Rust models `Genesis` and `BeforeOverwinter` as distinct variants of
`NetworkUpgrade` but assigns them the same minimum protocol version,
`170_002` (`external/types.rs:93`, the wildcard arm). We keep both variants
here so the enum is structurally faithful to Rust.

Source: `zebra-chain/src/parameters/network_upgrade.rs` (`NetworkUpgrade`
enum) and `zebra-network/src/protocol/external/types.rs:92-126`. -/
inductive NU
  | genesis
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

/-- Network kind. Mainnet, default Testnet, and Regtest are all modelled
distinctly because Rust differentiates Testnet from Regtest at Sapling
(170_007 vs 170_006); all other upgrades agree between default Testnet and
Regtest via the `is_default_testnet() || is_regtest()` guards.
Source: `zebra-network/src/protocol/external/types.rs:88-126`. -/
inductive Net
  | mainnet
  | testnet
  | regtest
  deriving DecidableEq, Repr

/-- `Version::min_specified_for_upgrade(Mainnet, network_upgrade)`.
Source: `zebra-network/src/protocol/external/types.rs:88-136`. -/
def minSpecifiedMainnet : NU → Nat
  | .genesis          => 170002
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

/-- `Version::min_specified_for_upgrade(Network::new_default_testnet(),
network_upgrade)`. At Sapling this is `170_007`, distinguishing the default
testnet from regtest.
Source: `zebra-network/src/protocol/external/types.rs:96`. -/
def minSpecifiedTestnet : NU → Nat
  | .genesis          => 170002
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

/-- `Version::min_specified_for_upgrade(Network::new_regtest(_),
network_upgrade)`. Differs from the default testnet at Sapling only:
regtest pins `170_006` while default testnet pins `170_007`.
Source: `zebra-network/src/protocol/external/types.rs:97`. -/
def minSpecifiedRegtest : NU → Nat
  | .genesis          => 170002
  | .beforeOverwinter => 170002
  | .overwinter       => 170003
  | .sapling          => 170006
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
  | .regtest => minSpecifiedRegtest nu

/-- A linear index over `NU` giving activation order. Used to express
"upgrade `a` activates no later than upgrade `b`". -/
def order : NU → Nat
  | .genesis          => 0
  | .beforeOverwinter => 1
  | .overwinter       => 2
  | .sapling          => 3
  | .blossom          => 4
  | .heartwood        => 5
  | .canopy           => 6
  | .nu5              => 7
  | .nu6              => 8
  | .nu6_1            => 9
  | .nu6_2            => 10
  | .nu7              => 11

/-- `INITIAL_MIN_NETWORK_PROTOCOL_VERSION` table value for each network kind,
pinned to NU6.2 per `zebra-network/src/constants.rs:414-416`.
Source: `zebra-network/src/constants.rs:411`. -/
def INITIAL_MIN_NETWORK_PROTOCOL_VERSION (net : Net) : Nat :=
  minSpecified net .nu6_2

/-! ## Theorems -/

/-- **T1 (monotonicity, mainnet).** Mainnet minimum protocol version is
monotone non-decreasing along activation order. -/
theorem minSpecifiedMainnet_monotone (a b : NU) (h : order a ≤ order b) :
    minSpecifiedMainnet a ≤ minSpecifiedMainnet b := by
  cases a <;> cases b <;> first | decide | (simp [order] at h)

/-- **T2 (monotonicity, default testnet).** Default testnet minimum
protocol version is monotone non-decreasing along activation order. -/
theorem minSpecifiedTestnet_monotone (a b : NU) (h : order a ≤ order b) :
    minSpecifiedTestnet a ≤ minSpecifiedTestnet b := by
  cases a <;> cases b <;> first | decide | (simp [order] at h)

/-- **T3 (monotonicity, regtest).** Regtest minimum protocol version is
monotone non-decreasing along activation order. -/
theorem minSpecifiedRegtest_monotone (a b : NU) (h : order a ≤ order b) :
    minSpecifiedRegtest a ≤ minSpecifiedRegtest b := by
  cases a <;> cases b <;> first | decide | (simp [order] at h)

/-- **T4 (monotonicity, any net).** The unified accessor is monotone
non-decreasing along activation order, on any of the three networks. -/
theorem minSpecified_monotone (net : Net) (a b : NU) (h : order a ≤ order b) :
    minSpecified net a ≤ minSpecified net b := by
  cases net
  · exact minSpecifiedMainnet_monotone a b h
  · exact minSpecifiedTestnet_monotone a b h
  · exact minSpecifiedRegtest_monotone a b h

/-- **T5 (mainnet ≥ default testnet at every upgrade).** Mainnet's
minimum is at least the default testnet's minimum (testnets advertise
earlier values during pre-deployment phases). -/
theorem mainnet_ge_testnet (nu : NU) :
    minSpecifiedTestnet nu ≤ minSpecifiedMainnet nu := by
  cases nu <;> decide

/-- **T6 (mainnet ≥ regtest at every upgrade).** Mainnet's minimum is at
least the regtest minimum. -/
theorem mainnet_ge_regtest (nu : NU) :
    minSpecifiedRegtest nu ≤ minSpecifiedMainnet nu := by
  cases nu <;> decide

/-- **T7 (all versions fit in `u32`).** Every minimum protocol version is a
valid `u32`. -/
theorem minSpecified_lt_u32 (net : Net) (nu : NU) :
    minSpecified net nu < 2 ^ 32 := by
  cases net <;> cases nu <;> decide

/-- **T8 (Genesis and BeforeOverwinter share the same minimum).** Per
`external/types.rs:93`'s wildcard arm, Genesis and BeforeOverwinter both
return `170_002` on every network. -/
theorem genesis_eq_beforeOverwinter (net : Net) :
    minSpecified net .genesis = minSpecified net .beforeOverwinter := by
  cases net <;> rfl

/-- **T9 (Genesis floor is 170_002 on every network).** -/
theorem genesis_value (net : Net) :
    minSpecified net .genesis = 170002 := by
  cases net <;> rfl

/-- **T10 (Testnet vs Regtest differ at Sapling only).** The default
testnet and regtest tables agree on every upgrade except Sapling, where
testnet is `170_007` and regtest is `170_006`. This matches Rust's
`external/types.rs:96-97` differentiated arms versus the collapsed
`is_default_testnet() || is_regtest()` arms below. -/
theorem testnet_eq_regtest_off_sapling (nu : NU) (h : nu ≠ NU.sapling) :
    minSpecifiedTestnet nu = minSpecifiedRegtest nu := by
  cases nu <;> first | rfl | exact (h rfl).elim

/-- **T11 (Sapling is the only Testnet/Regtest split).** At Sapling, the
default testnet exceeds regtest by exactly 1. -/
theorem testnet_sapling_minus_regtest_sapling :
    minSpecifiedTestnet .sapling = minSpecifiedRegtest .sapling + 1 := rfl

/-- **T12 (initial minimum is concretely 170150 on mainnet).** The
`INITIAL_MIN_NETWORK_PROTOCOL_VERSION` entry for Mainnet equals NU6.2's
minimum, `170_150`. Source: `zebra-network/src/constants.rs:414`. -/
theorem initial_mainnet_value :
    INITIAL_MIN_NETWORK_PROTOCOL_VERSION .mainnet = 170150 := rfl

/-- **T13 (initial minimum is concretely 170150 on default testnet).** The
`INITIAL_MIN_NETWORK_PROTOCOL_VERSION` entry for Testnet equals NU6.2's
minimum, `170_150`. Source: `zebra-network/src/constants.rs:415`. -/
theorem initial_testnet_value :
    INITIAL_MIN_NETWORK_PROTOCOL_VERSION .testnet = 170150 := rfl

/-- **T14 (initial minimum is concretely 170150 on regtest).** The
`INITIAL_MIN_NETWORK_PROTOCOL_VERSION` entry for Regtest equals NU6.2's
minimum, `170_150`. Source: `zebra-network/src/constants.rs:416`. -/
theorem initial_regtest_value :
    INITIAL_MIN_NETWORK_PROTOCOL_VERSION .regtest = 170150 := rfl

/-- **T15 (initial minimum agrees across all networks).** All three
`INITIAL_MIN_NETWORK_PROTOCOL_VERSION` entries agree at NU6.2 even though
the per-upgrade tables differ at lower upgrades. -/
theorem initial_value_agrees_across_networks :
    INITIAL_MIN_NETWORK_PROTOCOL_VERSION .mainnet =
      INITIAL_MIN_NETWORK_PROTOCOL_VERSION .testnet ∧
    INITIAL_MIN_NETWORK_PROTOCOL_VERSION .testnet =
      INITIAL_MIN_NETWORK_PROTOCOL_VERSION .regtest := by
  decide

/-- **T16 (strict progress at every mainnet upgrade between consecutive
NUs starting from Overwinter).** Each consecutive pair of upgrades on
mainnet from Overwinter onward has strictly increasing minimum protocol
version. (Genesis and BeforeOverwinter both pin `170_002`, so the
Genesis→BeforeOverwinter step is non-strict — see `T8`.) -/
theorem mainnet_strict_consecutive_from_overwinter :
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
