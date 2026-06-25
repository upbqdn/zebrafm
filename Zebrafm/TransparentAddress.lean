import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Transparent address byte layout from `zebra-chain/src/transparent/address.rs`

A Zcash transparent address carries a 2-byte network/type prefix followed by a
20-byte hash payload. Three address kinds use this 22-byte layout:

  * P2PKH (Pay-to-Public-Key-Hash), encoded on the wire by `ZcashSerialize`
    in Base58Check form;
  * P2SH (Pay-to-Script-Hash), same Base58Check path;
  * Tex (ZIP-320 Transparent-Source-Only), which shares the 2+20-byte shape but
    travels on the wire via Bech32m HRP, *not* through `impl ZcashSerialize`.

The wire-byte arithmetic that `ZcashSerialize`/`ZcashDeserialize` performs is:

  * `zcash_serialize`: write the network/kind-specific 2-byte prefix, then the
    20-byte hash. This is invoked for *all three* address kinds (the Rust impl
    handles `Tex` here too, even though the user-facing display path uses
    Bech32m).
  * `zcash_deserialize`: read 2 prefix bytes + 20 hash bytes, then dispatch on
    the prefix to choose `NetworkKind` and address kind. It only recognises the
    four P2PKH/P2SH prefix-pairs (mainnet + testnet) — Tex prefix bytes are
    *not* recognised, which is the asymmetry that ZIP-320 forbids round-tripping
    Tex addresses through Base58Check.

Network kinds modelled:

  * `Mainnet`, `Testnet`, `Regtest`. `NetworkKind::b58_pubkey_address_prefix`
    and `b58_script_address_prefix` both fold `Testnet | Regtest → testnet
    prefix`, so on-the-wire Regtest is byte-equal to Testnet. The deserialiser
    only returns `Mainnet`/`Testnet`, so a Regtest address round-trips as a
    Testnet address (we prove this).

Prefix bytes (from `zcash_protocol::constants` plus
`NetworkKind::tex_address_prefix` in `zebra-chain/src/parameters/network.rs`):

  * Mainnet P2PKH:  `[0x1c, 0xb8]`
  * Mainnet P2SH:   `[0x1c, 0xbd]`
  * Mainnet Tex:    `[0x1c, 0xb8]`  -- **collides with mainnet P2PKH**
  * Testnet P2PKH:  `[0x1d, 0x25]`
  * Testnet P2SH:   `[0x1c, 0xba]`
  * Testnet Tex:    `[0x1d, 0x25]`  -- collides with testnet P2PKH

The Tex/P2PKH prefix collision (which we prove) is exactly why ZIP-320 forbids
TEX from sharing the Base58Check codepath, and why the `ZcashDeserialize` arms
only cover the P2PKH/P2SH prefixes — there is no way to recover the Tex
network/kind from the wire bytes alone.

The Base58Check string shell that wraps these 22 bytes in `impl fmt::Display`
and `impl FromStr` is out of scope: we model exactly the 22-byte payload
`ZcashSerialize`/`ZcashDeserialize` operates on, plus the Tex prefix collision
since it is consensus-visible through `tex_address_prefix`.
-/

namespace Zebra.TransparentAddress

/-! ## Constants -/

/-- The fixed transparent-address hash width, in bytes (the `[u8; 20]` in
`PayToScriptHash::script_hash`, `PayToPublicKeyHash::pub_key_hash`, and
`Tex::validating_key_hash`).
Source: `zebra-chain/src/transparent/address.rs:37,46,56`. -/
def HASH_BYTES : Nat := 20

/-- The fixed network/type prefix width in bytes.
Source: `zebra-chain/src/transparent/address.rs:207` and the `[u8; 2]`
return types of `NetworkKind::b58_pubkey_address_prefix`,
`b58_script_address_prefix`, and `tex_address_prefix`. -/
def PREFIX_BYTES : Nat := 2

/-- The total on-the-wire length of a serialised transparent address:
prefix + hash. -/
def WIRE_BYTES : Nat := PREFIX_BYTES + HASH_BYTES

/-! ## Network prefix bytes -/

/-- Mainnet Base58Check P2PKH prefix bytes.
Source: `librustzcash/components/zcash_protocol/src/constants/mainnet.rs:49`
(consumed via `NetworkKind::b58_pubkey_address_prefix`,
`zebra-chain/src/parameters/network.rs:78-85`). -/
def MAINNET_P2PKH_PREFIX : List Nat := [0x1c, 0xb8]

/-- Mainnet Base58Check P2SH prefix bytes.
Source: `librustzcash/components/zcash_protocol/src/constants/mainnet.rs:54`
(consumed via `NetworkKind::b58_script_address_prefix`,
`zebra-chain/src/parameters/network.rs:89-96`). -/
def MAINNET_P2SH_PREFIX : List Nat := [0x1c, 0xbd]

/-- Testnet Base58Check P2PKH prefix bytes. Regtest folds to this prefix in
`NetworkKind::b58_pubkey_address_prefix`.
Source: `librustzcash/components/zcash_protocol/src/constants/testnet.rs:49`. -/
def TESTNET_P2PKH_PREFIX : List Nat := [0x1d, 0x25]

/-- Testnet Base58Check P2SH prefix bytes. Regtest folds to this prefix in
`NetworkKind::b58_script_address_prefix`.
Source: `librustzcash/components/zcash_protocol/src/constants/testnet.rs:54`. -/
def TESTNET_P2SH_PREFIX : List Nat := [0x1c, 0xba]

/-- Mainnet ZIP-320 Tex prefix bytes — note this is the **same** byte sequence
as `MAINNET_P2PKH_PREFIX`, which is the entire point of finding
"Tex/P2PKH prefix collision".
Source: `zebra-chain/src/parameters/network.rs:110-116`. -/
def MAINNET_TEX_PREFIX : List Nat := [0x1c, 0xb8]

/-- Testnet ZIP-320 Tex prefix bytes — same byte sequence as
`TESTNET_P2PKH_PREFIX`. Regtest folds to this prefix too.
Source: `zebra-chain/src/parameters/network.rs:110-116`. -/
def TESTNET_TEX_PREFIX : List Nat := [0x1d, 0x25]

/-! ## Address model -/

/-- The three `NetworkKind` variants the Rust enum carries.
Source: `zebra-chain/src/parameters/network.rs:38-48`.

`Regtest` is *not* folded into `Testnet`: it is its own enum variant in the
Rust source. The address-prefix lookups simply return the same bytes for
`Testnet` and `Regtest` (see `prefixFor`), which is why on-the-wire round-trip
of a Regtest address yields a Testnet address — there is no Regtest discriminator
in the byte stream. -/
inductive Network
  | mainnet
  | testnet
  | regtest
  deriving DecidableEq, Repr

/-- The three transparent address variants whose byte layout we model.

`p2pkh` and `p2sh` are the two Base58Check kinds handled by
`ZcashSerialize`/`ZcashDeserialize`. `tex` (ZIP-320) is also written by
`ZcashSerialize` using `NetworkKind::tex_address_prefix`, but its prefix bytes
collide with `p2pkh`, so `ZcashDeserialize` cannot distinguish it from `p2pkh`
on the wire — Tex addresses ship over Bech32m in normal use.
Source: `zebra-chain/src/transparent/address.rs:31-58`. -/
inductive AddrKind
  | p2pkh
  | p2sh
  | tex
  deriving DecidableEq, Repr

/-- A transparent address, modelled as a (network, kind, 20-byte hash) tuple.
Matches the byte layout of the `Address::PayToPublicKeyHash`,
`Address::PayToScriptHash`, and `Address::Tex` variants.
Source: `zebra-chain/src/transparent/address.rs:31-58`. -/
structure Address where
  network : Network
  kind    : AddrKind
  hash    : List Nat
  deriving Repr

/-- The hash-payload length invariant: a 20-byte `[u8; 20]`. -/
def IsHash (bs : List Nat) : Prop := bs.length = HASH_BYTES

/-- A well-formed `Address` carries a 20-byte hash. -/
def IsAddress (a : Address) : Prop := IsHash a.hash

/-! ## Prefix lookup -/

/-- The 2-byte prefix dispatched by network + kind, matching
`NetworkKind::b58_pubkey_address_prefix`,
`NetworkKind::b58_script_address_prefix`, and
`NetworkKind::tex_address_prefix`. Regtest deliberately returns the same bytes
as Testnet across all three lookups (no Regtest discriminator on the wire).
Source: `zebra-chain/src/parameters/network.rs:78-116`. -/
def prefixFor : Network → AddrKind → List Nat
  | .mainnet, .p2pkh => MAINNET_P2PKH_PREFIX
  | .mainnet, .p2sh  => MAINNET_P2SH_PREFIX
  | .mainnet, .tex   => MAINNET_TEX_PREFIX
  | .testnet, .p2pkh => TESTNET_P2PKH_PREFIX
  | .testnet, .p2sh  => TESTNET_P2SH_PREFIX
  | .testnet, .tex   => TESTNET_TEX_PREFIX
  | .regtest, .p2pkh => TESTNET_P2PKH_PREFIX
  | .regtest, .p2sh  => TESTNET_P2SH_PREFIX
  | .regtest, .tex   => TESTNET_TEX_PREFIX

/-! ## Serialisation -/

/-- `Address::zcash_serialize` writes the 2-byte prefix, then the 20-byte
hash, for all three address kinds. We model the wire form as the concatenation
of those two byte lists.
Source: `zebra-chain/src/transparent/address.rs:175-203`. -/
def zcashSerialize (a : Address) : List Nat :=
  prefixFor a.network a.kind ++ a.hash

/-- `Address::zcash_deserialize` reads 2 prefix bytes + 20 hash bytes, then
dispatches on the prefix to recover the network and address kind. Returns
`none` if the input doesn't have exactly 22 bytes with a recognised prefix.

The deserialiser only knows the four P2PKH/P2SH prefixes — it cannot
distinguish a Tex address from a P2PKH address on the wire (their prefix bytes
are identical), and it cannot tell Regtest from Testnet (their prefix bytes
are identical). It therefore coerces any Tex-shaped or Regtest-shaped input to
its P2PKH/Testnet siblings, exactly as the Rust impl does.
Source: `zebra-chain/src/transparent/address.rs:205-241`. -/
def zcashDeserialize (bs : List Nat) : Option Address :=
  match bs with
  | p0 :: p1 :: rest =>
    if rest.length = HASH_BYTES then
      if p0 = 0x1c ∧ p1 = 0xb8 then
        some { network := .mainnet, kind := .p2pkh, hash := rest }
      else if p0 = 0x1c ∧ p1 = 0xbd then
        some { network := .mainnet, kind := .p2sh, hash := rest }
      else if p0 = 0x1d ∧ p1 = 0x25 then
        some { network := .testnet, kind := .p2pkh, hash := rest }
      else if p0 = 0x1c ∧ p1 = 0xba then
        some { network := .testnet, kind := .p2sh, hash := rest }
      else none
    else none
  | _ => none

/-! ## Theorems -/

/-- **T1.** All network/kind prefixes are exactly 2 bytes long. The on-the-wire
`[u8; 2]` shape pin, covering all three `AddrKind`s. -/
theorem prefixFor_length (n : Network) (k : AddrKind) :
    (prefixFor n k).length = PREFIX_BYTES := by
  cases n <;> cases k <;> rfl

/-- **T2.** `zcashSerialize` produces exactly 22 bytes (prefix + hash) for any
well-formed address. -/
theorem zcashSerialize_length (a : Address) (h : IsAddress a) :
    (zcashSerialize a).length = WIRE_BYTES := by
  unfold zcashSerialize WIRE_BYTES
  rw [List.length_append, prefixFor_length]
  unfold IsAddress IsHash at h
  rw [h]

/-- **T3.** Wire round-trip for P2PKH and P2SH addresses on Mainnet/Testnet
networks: serialising and deserialising yields exactly the original. The Tex
and Regtest cases do *not* round-trip; their behaviour is captured by
`zcashSerialize_deserialize_tex_collapses_to_p2pkh` and
`zcashSerialize_deserialize_regtest_collapses_to_testnet` below. -/
theorem zcashSerialize_deserialize_b58
    (n : Network) (k : AddrKind) (hash : List Nat)
    (hHash : IsHash hash)
    (hN : n = .mainnet ∨ n = .testnet) (hK : k = .p2pkh ∨ k = .p2sh) :
    zcashDeserialize (zcashSerialize { network := n, kind := k, hash := hash }) =
      some { network := n, kind := k, hash := hash } := by
  unfold zcashSerialize zcashDeserialize
  unfold IsHash at hHash
  rcases hN with rfl | rfl <;> rcases hK with rfl | rfl <;>
    (unfold prefixFor MAINNET_P2PKH_PREFIX MAINNET_P2SH_PREFIX
            TESTNET_P2PKH_PREFIX TESTNET_P2SH_PREFIX
     simp [hHash])

/-- **T4.** The mainnet P2PKH prefix differs from the testnet P2PKH prefix:
their first bytes are distinct. The "network distinguishability" property
across the P2PKH variant. -/
theorem mainnet_testnet_p2pkh_distinct :
    MAINNET_P2PKH_PREFIX ≠ TESTNET_P2PKH_PREFIX := by
  unfold MAINNET_P2PKH_PREFIX TESTNET_P2PKH_PREFIX
  decide

/-- **T5.** The mainnet P2SH prefix differs from the testnet P2SH prefix:
the second bytes distinguish them. -/
theorem mainnet_testnet_p2sh_distinct :
    MAINNET_P2SH_PREFIX ≠ TESTNET_P2SH_PREFIX := by
  unfold MAINNET_P2SH_PREFIX TESTNET_P2SH_PREFIX
  decide

/-- **T6.** The four *Base58Check* prefixes (P2PKH/P2SH on Mainnet/Testnet)
are pairwise distinct, which makes the four `ZcashDeserialize` arms mutually
exclusive. This does **not** include Tex; see `mainnet_tex_p2pkh_collide` and
`testnet_tex_p2pkh_collide` for the Tex prefix collisions that motivate
ZIP-320's separate Bech32m codepath. -/
theorem b58_prefixes_pairwise_distinct :
    MAINNET_P2PKH_PREFIX ≠ MAINNET_P2SH_PREFIX ∧
    MAINNET_P2PKH_PREFIX ≠ TESTNET_P2PKH_PREFIX ∧
    MAINNET_P2PKH_PREFIX ≠ TESTNET_P2SH_PREFIX ∧
    MAINNET_P2SH_PREFIX  ≠ TESTNET_P2PKH_PREFIX ∧
    MAINNET_P2SH_PREFIX  ≠ TESTNET_P2SH_PREFIX ∧
    TESTNET_P2PKH_PREFIX ≠ TESTNET_P2SH_PREFIX := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **T7.** Network distinguishability lifted to P2PKH/P2SH addresses: a
serialised mainnet B58 address and a serialised testnet B58 address with the
same kind and hash bytes still produce different wire forms. Tex is excluded
because mainnet Tex and testnet Tex collide with their P2PKH siblings, not
across networks. -/
theorem mainnet_testnet_b58_distinguishable
    (k : AddrKind) (h : List Nat) (hK : k = .p2pkh ∨ k = .p2sh) :
    zcashSerialize { network := .mainnet, kind := k, hash := h } ≠
    zcashSerialize { network := .testnet, kind := k, hash := h } := by
  unfold zcashSerialize
  rcases hK with rfl | rfl <;>
    (unfold prefixFor MAINNET_P2PKH_PREFIX TESTNET_P2PKH_PREFIX
            MAINNET_P2SH_PREFIX TESTNET_P2SH_PREFIX
     simp)

/-- **T8.** The deserialiser rejects byte sequences whose total length is
not exactly 22 (prefix + hash). -/
theorem zcashDeserialize_rejects_wrong_length (bs : List Nat)
    (h : bs.length ≠ WIRE_BYTES) : zcashDeserialize bs = none := by
  unfold zcashDeserialize
  match bs with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: rest =>
    have hr : rest.length ≠ HASH_BYTES := by
      show rest.length ≠ HASH_BYTES
      unfold WIRE_BYTES PREFIX_BYTES HASH_BYTES at h
      simp only [List.length_cons] at h
      intro hh
      unfold HASH_BYTES at hh
      omega
    simp [hr]

/-- **T9.** The deserialiser rejects byte sequences whose first two bytes
don't match any known network/kind prefix. -/
theorem zcashDeserialize_rejects_unknown_prefix (rest : List Nat)
    (hLen : rest.length = HASH_BYTES) (b0 b1 : Nat)
    (h1 : ¬ (b0 = 0x1c ∧ b1 = 0xb8))
    (h2 : ¬ (b0 = 0x1c ∧ b1 = 0xbd))
    (h3 : ¬ (b0 = 0x1d ∧ b1 = 0x25))
    (h4 : ¬ (b0 = 0x1c ∧ b1 = 0xba)) :
    zcashDeserialize (b0 :: b1 :: rest) = none := by
  unfold zcashDeserialize
  simp [hLen, h1, h2, h3, h4]

/-- **T10.** When deserialisation succeeds, the recovered address has a
20-byte hash — the wire-level length-pin. -/
theorem zcashDeserialize_isAddress (bs : List Nat) (a : Address)
    (heq : zcashDeserialize bs = some a) : IsAddress a := by
  unfold IsAddress IsHash
  match bs, heq with
  | [], heq => simp [zcashDeserialize] at heq
  | [_], heq => simp [zcashDeserialize] at heq
  | b0 :: b1 :: rest, heq =>
    simp only [zcashDeserialize] at heq
    by_cases hLen : rest.length = HASH_BYTES
    · -- Length matches: the prefix-dispatch determines which variant we land in,
      -- but in every successful arm the address's hash field is `rest`.
      have : a.hash = rest := by
        simp only [hLen, if_true] at heq
        by_cases h1 : b0 = 0x1c ∧ b1 = 0xb8
        · simp only [h1] at heq
          rw [← Option.some.inj heq]
        · simp only [h1, if_false] at heq
          by_cases h2 : b0 = 0x1c ∧ b1 = 0xbd
          · simp only [h2] at heq
            rw [← Option.some.inj heq]
          · simp only [h2, if_false] at heq
            by_cases h3 : b0 = 0x1d ∧ b1 = 0x25
            · simp only [h3] at heq
              rw [← Option.some.inj heq]
            · simp only [h3, if_false] at heq
              by_cases h4 : b0 = 0x1c ∧ b1 = 0xba
              · simp only [h4] at heq
                rw [← Option.some.inj heq]
              · simp only [h4, if_false] at heq
                exact absurd heq (by simp)
      rw [this]
      exact hLen
    · simp only [hLen, if_false] at heq
      exact absurd heq (by simp)

/-- **T11.** First two bytes of the wire form recover the prefix. The prefix
bytes always sit at positions 0 and 1, in order. -/
theorem zcashSerialize_take_two (a : Address) :
    (zcashSerialize a).take 2 = prefixFor a.network a.kind := by
  unfold zcashSerialize
  have h2 : (prefixFor a.network a.kind).length = 2 := prefixFor_length _ _
  rw [show (2 : Nat) = (prefixFor a.network a.kind).length from h2.symm]
  rw [List.take_left]

/-- **T12.** Bytes from position 2 onward in the wire form are the hash
payload. The hash sits immediately after the 2-byte prefix. -/
theorem zcashSerialize_drop_two (a : Address) :
    (zcashSerialize a).drop 2 = a.hash := by
  unfold zcashSerialize
  have h2 : (prefixFor a.network a.kind).length = 2 := prefixFor_length _ _
  rw [show (2 : Nat) = (prefixFor a.network a.kind).length from h2.symm]
  rw [List.drop_left]

/-! ### ZIP-320 Tex prefix collisions -/

/-- **T13 (ZIP-320 collision, mainnet).** The mainnet Tex prefix is byte-equal
to the mainnet P2PKH prefix. This is consensus-visible through
`NetworkKind::tex_address_prefix` at `zebra-chain/src/parameters/network.rs:113`,
and it is precisely why `ZcashDeserialize` only knows P2PKH/P2SH and ZIP-320
ships TEX over Bech32m: there is no way to recover "this is a TEX" from these
two bytes alone. -/
theorem mainnet_tex_p2pkh_collide :
    MAINNET_TEX_PREFIX = MAINNET_P2PKH_PREFIX := by
  unfold MAINNET_TEX_PREFIX MAINNET_P2PKH_PREFIX
  rfl

/-- **T14 (ZIP-320 collision, testnet/regtest).** The testnet Tex prefix is
byte-equal to the testnet P2PKH prefix. Same collision as on mainnet, and
Regtest inherits both prefixes from Testnet, so Regtest Tex also collides with
Regtest/Testnet P2PKH. -/
theorem testnet_tex_p2pkh_collide :
    TESTNET_TEX_PREFIX = TESTNET_P2PKH_PREFIX := by
  unfold TESTNET_TEX_PREFIX TESTNET_P2PKH_PREFIX
  rfl

/-- **T15 (Tex serialise → P2PKH on the wire).** Serialising any Tex address
and deserialising the result yields the *P2PKH* sibling on the same network,
not the Tex variant. This is the consequence of T13/T14 at the round-trip
level: `ZcashSerialize` honours the Tex prefix, but `ZcashDeserialize` only
emits P2PKH/P2SH, so Tex collapses to P2PKH. -/
theorem zcashSerialize_deserialize_tex_collapses_to_p2pkh
    (n : Network) (hash : List Nat) (hHash : IsHash hash)
    (hN : n = .mainnet ∨ n = .testnet) :
    zcashDeserialize (zcashSerialize { network := n, kind := .tex, hash := hash }) =
      some { network := n, kind := .p2pkh, hash := hash } := by
  unfold zcashSerialize zcashDeserialize
  unfold IsHash at hHash
  rcases hN with rfl | rfl <;>
    (unfold prefixFor MAINNET_TEX_PREFIX TESTNET_TEX_PREFIX
     simp [hHash])

/-! ### Regtest coercion -/

/-- **T16 (Regtest → Testnet on the wire).** A Regtest address — whether
P2PKH, P2SH, or Tex — serialises to the same 22 bytes as the corresponding
Testnet address (P2PKH for Tex, since `ZcashDeserialize` does not know Tex).
The deserialiser only emits `Mainnet`/`Testnet`, so any Regtest input
round-trips as a Testnet sibling. This formalises the
"Rust deserialiser coerces Regtest → Testnet" behaviour. -/
theorem zcashSerialize_deserialize_regtest_collapses_to_testnet
    (k : AddrKind) (hash : List Nat) (hHash : IsHash hash) :
    zcashDeserialize (zcashSerialize { network := .regtest, kind := k, hash := hash }) =
      some { network := .testnet,
             kind := (match k with | .p2pkh => .p2pkh | .p2sh => .p2sh | .tex => .p2pkh),
             hash := hash } := by
  unfold zcashSerialize zcashDeserialize
  unfold IsHash at hHash
  cases k <;>
    (unfold prefixFor TESTNET_P2PKH_PREFIX TESTNET_P2SH_PREFIX TESTNET_TEX_PREFIX
     simp [hHash])

/-- **T17 (Regtest prefix-byte equality).** The Regtest prefix bytes equal
the Testnet prefix bytes for every `AddrKind`. This is the lemma that drives
T16 and reflects `NetworkKind::*_prefix` folding `Testnet | Regtest` to the
same arm. -/
theorem regtest_prefix_eq_testnet (k : AddrKind) :
    prefixFor .regtest k = prefixFor .testnet k := by
  cases k <;> rfl

/-! ### Concrete wire vectors -/

/-- **T18 (mainnet P2PKH zero hash, full wire bytes).** A mainnet P2PKH
address with a 20-byte zero hash serialises to exactly these 22 bytes. -/
theorem serialize_mainnet_p2pkh_zero :
    zcashSerialize { network := .mainnet, kind := .p2pkh,
                     hash := List.replicate HASH_BYTES 0 } =
    [0x1c, 0xb8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  unfold zcashSerialize prefixFor MAINNET_P2PKH_PREFIX HASH_BYTES
  rfl

/-- **T19 (testnet P2SH zero hash, full wire bytes).** A testnet P2SH
address with a 20-byte zero hash serialises to exactly these 22 bytes, with
prefix `[0x1c, 0xba]`. -/
theorem serialize_testnet_p2sh_zero :
    zcashSerialize { network := .testnet, kind := .p2sh,
                     hash := List.replicate HASH_BYTES 0 } =
    [0x1c, 0xba, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  unfold zcashSerialize prefixFor TESTNET_P2SH_PREFIX HASH_BYTES
  rfl

/-- **T20 (mainnet Tex zero hash, collides with P2PKH wire bytes).**
A mainnet Tex address with a 20-byte zero hash serialises to the *same* 22
bytes as the corresponding mainnet P2PKH address with the same hash. This is
the wire-level expression of T13. -/
theorem serialize_mainnet_tex_zero_eq_p2pkh :
    zcashSerialize { network := .mainnet, kind := .tex,
                     hash := List.replicate HASH_BYTES 0 } =
    zcashSerialize { network := .mainnet, kind := .p2pkh,
                     hash := List.replicate HASH_BYTES 0 } := by
  unfold zcashSerialize prefixFor MAINNET_TEX_PREFIX MAINNET_P2PKH_PREFIX
  rfl

/-- **T21 (regtest P2PKH zero hash equals testnet P2PKH zero hash on the
wire).** Regtest and Testnet P2PKH addresses with the same hash produce
identical 22-byte payloads. This is the wire-level expression of T17 for the
P2PKH kind. -/
theorem serialize_regtest_p2pkh_zero_eq_testnet :
    zcashSerialize { network := .regtest, kind := .p2pkh,
                     hash := List.replicate HASH_BYTES 0 } =
    zcashSerialize { network := .testnet, kind := .p2pkh,
                     hash := List.replicate HASH_BYTES 0 } := by
  unfold zcashSerialize prefixFor TESTNET_P2PKH_PREFIX
  rfl

end Zebra.TransparentAddress
