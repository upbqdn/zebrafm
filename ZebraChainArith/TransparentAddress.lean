import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith

/-!
# Transparent address byte layout from `zebra-chain/src/transparent/address.rs`

A Zcash transparent address has the same on-the-wire shape for both the P2PKH
and P2SH variants: a 2-byte network/type prefix followed by a 20-byte hash
payload. The byte arithmetic Zebra performs in
`impl ZcashSerialize for Address` and `impl ZcashDeserialize for Address`
amounts to:

  * `zcash_serialize`: write the network/type-specific 2-byte prefix, then the
    20-byte hash;
  * `zcash_deserialize`: read 2 prefix bytes + 20 hash bytes, then dispatch on
    the prefix to choose the network and the address type.

The concrete prefix byte sequences (from `zcash_protocol::constants`) are:

  * Mainnet P2PKH:  `[0x1c, 0xb8]`
  * Mainnet P2SH:   `[0x1c, 0xbd]`
  * Testnet P2PKH:  `[0x1d, 0x25]`
  * Testnet P2SH:   `[0x1c, 0xba]`

All four prefixes are distinct, which is what makes the `match` arms in
`zcash_deserialize` mutually exclusive.

We model:
  * networks as a two-element enum (`Mainnet`, `Testnet`) — `Regtest` shares
    the testnet prefixes and is folded in for the byte-layout properties we
    care about here;
  * address types as the two byte-layout variants (`P2PKH`, `P2SH`);
  * the 20-byte hash payload as a `List Nat` with a length invariant;
  * the on-the-wire form as the concatenation of the 2-byte prefix and the
    20-byte hash.

The Base58Check shell that wraps these 22 bytes in
`impl fmt::Display for Address` and the `bs58::decode(s).with_check(...)` call
in `impl FromStr for Address` is out of scope: we model exactly the prefix +
hash byte layout that `ZcashSerialize`/`ZcashDeserialize` operates on.
-/

namespace Zebra.TransparentAddress

/-! ## Constants -/

/-- The fixed transparent-address hash width, in bytes (the `[u8; 20]` in
`PayToScriptHash::script_hash` and `PayToPublicKeyHash::pub_key_hash`).
Source: `zebra-chain/src/transparent/address.rs:38` and
`zebra-chain/src/transparent/address.rs:46`. -/
def HASH_BYTES : Nat := 20

/-- The fixed network/type prefix width in bytes.
Source: `zebra-chain/src/transparent/address.rs:207` and the `[u8; 2]`
return type of `NetworkKind::b58_pubkey_address_prefix`. -/
def PREFIX_BYTES : Nat := 2

/-- The total on-the-wire length of a serialised transparent address:
prefix + hash. -/
def WIRE_BYTES : Nat := PREFIX_BYTES + HASH_BYTES

/-! ## Network prefix bytes -/

/-- Mainnet Base58Check P2PKH prefix bytes.
Source: `librustzcash/components/zcash_protocol/src/constants/mainnet.rs:49`
(consumed via `NetworkKind::b58_pubkey_address_prefix`,
`zebra-chain/src/parameters/network.rs:78`). -/
def MAINNET_P2PKH_PREFIX : List Nat := [0x1c, 0xb8]

/-- Mainnet Base58Check P2SH prefix bytes.
Source: `librustzcash/components/zcash_protocol/src/constants/mainnet.rs:54`
(consumed via `NetworkKind::b58_script_address_prefix`,
`zebra-chain/src/parameters/network.rs:89`). -/
def MAINNET_P2SH_PREFIX : List Nat := [0x1c, 0xbd]

/-- Testnet Base58Check P2PKH prefix bytes.
Source: `librustzcash/components/zcash_protocol/src/constants/testnet.rs:49`. -/
def TESTNET_P2PKH_PREFIX : List Nat := [0x1d, 0x25]

/-- Testnet Base58Check P2SH prefix bytes.
Source: `librustzcash/components/zcash_protocol/src/constants/testnet.rs:54`. -/
def TESTNET_P2SH_PREFIX : List Nat := [0x1c, 0xba]

/-! ## Address model -/

/-- The two network kinds whose prefixes we track. `Regtest` shares the
testnet Base58 prefixes, so it's folded into `Testnet` for the byte-layout
properties here.
Source: `zebra-chain/src/parameters/network.rs:78-95`. -/
inductive Network
  | mainnet
  | testnet
  deriving DecidableEq, Repr

/-- The two transparent address variants whose byte layout we model.
`Tex` (ZIP-320) is out of scope: it shares the same 2+20 byte shape but
ships on the wire via Bech32m, not via the `ZcashSerialize` impl we model.
Source: `zebra-chain/src/transparent/address.rs:33-47`. -/
inductive AddrKind
  | p2pkh
  | p2sh
  deriving DecidableEq, Repr

/-- A transparent address, modelled as a (network, kind, 20-byte hash) tuple.
Matches the byte layout of the `Address::PayToPublicKeyHash` and
`Address::PayToScriptHash` variants.
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
`NetworkKind::b58_pubkey_address_prefix` and
`NetworkKind::b58_script_address_prefix`.
Source: `zebra-chain/src/parameters/network.rs:78,89` (used in
`zebra-chain/src/transparent/address.rs:182,189`). -/
def prefixFor : Network → AddrKind → List Nat
  | .mainnet, .p2pkh => MAINNET_P2PKH_PREFIX
  | .mainnet, .p2sh  => MAINNET_P2SH_PREFIX
  | .testnet, .p2pkh => TESTNET_P2PKH_PREFIX
  | .testnet, .p2sh  => TESTNET_P2SH_PREFIX

/-! ## Serialisation -/

/-- `Address::zcash_serialize` writes the 2-byte prefix, then the 20-byte
hash. We model the wire form as the concatenation of those two byte lists.
Source: `zebra-chain/src/transparent/address.rs:176-203`. -/
def zcashSerialize (a : Address) : List Nat :=
  prefixFor a.network a.kind ++ a.hash

/-- `Address::zcash_deserialize` reads 2 prefix bytes + 20 hash bytes, then
dispatches on the prefix to recover the network and address kind. Returns
`none` if the input doesn't match exactly 22 bytes with a known prefix.
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

/-- **T1.** All four network/kind prefixes are exactly 2 bytes long. The
on-the-wire `[u8; 2]` shape pin. -/
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

/-- **T3.** Wire round-trip: serialising a well-formed address and then
deserialising the result yields exactly the original address. Modelled
across all four (network, kind) combinations. -/
theorem zcashSerialize_deserialize (a : Address) (h : IsAddress a) :
    zcashDeserialize (zcashSerialize a) = some a := by
  unfold zcashSerialize zcashDeserialize
  unfold IsAddress IsHash at h
  cases a with
  | mk network kind hash =>
    cases network <;> cases kind <;>
      (unfold prefixFor MAINNET_P2PKH_PREFIX MAINNET_P2SH_PREFIX
              TESTNET_P2PKH_PREFIX TESTNET_P2SH_PREFIX
       simp [h])

/-- **T4.** The mainnet P2PKH prefix differs from the testnet P2PKH prefix:
their first bytes are distinct. This is the "network distinguishability"
property the prompt asks for. -/
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

/-- **T6.** All four (network, kind) prefix pairs are pairwise distinct, so
the deserialiser's prefix dispatch is unambiguous. -/
theorem prefixes_pairwise_distinct :
    MAINNET_P2PKH_PREFIX ≠ MAINNET_P2SH_PREFIX ∧
    MAINNET_P2PKH_PREFIX ≠ TESTNET_P2PKH_PREFIX ∧
    MAINNET_P2PKH_PREFIX ≠ TESTNET_P2SH_PREFIX ∧
    MAINNET_P2SH_PREFIX  ≠ TESTNET_P2PKH_PREFIX ∧
    MAINNET_P2SH_PREFIX  ≠ TESTNET_P2SH_PREFIX ∧
    TESTNET_P2PKH_PREFIX ≠ TESTNET_P2SH_PREFIX := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **T7.** Network distinguishability lifted to addresses: a serialised
mainnet address and a serialised testnet address with the same kind and
hash bytes still produce different wire forms. -/
theorem network_distinguishable
    (k : AddrKind) (h : List Nat) :
    zcashSerialize { network := .mainnet, kind := k, hash := h } ≠
    zcashSerialize { network := .testnet, kind := k, hash := h } := by
  unfold zcashSerialize
  cases k <;>
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

/-- **T11.** Concrete-instance check: a mainnet P2PKH address with a 20-byte
zero hash serialises to the expected 22-byte wire form. -/
theorem serialize_mainnet_p2pkh_zero :
    zcashSerialize { network := .mainnet, kind := .p2pkh,
                     hash := List.replicate HASH_BYTES 0 } =
    [0x1c, 0xb8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  unfold zcashSerialize prefixFor MAINNET_P2PKH_PREFIX HASH_BYTES
  rfl

/-- **T12.** Concrete-instance check: a testnet P2SH address with a 20-byte
zero hash serialises to the expected 22-byte wire form, and the first two
bytes are the testnet-P2SH prefix `[0x1c, 0xba]`. -/
theorem serialize_testnet_p2sh_zero :
    zcashSerialize { network := .testnet, kind := .p2sh,
                     hash := List.replicate HASH_BYTES 0 } =
    [0x1c, 0xba, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  unfold zcashSerialize prefixFor TESTNET_P2SH_PREFIX HASH_BYTES
  rfl

/-- **T13.** First two bytes of the wire form recover the prefix. The
prefix bytes always sit at positions 0 and 1, in order. -/
theorem zcashSerialize_take_two (a : Address) :
    (zcashSerialize a).take 2 = prefixFor a.network a.kind := by
  unfold zcashSerialize
  have h2 : (prefixFor a.network a.kind).length = 2 := prefixFor_length _ _
  rw [show (2 : Nat) = (prefixFor a.network a.kind).length from h2.symm]
  rw [List.take_left]

/-- **T14.** Bytes from position 2 onward in the wire form are the hash
payload. The hash sits immediately after the 2-byte prefix. -/
theorem zcashSerialize_drop_two (a : Address) :
    (zcashSerialize a).drop 2 = a.hash := by
  unfold zcashSerialize
  have h2 : (prefixFor a.network a.kind).length = 2 := prefixFor_length _ _
  rw [show (2 : Nat) = (prefixFor a.network a.kind).length from h2.symm]
  rw [List.drop_left]

end Zebra.TransparentAddress
