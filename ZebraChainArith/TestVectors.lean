import ZebraChainArith.Height
import ZebraChainArith.Amount
import ZebraChainArith.CompactSize

/-!
# Concrete test vectors as kernel-verified propositions

Each `example` here is a `decide`-checked proposition mirroring one of the
doctests in the Rust source. They are not "tests" in the usual sense — once
the file builds, they have been verified by the Lean kernel.

Sources of vectors:
- `CompactSize64` vectors come from the Rust doctests in
  `zebra-chain/src/serialization/compact_size.rs`.
- `Height` vectors come from the inline `operator_tests` in
  `zebra-chain/src/block/height.rs`.
- `Amount` vectors are picked to exercise constraint-boundary behaviour.
-/

namespace Zebra.TestVectors

open Zebra.Amount (Constraint checkedAdd checkedSub mulU64 divU64 neg)
open Zebra.CompactSize

/-! ## CompactSize64 — values from the Rust doctests -/

/-- `0x12` → `[0x12]` (band 1). -/
example : encode 0x12 = [0x12] := by decide

/-- `0xfd` → `[0xfd, 0xfd, 0x00]` (band 2 boundary; band 1 cannot represent
0xfd because that flag byte is reserved). -/
example : encode 0xfd = [0xfd, 0xfd, 0x00] := by decide

/-- `0xaafd` → `[0xfd, 0xfd, 0xaa]` (band 2). -/
example : encode 0xaafd = [0xfd, 0xfd, 0xaa] := by decide

/-- `0xbbaafd` → `[0xfe, 0xfd, 0xaa, 0xbb, 0x00]` (band 3). -/
example : encode 0xbbaafd = [0xfe, 0xfd, 0xaa, 0xbb, 0x00] := by decide

/-- `0x22ccbbaafd` → `[0xff, 0xfd, 0xaa, 0xbb, 0xcc, 0x22, 0x00, 0x00, 0x00]`
(band 4). -/
example : encode 0x22ccbbaafd =
    [0xff, 0xfd, 0xaa, 0xbb, 0xcc, 0x22, 0x00, 0x00, 0x00] := by
  decide

/-- Round-trip: `0x12`. -/
example : decode (encode 0x12) = some (0x12, []) := by decide

/-- Round-trip: `0xaafd`. -/
example : decode (encode 0xaafd) = some (0xaafd, []) := by decide

/-- Round-trip: `0xbbaafd`. -/
example : decode (encode 0xbbaafd) = some (0xbbaafd, []) := by decide

/-! ### Canonicity rejection vectors -/

/-- 3-byte form of `0x12` is rejected: `[0xfd, 0x12, 0x00]` could have been a
single byte `[0x12]`. -/
example : decode [0xfd, 0x12, 0x00] = none := by decide

/-- 5-byte form of `0xaafd` is rejected: it would fit in band 2. -/
example : decode [0xfe, 0xfd, 0xaa, 0x00, 0x00] = none := by decide

/-- 9-byte form of `0xbbaafd` is rejected: it would fit in band 3. -/
example : decode [0xff, 0xfd, 0xaa, 0xbb, 0x00, 0x00, 0x00, 0x00, 0x00] = none := by
  decide

/-- Empty input is rejected. -/
example : decode [] = none := by decide

/-! ## CompactSizeMessage cap -/

/-- A small message size is accepted. -/
example : messageTryFrom 100 = some 100 := by decide

/-- `MAX_PROTOCOL_MESSAGE_LEN + 1` is rejected. -/
example : messageTryFrom (MAX_PROTOCOL_MESSAGE_LEN + 1) = none := by decide

/-! ## Height — vectors from the Rust `operator_tests` -/

/-- `Height::try_from(0) = Some(Height(0))`. -/
example : Zebra.Height.tryFromU32 0 = some 0 := by decide

/-- `Height::try_from(MAX) = Some(MAX)`. -/
example : Zebra.Height.tryFromU32 Zebra.Height.MAX_AS_U32 = some Zebra.Height.MAX_AS_U32 := by
  decide

/-- `Height::try_from(MAX + 1) = None`. -/
example : Zebra.Height.tryFromU32 (Zebra.Height.MAX_AS_U32 + 1) = none := by decide

/-- `Height(1) + 1 = Some(Height(2))`. -/
example : Zebra.Height.add 1 1 = some 2 := by decide

/-- `Height::MAX + 1 = None` (overflow). -/
example : Zebra.Height.add Zebra.Height.MAX_AS_U32 1 = none := by decide

/-- `Height(0) + (-1) = None` (underflow). -/
example : Zebra.Height.add 0 (-1) = none := by decide

/-- `Height(2) + (-1) = Some(Height(1))`. -/
example : Zebra.Height.add 2 (-1) = some 1 := by decide

/-- `subH (Height(2), Height(1)) = 1`. -/
example : Zebra.Height.subH 2 1 = 1 := by decide

/-- `subH (Height(0), Height(1)) = -1`. -/
example : Zebra.Height.subH 0 1 = -1 := by decide

/-! ## Amount — constraint boundaries -/

/-- `validate NonNegative 0 = some 0`. -/
example : Constraint.nonNegative.validate 0 = some 0 := by decide

/-- `validate NonNegative MAX_MONEY = some MAX_MONEY`. -/
example : Constraint.nonNegative.validate Zebra.Amount.MAX_MONEY =
    some Zebra.Amount.MAX_MONEY := by
  decide

/-- `validate NonNegative (MAX_MONEY + 1) = none`. -/
example : Constraint.nonNegative.validate (Zebra.Amount.MAX_MONEY + 1) = none := by
  decide

/-- `validate NonNegative (-1) = none`. -/
example : Constraint.nonNegative.validate (-1) = none := by decide

/-- `validate NegativeAllowed (-MAX_MONEY) = some (-MAX_MONEY)`. -/
example : Constraint.negativeAllowed.validate (-Zebra.Amount.MAX_MONEY) =
    some (-Zebra.Amount.MAX_MONEY) := by
  decide

/-- `validate NegativeOrZero (-1) = some (-1)`. -/
example : Constraint.negativeOrZero.validate (-1) = some (-1) := by decide

/-- `validate NegativeOrZero 1 = none`. -/
example : Constraint.negativeOrZero.validate 1 = none := by decide

/-- Division by zero rejected. -/
example : divU64 Constraint.nonNegative 100 0 = none := by decide

/-- Division within range succeeds. -/
example : divU64 Constraint.nonNegative 100 3 = some 33 := by decide

/-- `neg 0 = 0`. -/
example : neg 0 = 0 := by decide

/-- `neg (neg 5) = 5`. -/
example : neg (neg 5) = 5 := by decide

end Zebra.TestVectors
