/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base.Class
import SoftFloat.Core.Operators.Format
import SoftFloat.RISCV.Operators.Specialization

namespace SoftFloat.RISCV

-- ANCHOR: ClassMask
def classMask : Class → BitVec 10
  | .negativeInfinity => 0x001#10
  | .negativeNormal => 0x002#10
  | .negativeSubnormal => 0x004#10
  | .negativeZero => 0x008#10
  | .positiveZero => 0x010#10
  | .positiveSubnormal => 0x020#10
  | .positiveNormal => 0x040#10
  | .positiveInfinity => 0x080#10
  | .signalingNaN => 0x100#10
  | .quietNaN => 0x200#10
-- ANCHOR_END: ClassMask

-- ANCHOR: LoadImmediate
def loadImmediateFields : Nat → Bool × Int × Nat
  | 0 => (true, 0, 0)
  | 2 => (false, -16, 0)
  | 3 => (false, -15, 0)
  | 4 => (false, -8, 0)
  | 5 => (false, -7, 0)
  | 6 => (false, -4, 0)
  | 7 => (false, -3, 0)
  | 8 => (false, -2, 0)
  | 9 => (false, -2, 1)
  | 10 => (false, -2, 2)
  | 11 => (false, -2, 3)
  | 12 => (false, -1, 0)
  | 13 => (false, -1, 1)
  | 14 => (false, -1, 2)
  | 15 => (false, -1, 3)
  | 16 => (false, 0, 0)
  | 17 => (false, 0, 1)
  | 18 => (false, 0, 2)
  | 19 => (false, 0, 3)
  | 20 => (false, 1, 0)
  | 21 => (false, 1, 1)
  | 22 => (false, 1, 2)
  | 23 => (false, 2, 0)
  | 24 => (false, 3, 0)
  | 25 => (false, 4, 0)
  | 26 => (false, 7, 0)
  | 27 => (false, 8, 0)
  | 28 => (false, 15, 0)
  | _ => (false, 16, 0)

def loadImmediate (fmt : Format) (i : BitVec 5) : BitVec fmt.width :=
  BitVec.ofNat fmt.width <|
    match i.toNat with
    | 1 => fmt.pack false 1 0
    | 30 => fmt.pack false fmt.expMax 0
    | 31 => fmt.canonicalNaN
    | k =>
      let (s, e, f) := loadImmediateFields k
      let be : Int := e + fmt.bias
      if (fmt.expMax : Int) ≤ be then fmt.pack false fmt.expMax 0
      else if 0 < be then fmt.pack s be.toNat (f * 2 ^ (fmt.fracBits - 2))
      else fmt.pack s 0 ((2 ^ fmt.fracBits + f * 2 ^ (fmt.fracBits - 2)) / 2 ^ (1 - be).toNat)
-- ANCHOR_END: LoadImmediate

end SoftFloat.RISCV
