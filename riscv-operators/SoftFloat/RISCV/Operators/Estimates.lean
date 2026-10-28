/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Operators.Format
import SoftFloat.RISCV.Base.RoundingMode
import SoftFloat.RISCV.Operators.Specialization

namespace SoftFloat.RISCV

-- ANCHOR: Estimates
def reciprocalSquareRootTable : List Nat :=
  [52, 51, 50, 48, 47, 46, 44, 43, 42, 41, 40, 39, 38, 36, 35, 34,
   33, 32, 31, 30, 30, 29, 28, 27, 26, 25, 24, 23, 23, 22, 21, 20,
   19, 19, 18, 17, 16, 16, 15, 14, 14, 13, 12, 12, 11, 10, 10, 9,
   9, 8, 7, 7, 6, 6, 5, 4, 4, 3, 3, 2, 2, 1, 1, 0,
   127, 125, 123, 121, 119, 118, 116, 114, 113, 111, 109, 108, 106, 105, 103, 102,
   100, 99, 97, 96, 95, 93, 92, 91, 90, 88, 87, 86, 85, 84, 83, 82,
   80, 79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 70, 69, 68, 67, 66,
   65, 64, 63, 63, 62, 61, 60, 59, 59, 58, 57, 56, 56, 55, 54, 53]

def reciprocalTable : List Nat :=
  [127, 125, 123, 121, 119, 117, 116, 114, 112, 110, 109, 107, 105, 104, 102, 100,
   99, 97, 96, 94, 93, 91, 90, 88, 87, 85, 84, 83, 81, 80, 79, 77,
   76, 75, 74, 72, 71, 70, 69, 68, 66, 65, 64, 63, 62, 61, 60, 59,
   58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, 47, 46, 45, 44, 43,
   42, 41, 40, 40, 39, 38, 37, 36, 35, 35, 34, 33, 32, 31, 31, 30,
   29, 28, 28, 27, 26, 25, 25, 24, 23, 23, 22, 21, 21, 20, 19, 19,
   18, 17, 17, 16, 15, 15, 14, 14, 13, 12, 12, 11, 11, 10, 9, 9,
   8, 8, 7, 7, 6, 5, 5, 4, 4, 3, 3, 2, 2, 1, 1, 0]

def normalizedInput (fmt : Format) (u : Format.Unpacked) : Int × Nat :=
  if u.expField = 0 then
    let lz := fmt.fracBits - (Nat.log2 u.fracField + 1)
    (-(lz : Int), u.fracField * 2 ^ (lz + 1) % 2 ^ fmt.fracBits)
  else (u.expField, u.fracField)

def reciprocalSquareRootEstimate7 (fmt : Format) (a : Nat) : Nat × StatusFlags :=
  let u := fmt.unpack a
  if u.expField = fmt.expMax then
    if u.fracField = 0 then
      if u.sign then (fmt.canonicalNaN, { invalidOperation := true }) else (fmt.pack false 0 0, {})
    else (fmt.canonicalNaN, { invalidOperation := decide (u.fracField < 2 ^ (fmt.fracBits - 1)) })
  else if u.expField = 0 ∧ u.fracField = 0 then (fmt.pack u.sign fmt.expMax 0, { divideByZero := true })
  else if u.sign then (fmt.canonicalNaN, { invalidOperation := true })
  else
    let n := normalizedInput fmt u
    let oe := (3 * (fmt.bias : Int) - 1 - n.1) / 2
    let sig := reciprocalSquareRootTable.getD ((n.1 % 2).toNat * 64 + n.2 / 2 ^ (fmt.fracBits - 6)) 0
    (fmt.pack false oe.toNat (sig * 2 ^ (fmt.fracBits - 7)), {})

def reciprocalOverflowsToInfinity : RoundingMode → Bool → Bool
  | .RNE, _ => true
  | .RMM, _ => true
  | .RTZ, _ => false
  | .RUP, s => !s
  | .RDN, s => s

def reciprocalEstimate7 (fmt : Format) (rm : RoundingMode) (a : Nat) : Nat × StatusFlags :=
  let u := fmt.unpack a
  if u.expField = fmt.expMax then
    if u.fracField = 0 then (fmt.pack u.sign 0 0, {})
    else (fmt.canonicalNaN, { invalidOperation := decide (u.fracField < 2 ^ (fmt.fracBits - 1)) })
  else if u.expField = 0 ∧ u.fracField = 0 then (fmt.pack u.sign fmt.expMax 0, { divideByZero := true })
  else
    let n := normalizedInput fmt u
    let oe : Int := 2 * (fmt.bias : Int) - 1 - n.1
    if oe < -1 ∨ 2 * (fmt.bias : Int) < oe then
      (if reciprocalOverflowsToInfinity rm u.sign then fmt.pack u.sign fmt.expMax 0
       else fmt.pack u.sign (fmt.expMax - 1) (2 ^ fmt.fracBits - 1), { overflow := true, inexact := true })
    else
      let sig := reciprocalTable.getD (n.2 / 2 ^ (fmt.fracBits - 7)) 0 * 2 ^ (fmt.fracBits - 7)
      if oe ≤ 0 then (fmt.pack u.sign 0 ((2 ^ fmt.fracBits + sig) / 2 ^ (1 - oe).toNat), {})
      else (fmt.pack u.sign oe.toNat sig, {})
-- ANCHOR_END: Estimates

end SoftFloat.RISCV
