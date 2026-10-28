/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base
import SoftFloat.Core.Base.Types
import SoftFloat.Core.Operators.Format

namespace SoftFloat

-- ANCHOR: SpecializationRiscv
def Format.canonicalNaN (fmt : Format) : Nat :=
  fmt.pack false fmt.expMax fmt.quietBit

def Specialization.riscv : Specialization where
  propagateNaN := fun _ dst _ => dst.canonicalNaN
  setPayloadSign := fun _ _ _ => false
  fusedMultiplyAddZeroInfinityQuietNaNInvalid := true
  tininess := .afterRounding
  intOutOfRange := fun src _ _ signed w x =>
    let u := src.unpack x
    if src.isNaNU u || !u.sign then (if signed then 2 ^ (w - 1) - 1 else 2 ^ w - 1)
    else (if signed then 2 ^ w - 2 ^ (w - 1) else 0)
  totalOrderNaN := fun fmt x y =>
    let px := (fmt.unpack x).fracField % fmt.quietBit
    let py := (fmt.unpack y).fracField % fmt.quietBit
    if (fmt.unpack x).sign then decide (py ≤ px) else decide (px ≤ py)
  admissiblePayload := fun signaling fmt n => decide (n < fmt.quietBit) && (!signaling || n != 0)
  minNumMaxNumOfEqual := fun eq fmt x y =>
    match eq with
    | .minNum | .minNumMag => if (fmt.unpack x).sign then x else y
    | .maxNum | .maxNumMag => if (fmt.unpack x).sign then y else x
  scaleBOfNaNExponent := fun fmt _ x n =>
    (fmt.canonicalNaN, { invalidOperation := fmt.isSNaNU (fmt.unpack x) || fmt.isSNaNU (fmt.unpack n) })
-- ANCHOR_END: SpecializationRiscv

end SoftFloat
