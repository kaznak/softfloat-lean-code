/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base
import SoftFloat.Core.Base.Types
import SoftFloat.Core.Operators.Format
import SoftFloat.Core.Operators.MinMax
import SoftFloat.Core.Operators.MinMaxMagnitude

namespace SoftFloat

-- ANCHOR: minNumMaxNum
namespace Format

def signalingNaNResult (spec : Specialization) (op : NaNOperation) (fmt : Format) (a b : Nat) :
    Nat × StatusFlags :=
  (spec.propagateNaN op fmt [(fmt, a), (fmt, b)], { invalidOperation := true })

def minNumWith (spec : Specialization) (op : NaNOperation) (eq : MinNumMaxNumOperation) (fmt : Format)
    (a b : Nat) : Nat × StatusFlags :=
  let ua := fmt.unpack a
  let ub := fmt.unpack b
  if fmt.isSNaNU ua || fmt.isSNaNU ub then fmt.signalingNaNResult spec op a b
  else if fmt.isNaNU ua || fmt.isNaNU ub || fmt.ltU ua ub || fmt.ltU ub ua then fmt.minimumNumberWith spec op a b
  else (spec.minNumMaxNumOfEqual eq fmt a b, {})

def maxNumWith (spec : Specialization) (op : NaNOperation) (eq : MinNumMaxNumOperation) (fmt : Format)
    (a b : Nat) : Nat × StatusFlags :=
  let ua := fmt.unpack a
  let ub := fmt.unpack b
  if fmt.isSNaNU ua || fmt.isSNaNU ub then fmt.signalingNaNResult spec op a b
  else if fmt.isNaNU ua || fmt.isNaNU ub || fmt.ltU ua ub || fmt.ltU ub ua then fmt.maximumNumberWith spec op a b
  else (spec.minNumMaxNumOfEqual eq fmt a b, {})

def minNum (spec : Specialization) (fmt : Format) (a b : Nat) : Nat × StatusFlags :=
  fmt.minNumWith spec .minNum .minNum a b

def maxNum (spec : Specialization) (fmt : Format) (a b : Nat) : Nat × StatusFlags :=
  fmt.maxNumWith spec .maxNum .maxNum a b

def minNumMag (spec : Specialization) (fmt : Format) (a b : Nat) : Nat × StatusFlags :=
  fmt.magnitudeSelect true a b (fmt.minNumWith spec .minNumMag .minNumMag a b)

def maxNumMag (spec : Specialization) (fmt : Format) (a b : Nat) : Nat × StatusFlags :=
  fmt.magnitudeSelect false a b (fmt.maxNumWith spec .maxNumMag .maxNumMag a b)

end Format
-- ANCHOR_END: minNumMaxNum

end SoftFloat
