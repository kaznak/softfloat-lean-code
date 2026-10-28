/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base
import SoftFloat.Core.Base.Types
import SoftFloat.Core.Operators.Format
import SoftFloat.Core.Operators.Compare

namespace SoftFloat

-- ANCHOR: minmaxNum
namespace Format

def minimumNumberWith (spec : Specialization) (op : NaNOperation) (fmt : Format) (a b : Nat) :
    Nat × StatusFlags :=
  let ua := fmt.unpack a
  let ub := fmt.unpack b
  let inv : StatusFlags := { invalidOperation := fmt.isSNaNU ua || fmt.isSNaNU ub }
  if fmt.isNaNU ua && fmt.isNaNU ub then
    (spec.propagateNaN op fmt [(fmt, a), (fmt, b)], inv)
  else if fmt.isNaNU ua then (b, inv)
  else if fmt.isNaNU ub then (a, inv)
  else if isZeroU ua && isZeroU ub then
    (if ua.sign then a else b, {})
  else
    (if fmt.ltU ua ub then a else b, {})

def maximumNumberWith (spec : Specialization) (op : NaNOperation) (fmt : Format) (a b : Nat) :
    Nat × StatusFlags :=
  let ua := fmt.unpack a
  let ub := fmt.unpack b
  let inv : StatusFlags := { invalidOperation := fmt.isSNaNU ua || fmt.isSNaNU ub }
  if fmt.isNaNU ua && fmt.isNaNU ub then
    (spec.propagateNaN op fmt [(fmt, a), (fmt, b)], inv)
  else if fmt.isNaNU ua then (b, inv)
  else if fmt.isNaNU ub then (a, inv)
  else if isZeroU ua && isZeroU ub then
    (if ua.sign then b else a, {})
  else
    (if fmt.ltU ua ub then b else a, {})

def minimumNumber (spec : Specialization) (fmt : Format) (a b : Nat) : Nat × StatusFlags :=
  fmt.minimumNumberWith spec .minimumNumber a b

def maximumNumber (spec : Specialization) (fmt : Format) (a b : Nat) : Nat × StatusFlags :=
  fmt.maximumNumberWith spec .maximumNumber a b

end Format
-- ANCHOR_END: minmaxNum


-- ANCHOR: minmax
namespace Format

def minimumWith (spec : Specialization) (op : NaNOperation) (fmt : Format) (a b : Nat) :
    Nat × StatusFlags :=
  let ua := fmt.unpack a
  let ub := fmt.unpack b
  if fmt.isNaNU ua || fmt.isNaNU ub then
    (spec.propagateNaN op fmt [(fmt, a), (fmt, b)], { invalidOperation := fmt.isSNaNU ua || fmt.isSNaNU ub })
  else if isZeroU ua && isZeroU ub then
    (if ua.sign then a else b, {})
  else
    (if fmt.ltU ua ub then a else b, {})

def maximumWith (spec : Specialization) (op : NaNOperation) (fmt : Format) (a b : Nat) :
    Nat × StatusFlags :=
  let ua := fmt.unpack a
  let ub := fmt.unpack b
  if fmt.isNaNU ua || fmt.isNaNU ub then
    (spec.propagateNaN op fmt [(fmt, a), (fmt, b)], { invalidOperation := fmt.isSNaNU ua || fmt.isSNaNU ub })
  else if isZeroU ua && isZeroU ub then
    (if ua.sign then b else a, {})
  else
    (if fmt.ltU ua ub then b else a, {})

def minimum (spec : Specialization) (fmt : Format) (a b : Nat) : Nat × StatusFlags :=
  fmt.minimumWith spec .minimum a b

def maximum (spec : Specialization) (fmt : Format) (a b : Nat) : Nat × StatusFlags :=
  fmt.maximumWith spec .maximum a b

end Format
-- ANCHOR_END: minmax

end SoftFloat
