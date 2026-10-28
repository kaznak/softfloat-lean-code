/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base
import SoftFloat.Core.Operators.Round
import SoftFloat.Core.Operators.Sign

namespace SoftFloat

namespace Format

-- ANCHOR: addition
def addition (spec : Specialization) (fa fb dst : Format) (rm : RoundingDirection) (a b : Nat) :
    Nat × StatusFlags :=
  let ua := fa.unpack a
  let ub := fb.unpack b
  let nan := spec.propagateNaN .addition dst [(fa, a), (fb, b)]
  if fa.isNaNU ua || fb.isNaNU ub then
    (nan, { invalidOperation := fa.isSNaNU ua || fb.isSNaNU ub })
  else if fa.isInfU ua then
    if fb.isInfU ub && ua.sign != ub.sign then
      (nan, { invalidOperation := true })
    else
      (dst.pack ua.sign dst.expMax 0, {})
  else if fb.isInfU ub then
    (dst.pack ub.sign dst.expMax 0, {})
  else
    let ma := fa.sigOf ua
    let mb := fb.sigOf ub
    let qa := fa.ulpExpOf ua
    let qb := fb.ulpExpOf ub
    let qc := Min.min qa qb
    let A : Int := (if ua.sign then -1 else 1) * ((ma <<< (qa - qc).toNat : Nat) : Int)
    let B : Int := (if ub.sign then -1 else 1) * ((mb <<< (qb - qc).toNat : Nat) : Int)
    let S := A + B
    if S = 0 then
      let zsign : Bool :=
        if ma = 0 && mb = 0 && ua.sign == ub.sign then ua.sign else rm = RoundingDirection.roundTowardNegative
      (dst.pack zsign 0 0, {})
    else
      dst.roundPack spec rm (S < 0) S.natAbs qc
-- ANCHOR_END: addition

-- ANCHOR: multiplication
def multiplication (spec : Specialization) (fa fb dst : Format) (rm : RoundingDirection) (a b : Nat) :
    Nat × StatusFlags :=
  let ua := fa.unpack a
  let ub := fb.unpack b
  let sign : Bool := ua.sign != ub.sign
  let nan := spec.propagateNaN .multiplication dst [(fa, a), (fb, b)]
  if fa.isNaNU ua || fb.isNaNU ub then
    (nan, { invalidOperation := fa.isSNaNU ua || fb.isSNaNU ub })
  else if fa.isInfU ua then
    if isZeroU ub then (nan, { invalidOperation := true })
    else (dst.pack sign dst.expMax 0, {})
  else if fb.isInfU ub then
    if isZeroU ua then (nan, { invalidOperation := true })
    else (dst.pack sign dst.expMax 0, {})
  else if isZeroU ua || isZeroU ub then
    (dst.pack sign 0 0, {})
  else
    dst.roundPack spec rm sign (fa.sigOf ua * fb.sigOf ub) (fa.ulpExpOf ua + fb.ulpExpOf ub)
-- ANCHOR_END: multiplication

-- ANCHOR: fusedMultiplyAdd
def fusedMultiplyAdd (spec : Specialization) (fa fb fc dst : Format) (rm : RoundingDirection)
    (a b c : Nat) : Nat × StatusFlags :=
  let ua := fa.unpack a
  let ub := fb.unpack b
  let uc := fc.unpack c
  let signProd : Bool := ua.sign != ub.sign
  let signC : Bool := uc.sign
  let nan := spec.propagateNaN .fusedMultiplyAdd dst [(fa, a), (fb, b), (fc, c)]
  if fa.isNaNU ua || fb.isNaNU ub then
    (nan, { invalidOperation := fa.isSNaNU ua || fb.isSNaNU ub || fc.isSNaNU uc })
  else if fa.isInfU ua || fb.isInfU ub then
    if isZeroU ua || isZeroU ub then
      (nan,
        { invalidOperation := !(fc.isNaNU uc && !fc.isSNaNU uc)
            || spec.fusedMultiplyAddZeroInfinityQuietNaNInvalid })
    else if fc.isNaNU uc then
      (nan, { invalidOperation := fc.isSNaNU uc })
    else if fc.isInfU uc then
      if signProd == signC then (dst.pack signProd dst.expMax 0, {})
      else (nan, { invalidOperation := true })
    else
      (dst.pack signProd dst.expMax 0, {})
  else if fc.isNaNU uc then
    (nan, { invalidOperation := fc.isSNaNU uc })
  else if fc.isInfU uc then
    (dst.pack signC dst.expMax 0, {})
  else
    let mp := fa.sigOf ua * fb.sigOf ub
    let qp := fa.ulpExpOf ua + fb.ulpExpOf ub
    let mc := fc.sigOf uc
    let qc := fc.ulpExpOf uc
    if mp = 0 then
      if mc = 0 then
        (dst.pack (if signProd == signC then signC else rm = RoundingDirection.roundTowardNegative) 0 0, {})
      else
        dst.roundPack spec rm signC mc qc
    else
      let qmin := Min.min qp qc
      let P : Int := (if signProd then -1 else 1) * ((mp <<< (qp - qmin).toNat : Nat) : Int)
      let C : Int := (if signC then -1 else 1) * ((mc <<< (qc - qmin).toNat : Nat) : Int)
      let S := P + C
      if S = 0 then
        (dst.pack (rm = RoundingDirection.roundTowardNegative) 0 0, {})
      else
        dst.roundPack spec rm (S < 0) S.natAbs qmin
-- ANCHOR_END: fusedMultiplyAdd

-- ANCHOR: subtraction
def subtraction (spec : Specialization) (fa fb dst : Format) (rm : RoundingDirection) (a b : Nat) :
    Nat × StatusFlags :=
  let ua := fa.unpack a
  let ub := fb.unpack b
  let nan := spec.propagateNaN .subtraction dst [(fa, a), (fb, b)]
  if fa.isNaNU ua || fb.isNaNU ub then
    (nan, { invalidOperation := fa.isSNaNU ua || fb.isSNaNU ub })
  else if fa.isInfU ua && fb.isInfU ub && ua.sign == ub.sign then
    (nan, { invalidOperation := true })
  else
    addition spec fa fb dst rm a (fb.flipSign b)
-- ANCHOR_END: subtraction

-- ANCHOR: division
def division (spec : Specialization) (fa fb dst : Format) (rm : RoundingDirection) (a b : Nat) :
    Nat × StatusFlags :=
  let ua := fa.unpack a
  let ub := fb.unpack b
  let sign : Bool := ua.sign != ub.sign
  let nan := spec.propagateNaN .division dst [(fa, a), (fb, b)]
  if fa.isNaNU ua || fb.isNaNU ub then
    (nan, { invalidOperation := fa.isSNaNU ua || fb.isSNaNU ub })
  else if fa.isInfU ua then
    if fb.isInfU ub then (nan, { invalidOperation := true })
    else (dst.pack sign dst.expMax 0, {})
  else if fb.isInfU ub then
    (dst.pack sign 0 0, {})
  else if isZeroU ub then
    if isZeroU ua then (nan, { invalidOperation := true })
    else (dst.pack sign dst.expMax 0, { divideByZero := true })
  else if isZeroU ua then
    (dst.pack sign 0 0, {})
  else
    let ma := fa.sigOf ua
    let mb := fb.sigOf ub
    let k := dst.sigBits + 2 + (Nat.log2 mb + 1)
    let quot := (ma <<< k) / mb
    let rem := (ma <<< k) % mb
    let m := 2 * quot + (if rem = 0 then 0 else 1)
    dst.roundPack spec rm sign m (fa.ulpExpOf ua - fb.ulpExpOf ub - k - 1)
-- ANCHOR_END: division

-- ANCHOR: isqrtAux
def isqrtAux (N : Nat) : Nat → Nat → Nat
  | 0, r => r
  | i + 1, r =>
    let c := r + 2 ^ i
    isqrtAux N i (if c * c ≤ N then c else r)
-- ANCHOR_END: isqrtAux

-- ANCHOR: isqrt
def isqrt (N : Nat) : Nat :=
  isqrtAux N (Nat.log2 N / 2 + 1) 0
-- ANCHOR_END: isqrt

-- ANCHOR: squareRoot
def squareRoot (spec : Specialization) (fa dst : Format) (rm : RoundingDirection) (a : Nat) :
    Nat × StatusFlags :=
  let ua := fa.unpack a
  let nan := spec.propagateNaN .squareRoot dst [(fa, a)]
  if fa.isNaNU ua then
    (nan, { invalidOperation := fa.isSNaNU ua })
  else if isZeroU ua then
    (dst.pack ua.sign 0 0, {})
  else if ua.sign then
    (nan, { invalidOperation := true })
  else if fa.isInfU ua then
    (dst.pack false dst.expMax 0, {})
  else
    let m := fa.sigOf ua
    let q := fa.ulpExpOf ua
    let t0 : Nat := 2 * (dst.sigBits + 2)
    let t : Nat := if (q - t0) % 2 = 0 then t0 else t0 + 1
    let N := m <<< t
    let r := isqrt N
    let m' := 2 * r + (if r * r = N then 0 else 1)
    dst.roundPack spec rm false m' ((q - t) / 2 - 1)
-- ANCHOR_END: squareRoot

end Format

end SoftFloat
