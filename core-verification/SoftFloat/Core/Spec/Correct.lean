/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec.Compare
import SoftFloat.Core.Spec.Sign
import SoftFloat.Core.Spec.Classify
import SoftFloat.Core.Spec.Specialization
import SoftFloat.Core.Spec.Arith
import SoftFloat.Core.Spec.Convert
import SoftFloat.Core.Spec.MinMax
import SoftFloat.Core.Spec.Predicates
import SoftFloat.Core.Spec.TotalOrder
import SoftFloat.Core.Spec.NextUpDown
import SoftFloat.Core.Spec.MinMaxMagnitude
import SoftFloat.Core.Spec.MinNumMaxNum
import SoftFloat.Core.Spec.Remainder
import SoftFloat.Core.Spec.Payload
import SoftFloat.Core.Spec.LogB
import SoftFloat.Core.Spec.Domain

namespace SoftFloat.Spec

open SoftFloat

-- ANCHOR: Correct
structure Correct (sp : Specialization) (o : Ops) : Prop where
  addition : ∀ fa fb dst rm a b, Domain.addition fa fb dst rm a b →
    AdditionSpecOf sp fa fb dst rm a b (o.addition fa fb dst rm a b)
  subtraction : ∀ fa fb dst rm a b, Domain.subtraction fa fb dst rm a b →
    SubtractionSpecOf sp fa fb dst rm a b (o.subtraction fa fb dst rm a b)
  multiplication : ∀ fa fb dst rm a b, Domain.multiplication fa fb dst rm a b →
    MultiplicationSpecOf sp fa fb dst rm a b (o.multiplication fa fb dst rm a b)
  division : ∀ fa fb dst rm a b, Domain.division fa fb dst rm a b →
    DivisionSpecOf sp fa fb dst rm a b (o.division fa fb dst rm a b)
  squareRoot : ∀ fa dst rm a, Domain.squareRoot fa dst rm a →
    SquareRootSpecOf sp fa dst rm a (o.squareRoot fa dst rm a)
  fusedMultiplyAdd : ∀ fa fb fc dst rm a b c, Domain.fusedMultiplyAdd fa fb fc dst rm a b c →
    FusedMultiplyAddSpecOf sp fa fb fc dst rm a b c (o.fusedMultiplyAdd fa fb fc dst rm a b c)
  convertFormat : ∀ src dst rm a, Domain.convertFormat src dst rm a →
    ConvertFormatSpecOf sp src dst rm a (o.convertFormat src dst rm a)
  convertFromInt : ∀ fmt rm v, Domain.convertFromInt fmt rm v →
    ConvertFromIntSpecOf sp fmt rm v (o.convertFromInt fmt rm v)
  convertToInteger : ∀ fmt rm exact signed w a, Domain.convertToInteger fmt rm exact signed w a →
    ConvertToIntegerSpecOf sp fmt rm exact signed w a (o.convertToInteger fmt rm exact signed w a)
  roundToIntegral : ∀ fmt rm exact a, Domain.roundToIntegral fmt rm exact a →
    RoundToIntegralSpecOf sp fmt rm exact a (o.roundToIntegral fmt rm exact a)
  comparison : ∀ fa fb signaling holds a b, Domain.comparison fa fb signaling holds a b →
    ComparisonSpecOf fa fb signaling holds a b (o.comparison fa fb signaling holds a b)
  copy : ∀ fmt x, Domain.copy fmt x →
    CopySpecOf fmt x (o.copy fmt x)
  negate : ∀ fmt x, Domain.negate fmt x →
    NegateSpecOf fmt x (o.negate fmt x)
  abs : ∀ fmt x, Domain.abs fmt x →
    AbsSpecOf fmt x (o.abs fmt x)
  copySign : ∀ fmt x y, Domain.copySign fmt x y →
    CopySignSpecOf fmt x y (o.copySign fmt x y)
  minimumNumber : ∀ fmt a b, Domain.minimumNumber fmt a b →
    MinimumNumberSpecOf sp fmt a b (o.minimumNumber fmt a b)
  maximumNumber : ∀ fmt a b, Domain.maximumNumber fmt a b →
    MaximumNumberSpecOf sp fmt a b (o.maximumNumber fmt a b)
  minimum : ∀ fmt a b, Domain.minimum fmt a b →
    MinimumSpecOf sp fmt a b (o.minimum fmt a b)
  maximum : ∀ fmt a b, Domain.maximum fmt a b →
    MaximumSpecOf sp fmt a b (o.maximum fmt a b)
  classOf : ∀ fmt x, Domain.classOf fmt x →
    ClassSpecOf fmt x (o.classOf fmt x)
  isSignMinus : ∀ fmt x, Domain.isSignMinus fmt x →
    IsSignMinusSpecOf fmt x (o.isSignMinus fmt x)
  isNormal : ∀ fmt x, Domain.isNormal fmt x →
    IsNormalSpecOf fmt x (o.isNormal fmt x)
  isFinite : ∀ fmt x, Domain.isFinite fmt x →
    IsFiniteSpecOf fmt x (o.isFinite fmt x)
  isZero : ∀ fmt x, Domain.isZero fmt x →
    IsZeroSpecOf fmt x (o.isZero fmt x)
  isSubnormal : ∀ fmt x, Domain.isSubnormal fmt x →
    IsSubnormalSpecOf fmt x (o.isSubnormal fmt x)
  isInfinite : ∀ fmt x, Domain.isInfinite fmt x →
    IsInfiniteSpecOf fmt x (o.isInfinite fmt x)
  isNaN : ∀ fmt x, Domain.isNaN fmt x →
    IsNaNSpecOf fmt x (o.isNaN fmt x)
  isSignaling : ∀ fmt x, Domain.isSignaling fmt x →
    IsSignalingSpecOf fmt x (o.isSignaling fmt x)
  isCanonical : ∀ fmt x, Domain.isCanonical fmt x →
    IsCanonicalSpecOf fmt x (o.isCanonical fmt x)
  radix : ∀ fmt x, Domain.radix fmt x →
    RadixSpecOf fmt x (o.radix fmt x)
  totalOrder : ∀ fmt x y, Domain.totalOrder fmt x y →
    TotalOrderSpecOf sp fmt x y (o.totalOrder fmt x y)
  totalOrderMag : ∀ fmt x y, Domain.totalOrderMag fmt x y →
    TotalOrderMagSpecOf sp fmt x y (o.totalOrderMag fmt x y)
  nextUp : ∀ fmt x, Domain.nextUp fmt x →
    NextUpSpecOf sp fmt x (o.nextUp fmt x)
  nextDown : ∀ fmt x, Domain.nextDown fmt x →
    NextDownSpecOf sp fmt x (o.nextDown fmt x)
  minNum : ∀ fmt a b, Domain.minNum fmt a b →
    MinNumSpecOf sp fmt a b (o.minNum fmt a b)
  maxNum : ∀ fmt a b, Domain.maxNum fmt a b →
    MaxNumSpecOf sp fmt a b (o.maxNum fmt a b)
  minNumMag : ∀ fmt a b, Domain.minNumMag fmt a b →
    MinNumMagSpecOf sp fmt a b (o.minNumMag fmt a b)
  maxNumMag : ∀ fmt a b, Domain.maxNumMag fmt a b →
    MaxNumMagSpecOf sp fmt a b (o.maxNumMag fmt a b)
  minimumMagnitude : ∀ fmt a b, Domain.minimumMagnitude fmt a b →
    MinimumMagnitudeSpecOf sp fmt a b (o.minimumMagnitude fmt a b)
  minimumMagnitudeNumber : ∀ fmt a b, Domain.minimumMagnitudeNumber fmt a b →
    MinimumMagnitudeNumberSpecOf sp fmt a b (o.minimumMagnitudeNumber fmt a b)
  maximumMagnitude : ∀ fmt a b, Domain.maximumMagnitude fmt a b →
    MaximumMagnitudeSpecOf sp fmt a b (o.maximumMagnitude fmt a b)
  maximumMagnitudeNumber : ∀ fmt a b, Domain.maximumMagnitudeNumber fmt a b →
    MaximumMagnitudeNumberSpecOf sp fmt a b (o.maximumMagnitudeNumber fmt a b)
  remainder : ∀ fmt a b, Domain.remainder fmt a b →
    RemainderSpecOf sp fmt a b (o.remainder fmt a b)
  getPayload : ∀ fmt x, Domain.getPayload fmt x →
    GetPayloadSpecOf fmt x (o.getPayload fmt x)
  setPayload : ∀ fmt x, Domain.setPayload fmt x →
    SetPayloadSpecOf sp fmt x (o.setPayload fmt x)
  setPayloadSignaling : ∀ fmt x, Domain.setPayloadSignaling fmt x →
    SetPayloadSignalingSpecOf sp fmt x (o.setPayloadSignaling fmt x)
  logB : ∀ fmt lf x, Domain.logB fmt lf x →
    LogBSpecOf sp fmt lf x (o.logB fmt lf x)
  scaleB : ∀ fmt lf rm x n, Domain.scaleB fmt lf rm x n →
    ScaleBSpecOf sp fmt lf rm x n (o.scaleB fmt lf rm x n)
-- ANCHOR_END: Correct

end SoftFloat.Spec
