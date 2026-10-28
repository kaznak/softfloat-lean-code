/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Proof.Compare
import SoftFloat.Core.Proof.MinMax
import SoftFloat.Core.Proof.ConvertToInteger
import SoftFloat.Core.Proof.AddMul
import SoftFloat.Core.Proof.Division
import SoftFloat.Core.Proof.SquareRoot
import SoftFloat.Core.Proof.FusedMultiplyAdd
import SoftFloat.Core.Proof.ConvertFormat
import SoftFloat.Core.Proof.RoundToIntegral
import SoftFloat.Core.Proof.Predicates
import SoftFloat.Core.Proof.TotalOrder
import SoftFloat.Core.Proof.NextUpDown
import SoftFloat.Core.Proof.MinMaxMagnitude
import SoftFloat.Core.Proof.MinNumMaxNum
import SoftFloat.Core.Proof.Remainder
import SoftFloat.Core.Proof.Payload
import SoftFloat.Core.Proof.LogB

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Format SoftFloat.Spec

theorem correct_agree {sp : Specialization} {o₁ o₂ : Ops} (h₁ : Correct sp o₁)
    (h₂ : Correct sp o₂) : Agree o₁ o₂ where
  addition _ _ _ _ _ _ h := additionSpecOf_unique (h₁.addition _ _ _ _ _ _ h)
    (h₂.addition _ _ _ _ _ _ h)
  subtraction _ _ _ _ _ _ h := subtractionSpecOf_unique (h₁.subtraction _ _ _ _ _ _ h)
    (h₂.subtraction _ _ _ _ _ _ h)
  multiplication _ _ _ _ _ _ h := multiplicationSpecOf_unique
    (h₁.multiplication _ _ _ _ _ _ h) (h₂.multiplication _ _ _ _ _ _ h)
  division _ _ _ _ _ _ h := divisionSpecOf_unique (h₁.division _ _ _ _ _ _ h)
    (h₂.division _ _ _ _ _ _ h)
  squareRoot _ _ _ _ h := squareRootSpecOf_unique (h₁.squareRoot _ _ _ _ h)
    (h₂.squareRoot _ _ _ _ h)
  fusedMultiplyAdd _ _ _ _ _ _ _ _ h := fusedMultiplyAddSpecOf_unique
    (h₁.fusedMultiplyAdd _ _ _ _ _ _ _ _ h) (h₂.fusedMultiplyAdd _ _ _ _ _ _ _ _ h)
  convertFormat _ _ _ _ h := convertFormatSpecOf_unique (h₁.convertFormat _ _ _ _ h)
    (h₂.convertFormat _ _ _ _ h)
  convertFromInt _ _ _ h := convertFromIntSpecOf_unique (h₁.convertFromInt _ _ _ h)
    (h₂.convertFromInt _ _ _ h)
  convertToInteger _ _ _ _ _ _ h := convertToIntegerSpecOf_unique
    (h₁.convertToInteger _ _ _ _ _ _ h) (h₂.convertToInteger _ _ _ _ _ _ h)
  roundToIntegral _ _ _ _ h := roundToIntegralSpecOf_unique (h₁.roundToIntegral _ _ _ _ h)
    (h₂.roundToIntegral _ _ _ _ h)
  comparison _ _ _ _ _ _ h := comparisonSpecOf_unique (h₁.comparison _ _ _ _ _ _ h)
    (h₂.comparison _ _ _ _ _ _ h)
  copy _ _ h := (h₁.copy _ _ h).trans (h₂.copy _ _ h).symm
  negate _ _ h := (h₁.negate _ _ h).trans (h₂.negate _ _ h).symm
  abs _ _ h := (h₁.abs _ _ h).trans (h₂.abs _ _ h).symm
  copySign _ _ _ h := (h₁.copySign _ _ _ h).trans (h₂.copySign _ _ _ h).symm
  minimumNumber _ _ _ h := minMaxNumberSpecOf_unique h.1 h.2 (h₁.minimumNumber _ _ _ h)
    (h₂.minimumNumber _ _ _ h)
  maximumNumber _ _ _ h := minMaxNumberSpecOf_unique h.1 h.2 (h₁.maximumNumber _ _ _ h)
    (h₂.maximumNumber _ _ _ h)
  minimum _ _ _ h := minMaxPropagateSpecOf_unique h.1 h.2 (h₁.minimum _ _ _ h)
    (h₂.minimum _ _ _ h)
  maximum _ _ _ h := minMaxPropagateSpecOf_unique h.1 h.2 (h₁.maximum _ _ _ h)
    (h₂.maximum _ _ _ h)
  classOf _ _ h := (h₁.classOf _ _ h).trans (h₂.classOf _ _ h).symm
  isSignMinus _ _ h := isSignMinusSpecOf_unique (h₁.isSignMinus _ _ h) (h₂.isSignMinus _ _ h)
  isNormal _ _ h := isNormalSpecOf_unique (h₁.isNormal _ _ h) (h₂.isNormal _ _ h)
  isFinite _ _ h := isFiniteSpecOf_unique (h₁.isFinite _ _ h) (h₂.isFinite _ _ h)
  isZero _ _ h := isZeroSpecOf_unique (h₁.isZero _ _ h) (h₂.isZero _ _ h)
  isSubnormal _ _ h := isSubnormalSpecOf_unique (h₁.isSubnormal _ _ h) (h₂.isSubnormal _ _ h)
  isInfinite _ _ h := isInfiniteSpecOf_unique (h₁.isInfinite _ _ h) (h₂.isInfinite _ _ h)
  isNaN _ _ h := isNaNSpecOf_unique (h₁.isNaN _ _ h) (h₂.isNaN _ _ h)
  isSignaling _ _ h := isSignalingSpecOf_unique (h₁.isSignaling _ _ h) (h₂.isSignaling _ _ h)
  isCanonical _ _ h := isCanonicalSpecOf_unique (h₁.isCanonical _ _ h) (h₂.isCanonical _ _ h)
  radix _ _ h := radixSpecOf_unique (h₁.radix _ _ h) (h₂.radix _ _ h)
  totalOrder _ _ _ h := totalOrderSpecOf_unique (h₁.totalOrder _ _ _ h)
    (h₂.totalOrder _ _ _ h)
  totalOrderMag _ _ _ h := totalOrderMagSpecOf_unique (h₁.totalOrderMag _ _ _ h)
    (h₂.totalOrderMag _ _ _ h)
  nextUp _ _ h := nextUpSpecOf_unique (h₁.nextUp _ _ h) (h₂.nextUp _ _ h)
  nextDown _ _ h := nextDownSpecOf_unique (h₁.nextDown _ _ h) (h₂.nextDown _ _ h)
  minNum _ _ _ h := minNumSpecOf_unique h.1 h.2 (h₁.minNum _ _ _ h) (h₂.minNum _ _ _ h)
  maxNum _ _ _ h := maxNumSpecOf_unique h.1 h.2 (h₁.maxNum _ _ _ h) (h₂.maxNum _ _ _ h)
  minNumMag _ _ _ h := minNumMagSpecOf_unique h.1 h.2 (h₁.minNumMag _ _ _ h) (h₂.minNumMag _ _ _ h)
  maxNumMag _ _ _ h := maxNumMagSpecOf_unique h.1 h.2 (h₁.maxNumMag _ _ _ h) (h₂.maxNumMag _ _ _ h)
  minimumMagnitude _ _ _ h := minimumMagnitudeSpecOf_unique h.1 h.2
    (h₁.minimumMagnitude _ _ _ h) (h₂.minimumMagnitude _ _ _ h)
  minimumMagnitudeNumber _ _ _ h := minimumMagnitudeNumberSpecOf_unique h.1 h.2
    (h₁.minimumMagnitudeNumber _ _ _ h) (h₂.minimumMagnitudeNumber _ _ _ h)
  maximumMagnitude _ _ _ h := maximumMagnitudeSpecOf_unique h.1 h.2
    (h₁.maximumMagnitude _ _ _ h) (h₂.maximumMagnitude _ _ _ h)
  maximumMagnitudeNumber _ _ _ h := maximumMagnitudeNumberSpecOf_unique h.1 h.2
    (h₁.maximumMagnitudeNumber _ _ _ h) (h₂.maximumMagnitudeNumber _ _ _ h)
  remainder _ _ _ h := remainderSpecOf_unique (h₁.remainder _ _ _ h) (h₂.remainder _ _ _ h)
  getPayload _ _ h := getPayloadSpecOf_unique (h₁.getPayload _ _ h) (h₂.getPayload _ _ h)
  setPayload _ _ h := setPayloadSpecOf_unique (h₁.setPayload _ _ h) (h₂.setPayload _ _ h)
  setPayloadSignaling _ _ h := setPayloadSignalingSpecOf_unique (h₁.setPayloadSignaling _ _ h)
    (h₂.setPayloadSignaling _ _ h)
  logB _ _ _ h := logBSpecOf_unique (h₁.logB _ _ _ h) (h₂.logB _ _ _ h)
  scaleB _ _ _ _ _ h := scaleBSpecOf_unique h.1 h.2.2 (h₁.scaleB _ _ _ _ _ h)
    (h₂.scaleB _ _ _ _ _ h)

end SoftFloat.Proof
