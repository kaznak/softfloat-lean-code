/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec.Correct

namespace SoftFloat.Spec

open SoftFloat

-- ANCHOR: Agree
structure Agree (o₁ o₂ : Ops) : Prop where
  addition : ∀ fa fb dst rm a b, Domain.addition fa fb dst rm a b →
    o₁.addition fa fb dst rm a b = o₂.addition fa fb dst rm a b
  subtraction : ∀ fa fb dst rm a b, Domain.subtraction fa fb dst rm a b →
    o₁.subtraction fa fb dst rm a b = o₂.subtraction fa fb dst rm a b
  multiplication : ∀ fa fb dst rm a b, Domain.multiplication fa fb dst rm a b →
    o₁.multiplication fa fb dst rm a b = o₂.multiplication fa fb dst rm a b
  division : ∀ fa fb dst rm a b, Domain.division fa fb dst rm a b →
    o₁.division fa fb dst rm a b = o₂.division fa fb dst rm a b
  squareRoot : ∀ fa dst rm a, Domain.squareRoot fa dst rm a →
    o₁.squareRoot fa dst rm a = o₂.squareRoot fa dst rm a
  fusedMultiplyAdd : ∀ fa fb fc dst rm a b c, Domain.fusedMultiplyAdd fa fb fc dst rm a b c →
    o₁.fusedMultiplyAdd fa fb fc dst rm a b c = o₂.fusedMultiplyAdd fa fb fc dst rm a b c
  convertFormat : ∀ src dst rm a, Domain.convertFormat src dst rm a →
    o₁.convertFormat src dst rm a = o₂.convertFormat src dst rm a
  convertFromInt : ∀ fmt rm v, Domain.convertFromInt fmt rm v →
    o₁.convertFromInt fmt rm v = o₂.convertFromInt fmt rm v
  convertToInteger : ∀ fmt rm exact signed w a, Domain.convertToInteger fmt rm exact signed w a →
    o₁.convertToInteger fmt rm exact signed w a = o₂.convertToInteger fmt rm exact signed w a
  roundToIntegral : ∀ fmt rm exact a, Domain.roundToIntegral fmt rm exact a →
    o₁.roundToIntegral fmt rm exact a = o₂.roundToIntegral fmt rm exact a
  comparison : ∀ fa fb signaling holds a b, Domain.comparison fa fb signaling holds a b →
    o₁.comparison fa fb signaling holds a b = o₂.comparison fa fb signaling holds a b
  copy : ∀ fmt x, Domain.copy fmt x →
    o₁.copy fmt x = o₂.copy fmt x
  negate : ∀ fmt x, Domain.negate fmt x →
    o₁.negate fmt x = o₂.negate fmt x
  abs : ∀ fmt x, Domain.abs fmt x →
    o₁.abs fmt x = o₂.abs fmt x
  copySign : ∀ fmt x y, Domain.copySign fmt x y →
    o₁.copySign fmt x y = o₂.copySign fmt x y
  minimumNumber : ∀ fmt a b, Domain.minimumNumber fmt a b →
    o₁.minimumNumber fmt a b = o₂.minimumNumber fmt a b
  maximumNumber : ∀ fmt a b, Domain.maximumNumber fmt a b →
    o₁.maximumNumber fmt a b = o₂.maximumNumber fmt a b
  minimum : ∀ fmt a b, Domain.minimum fmt a b →
    o₁.minimum fmt a b = o₂.minimum fmt a b
  maximum : ∀ fmt a b, Domain.maximum fmt a b →
    o₁.maximum fmt a b = o₂.maximum fmt a b
  classOf : ∀ fmt x, Domain.classOf fmt x →
    o₁.classOf fmt x = o₂.classOf fmt x
  isSignMinus : ∀ fmt x, Domain.isSignMinus fmt x →
    o₁.isSignMinus fmt x = o₂.isSignMinus fmt x
  isNormal : ∀ fmt x, Domain.isNormal fmt x →
    o₁.isNormal fmt x = o₂.isNormal fmt x
  isFinite : ∀ fmt x, Domain.isFinite fmt x →
    o₁.isFinite fmt x = o₂.isFinite fmt x
  isZero : ∀ fmt x, Domain.isZero fmt x →
    o₁.isZero fmt x = o₂.isZero fmt x
  isSubnormal : ∀ fmt x, Domain.isSubnormal fmt x →
    o₁.isSubnormal fmt x = o₂.isSubnormal fmt x
  isInfinite : ∀ fmt x, Domain.isInfinite fmt x →
    o₁.isInfinite fmt x = o₂.isInfinite fmt x
  isNaN : ∀ fmt x, Domain.isNaN fmt x →
    o₁.isNaN fmt x = o₂.isNaN fmt x
  isSignaling : ∀ fmt x, Domain.isSignaling fmt x →
    o₁.isSignaling fmt x = o₂.isSignaling fmt x
  isCanonical : ∀ fmt x, Domain.isCanonical fmt x →
    o₁.isCanonical fmt x = o₂.isCanonical fmt x
  radix : ∀ fmt x, Domain.radix fmt x →
    o₁.radix fmt x = o₂.radix fmt x
  totalOrder : ∀ fmt x y, Domain.totalOrder fmt x y →
    o₁.totalOrder fmt x y = o₂.totalOrder fmt x y
  totalOrderMag : ∀ fmt x y, Domain.totalOrderMag fmt x y →
    o₁.totalOrderMag fmt x y = o₂.totalOrderMag fmt x y
  nextUp : ∀ fmt x, Domain.nextUp fmt x →
    o₁.nextUp fmt x = o₂.nextUp fmt x
  nextDown : ∀ fmt x, Domain.nextDown fmt x →
    o₁.nextDown fmt x = o₂.nextDown fmt x
  minNum : ∀ fmt a b, Domain.minNum fmt a b →
    o₁.minNum fmt a b = o₂.minNum fmt a b
  maxNum : ∀ fmt a b, Domain.maxNum fmt a b →
    o₁.maxNum fmt a b = o₂.maxNum fmt a b
  minNumMag : ∀ fmt a b, Domain.minNumMag fmt a b →
    o₁.minNumMag fmt a b = o₂.minNumMag fmt a b
  maxNumMag : ∀ fmt a b, Domain.maxNumMag fmt a b →
    o₁.maxNumMag fmt a b = o₂.maxNumMag fmt a b
  minimumMagnitude : ∀ fmt a b, Domain.minimumMagnitude fmt a b →
    o₁.minimumMagnitude fmt a b = o₂.minimumMagnitude fmt a b
  minimumMagnitudeNumber : ∀ fmt a b, Domain.minimumMagnitudeNumber fmt a b →
    o₁.minimumMagnitudeNumber fmt a b = o₂.minimumMagnitudeNumber fmt a b
  maximumMagnitude : ∀ fmt a b, Domain.maximumMagnitude fmt a b →
    o₁.maximumMagnitude fmt a b = o₂.maximumMagnitude fmt a b
  maximumMagnitudeNumber : ∀ fmt a b, Domain.maximumMagnitudeNumber fmt a b →
    o₁.maximumMagnitudeNumber fmt a b = o₂.maximumMagnitudeNumber fmt a b
  remainder : ∀ fmt a b, Domain.remainder fmt a b →
    o₁.remainder fmt a b = o₂.remainder fmt a b
  getPayload : ∀ fmt x, Domain.getPayload fmt x →
    o₁.getPayload fmt x = o₂.getPayload fmt x
  setPayload : ∀ fmt x, Domain.setPayload fmt x →
    o₁.setPayload fmt x = o₂.setPayload fmt x
  setPayloadSignaling : ∀ fmt x, Domain.setPayloadSignaling fmt x →
    o₁.setPayloadSignaling fmt x = o₂.setPayloadSignaling fmt x
  logB : ∀ fmt lf x, Domain.logB fmt lf x →
    o₁.logB fmt lf x = o₂.logB fmt lf x
  scaleB : ∀ fmt lf rm x n, Domain.scaleB fmt lf rm x n →
    o₁.scaleB fmt lf rm x n = o₂.scaleB fmt lf rm x n
-- ANCHOR_END: Agree

end SoftFloat.Spec
