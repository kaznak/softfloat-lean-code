/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Proof.SignClass
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

open SoftFloat Spec

theorem softfloat_correct (sp : Specialization) (hsp : Specialization.Valid sp) :
    Correct sp (softfloat sp) where
  addition _ _ _ _ _ _ h := softfloat_addition_spec sp hsp _ _ _ _ _ _ h.1 h.2
  subtraction _ _ _ _ _ _ h := softfloat_subtraction_spec sp hsp _ _ _ _ _ _ h.1 h.2
  multiplication _ _ _ _ _ _ h := softfloat_multiplication_spec sp hsp _ _ _ _ _ _ h.1 h.2
  division _ _ _ _ _ _ h := softfloat_division_spec sp hsp _ _ _ _ _ _ h.1 h.2
  squareRoot _ _ _ _ h := softfloat_squareRoot_spec sp hsp _ _ _ _ h
  fusedMultiplyAdd _ _ _ _ _ _ _ _ h := softfloat_fusedMultiplyAdd_spec sp hsp _ _ _ _ _ _ _ _
    h.1 h.2.1 h.2.2
  convertFormat _ _ _ _ h := softfloat_convertFormat_spec sp _ _ _ _ h
  convertFromInt _ _ _ _ := softfloat_convertFromInt_spec sp _ _ _
  convertToInteger _ _ _ _ _ _ h := softfloat_convertToInteger_spec sp _ _ _ _ _ _ h.1 h.2
  roundToIntegral _ _ _ _ h := softfloat_roundToIntegral_spec sp _ _ _ _ h
  comparison _ _ _ _ _ _ _ := softfloat_comparison sp _ _ _ _ _ _
  copy _ _ _ := softfloat_copy_spec sp _ _
  negate _ _ h := softfloat_negate_spec sp _ _ h
  abs _ _ h := softfloat_abs_spec sp _ _ h
  copySign _ _ _ h := softfloat_copySign_spec sp _ _ _ h.1 h.2
  minimumNumber _ _ _ h := softfloat_minimumNumber sp hsp _ _ _ h.1 h.2
  maximumNumber _ _ _ h := softfloat_maximumNumber sp hsp _ _ _ h.1 h.2
  minimum _ _ _ h := softfloat_minimum sp hsp _ _ _ h.1 h.2
  maximum _ _ _ h := softfloat_maximum sp hsp _ _ _ h.1 h.2
  classOf _ _ _ := softfloat_classOf_spec sp _ _
  isSignMinus _ _ h := softfloat_isSignMinus_spec sp _ _ h
  isNormal _ _ h := softfloat_isNormal_spec sp _ _ h
  isFinite _ _ h := softfloat_isFinite_spec sp _ _ h
  isZero _ _ h := softfloat_isZero_spec sp _ _ h
  isSubnormal _ _ h := softfloat_isSubnormal_spec sp _ _ h
  isInfinite _ _ h := softfloat_isInfinite_spec sp _ _ h
  isNaN _ _ h := softfloat_isNaN_spec sp _ _ h
  isSignaling _ _ h := softfloat_isSignaling_spec sp _ _ h
  isCanonical _ _ h := softfloat_isCanonical_spec sp _ _ h
  radix _ _ h := softfloat_radix_spec sp _ _ h
  totalOrder _ _ _ h := softfloat_totalOrder_spec sp _ _ _ h.1 h.2
  totalOrderMag _ _ _ h := softfloat_totalOrderMag_spec sp _ _ _ h.1 h.2
  nextUp _ _ h := softfloat_nextUp_spec sp hsp _ _ h
  nextDown _ _ h := softfloat_nextDown_spec sp hsp _ _ h
  minNum _ _ _ h := softfloat_minNum_spec sp hsp _ _ _ h.1 h.2
  maxNum _ _ _ h := softfloat_maxNum_spec sp hsp _ _ _ h.1 h.2
  minNumMag _ _ _ h := softfloat_minNumMag_spec sp hsp _ _ _ h.1 h.2
  maxNumMag _ _ _ h := softfloat_maxNumMag_spec sp hsp _ _ _ h.1 h.2
  minimumMagnitude _ _ _ h := softfloat_minimumMagnitude_spec sp hsp _ _ _ h.1 h.2
  minimumMagnitudeNumber _ _ _ h := softfloat_minimumMagnitudeNumber_spec sp hsp _ _ _ h.1 h.2
  maximumMagnitude _ _ _ h := softfloat_maximumMagnitude_spec sp hsp _ _ _ h.1 h.2
  maximumMagnitudeNumber _ _ _ h := softfloat_maximumMagnitudeNumber_spec sp hsp _ _ _ h.1 h.2
  remainder _ _ _ h := softfloat_remainder_spec sp hsp _ _ _ h.1 h.2
  getPayload _ _ h := softfloat_getPayload_spec sp _ _ h
  setPayload _ _ h := softfloat_setPayload_spec sp hsp _ _ h
  setPayloadSignaling _ _ h := softfloat_setPayloadSignaling_spec sp hsp _ _ h
  logB _ _ _ h := softfloat_logB_spec sp hsp _ _ _ h.1 h.2
  scaleB _ _ _ _ _ h := softfloat_scaleB_spec sp hsp _ _ _ _ _ h.1 h.2.1 h.2.2

end SoftFloat.Proof
