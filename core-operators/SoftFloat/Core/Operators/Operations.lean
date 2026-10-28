/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Operators.Arith
import SoftFloat.Core.Operators.Compare
import SoftFloat.Core.Operators.Convert
import SoftFloat.Core.Operators.MinMax
import SoftFloat.Core.Operators.Predicates
import SoftFloat.Core.Operators.TotalOrder
import SoftFloat.Core.Operators.NextUpDown
import SoftFloat.Core.Operators.MinMaxMagnitude
import SoftFloat.Core.Operators.MinNumMaxNum
import SoftFloat.Core.Operators.Remainder
import SoftFloat.Core.Operators.Payload
import SoftFloat.Core.Operators.LogB

namespace SoftFloat

-- ANCHOR: Operations
def softfloat (sp : Specialization) : Ops where
  addition := Format.addition sp
  subtraction := Format.subtraction sp
  multiplication := Format.multiplication sp
  division := Format.division sp
  squareRoot := Format.squareRoot sp
  fusedMultiplyAdd := Format.fusedMultiplyAdd sp
  convertFormat := Format.convertFormat sp
  convertFromInt := Format.convertFromInt sp
  convertToInteger := Format.convertToInteger sp
  roundToIntegral := Format.roundToIntegral sp
  comparison := Format.comparison
  copy := Format.copy
  negate := Format.negate
  abs := Format.abs
  copySign := Format.copySign
  minimumNumber := Format.minimumNumber sp
  maximumNumber := Format.maximumNumber sp
  minimum := Format.minimum sp
  maximum := Format.maximum sp
  classOf := Format.classOf
  isSignMinus := Format.isSignMinus
  isNormal := Format.isNormal
  isFinite := Format.isFinite
  isZero := Format.isZero
  isSubnormal := Format.isSubnormal
  isInfinite := Format.isInfinite
  isNaN := Format.isNaN
  isSignaling := Format.isSignaling
  isCanonical := Format.isCanonical
  radix := Format.radix
  totalOrder := Format.totalOrder sp
  totalOrderMag := Format.totalOrderMag sp
  nextUp := Format.nextUp sp
  nextDown := Format.nextDown sp
  minNum := Format.minNum sp
  maxNum := Format.maxNum sp
  minNumMag := Format.minNumMag sp
  maxNumMag := Format.maxNumMag sp
  minimumMagnitude := Format.minimumMagnitude sp
  minimumMagnitudeNumber := Format.minimumMagnitudeNumber sp
  maximumMagnitude := Format.maximumMagnitude sp
  maximumMagnitudeNumber := Format.maximumMagnitudeNumber sp
  remainder := Format.remainder sp
  getPayload := Format.getPayload
  setPayload := Format.setPayload sp
  setPayloadSignaling := Format.setPayloadSignaling sp
  logB := Format.logB sp
  scaleB := Format.scaleB sp
-- ANCHOR_END: Operations

end SoftFloat
