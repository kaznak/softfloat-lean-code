/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Base.FormatOps
import SoftFloat.Core.Spec.Correct

namespace SoftFloat.Spec

open SoftFloat

-- ANCHOR: FormatCorrect
def bitsResult {w : Nat} (r : BitVec w × StatusFlags) : Nat × StatusFlags := (r.1.toNat, r.2)

structure FormatCorrect (sp : Specialization) (fmt : Format) (fo : FormatOps fmt) : Prop where
  addition : ∀ rm (a b : BitVec fmt.width),
    AdditionSpecOf sp fmt fmt fmt rm a.toNat b.toNat (bitsResult (fo.addition rm a b))
  subtraction : ∀ rm (a b : BitVec fmt.width),
    SubtractionSpecOf sp fmt fmt fmt rm a.toNat b.toNat (bitsResult (fo.subtraction rm a b))
  multiplication : ∀ rm (a b : BitVec fmt.width),
    MultiplicationSpecOf sp fmt fmt fmt rm a.toNat b.toNat (bitsResult (fo.multiplication rm a b))
  division : ∀ rm (a b : BitVec fmt.width),
    DivisionSpecOf sp fmt fmt fmt rm a.toNat b.toNat (bitsResult (fo.division rm a b))
  squareRoot : ∀ rm (a : BitVec fmt.width),
    SquareRootSpecOf sp fmt fmt rm a.toNat (bitsResult (fo.squareRoot rm a))
  fusedMultiplyAdd : ∀ rm (a b c : BitVec fmt.width),
    FusedMultiplyAddSpecOf sp fmt fmt fmt fmt rm a.toNat b.toNat c.toNat
      (bitsResult (fo.fusedMultiplyAdd rm a b c))
  roundToIntegral : ∀ rm exact (a : BitVec fmt.width),
    RoundToIntegralSpecOf sp fmt rm exact a.toNat (bitsResult (fo.roundToIntegral rm exact a))
  compareQuietEqual : ∀ (a b : BitVec fmt.width),
    ComparisonSpecOf fmt fmt false (· == .equal) a.toNat b.toNat (fo.compareQuietEqual a b)
  compareSignalingEqual : ∀ (a b : BitVec fmt.width),
    ComparisonSpecOf fmt fmt true (· == .equal) a.toNat b.toNat (fo.compareSignalingEqual a b)
  compareSignalingLess : ∀ (a b : BitVec fmt.width),
    ComparisonSpecOf fmt fmt true (· == .lessThan) a.toNat b.toNat (fo.compareSignalingLess a b)
  compareQuietLess : ∀ (a b : BitVec fmt.width),
    ComparisonSpecOf fmt fmt false (· == .lessThan) a.toNat b.toNat (fo.compareQuietLess a b)
  compareSignalingLessEqual : ∀ (a b : BitVec fmt.width),
    ComparisonSpecOf fmt fmt true (fun r => r == .lessThan || r == .equal) a.toNat b.toNat
      (fo.compareSignalingLessEqual a b)
  compareQuietLessEqual : ∀ (a b : BitVec fmt.width),
    ComparisonSpecOf fmt fmt false (fun r => r == .lessThan || r == .equal) a.toNat b.toNat
      (fo.compareQuietLessEqual a b)
  convertFormat : ∀ rm (dst : Format) (a : BitVec fmt.width),
    ConvertFormatSpecOf sp fmt dst rm a.toNat (bitsResult (fo.convertFormat rm dst a))
  convertToInteger : ∀ rm exact signed (w : Nat) (a : BitVec fmt.width), 0 < w →
    ConvertToIntegerSpecOf sp fmt rm exact signed w a.toNat
      (bitsResult (fo.convertToInteger rm exact signed w a))
  convertFromInt : ∀ rm (signed : Bool) {w : Nat} (x : BitVec w),
    ConvertFromIntSpecOf sp fmt rm (if signed then x.toInt else (x.toNat : Int))
      (bitsResult (fo.convertFromInt rm signed x))
  copy : ∀ (a : BitVec fmt.width), CopySpecOf fmt a.toNat (fo.copy a).toNat
  abs : ∀ (a : BitVec fmt.width), AbsSpecOf fmt a.toNat (fo.abs a).toNat
  negate : ∀ (a : BitVec fmt.width), NegateSpecOf fmt a.toNat (fo.negate a).toNat
  copySign : ∀ (a b : BitVec fmt.width), CopySignSpecOf fmt a.toNat b.toNat (fo.copySign a b).toNat
  classOf : ∀ (a : BitVec fmt.width), ClassSpecOf fmt a.toNat (fo.classOf a)
  minimumNumber : ∀ (a b : BitVec fmt.width),
    MinimumNumberSpecOf sp fmt a.toNat b.toNat (bitsResult (fo.minimumNumber a b))
  maximumNumber : ∀ (a b : BitVec fmt.width),
    MaximumNumberSpecOf sp fmt a.toNat b.toNat (bitsResult (fo.maximumNumber a b))
  minimum : ∀ (a b : BitVec fmt.width),
    MinimumSpecOf sp fmt a.toNat b.toNat (bitsResult (fo.minimum a b))
  maximum : ∀ (a b : BitVec fmt.width),
    MaximumSpecOf sp fmt a.toNat b.toNat (bitsResult (fo.maximum a b))
-- ANCHOR_END: FormatCorrect

end SoftFloat.Spec
