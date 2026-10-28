/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.RISCV.Base.Ops
import SoftFloat.RISCV.Spec.Choices
import SoftFloat.RISCV.Spec.Instructions
import SoftFloat.RISCV.Spec.Zfa
import SoftFloat.RISCV.Spec.V
import SoftFloat.RISCV.Spec.Domain
import SoftFloat.RISCV.Spec.Formats

namespace SoftFloat.RISCV.Spec

open SoftFloat SoftFloat.Spec

-- ANCHOR: InstructionCorrect
structure InstructionCorrect (sp : Specialization) (fmt : Format) (o : InstructionOps fmt) : Prop where
  FADD : ∀ m (a b : BitVec fmt.width),
    AdditionSpecOf sp fmt fmt fmt m.toRoundingDirection a.toNat b.toNat (bitsResult (o.FADD m a b))
  FSUB : ∀ m (a b : BitVec fmt.width),
    SubtractionSpecOf sp fmt fmt fmt m.toRoundingDirection a.toNat b.toNat (bitsResult (o.FSUB m a b))
  FMUL : ∀ m (a b : BitVec fmt.width),
    MultiplicationSpecOf sp fmt fmt fmt m.toRoundingDirection a.toNat b.toNat (bitsResult (o.FMUL m a b))
  FDIV : ∀ m (a b : BitVec fmt.width),
    DivisionSpecOf sp fmt fmt fmt m.toRoundingDirection a.toNat b.toNat (bitsResult (o.FDIV m a b))
  FSQRT : ∀ m (a : BitVec fmt.width),
    SquareRootSpecOf sp fmt fmt m.toRoundingDirection a.toNat (bitsResult (o.FSQRT m a))
  FMIN : ∀ (a b : BitVec fmt.width), MinimumNumberSpecOf sp fmt a.toNat b.toNat (bitsResult (o.FMIN a b))
  FMAX : ∀ (a b : BitVec fmt.width), MaximumNumberSpecOf sp fmt a.toNat b.toNat (bitsResult (o.FMAX a b))
  FMADD : ∀ m (a b c : BitVec fmt.width),
    FusedMultiplyAddSpecOf sp fmt fmt fmt fmt m.toRoundingDirection a.toNat b.toNat c.toNat
      (bitsResult (o.FMADD m a b c))
  FMSUB : ∀ m (a b c : BitVec fmt.width),
    FusedMultiplyAddSpecOf sp fmt fmt fmt fmt m.toRoundingDirection a.toNat b.toNat (negated fmt c.toNat)
      (bitsResult (o.FMSUB m a b c))
  FNMSUB : ∀ m (a b c : BitVec fmt.width),
    FusedMultiplyAddSpecOf sp fmt fmt fmt fmt m.toRoundingDirection (negated fmt a.toNat) b.toNat c.toNat
      (bitsResult (o.FNMSUB m a b c))
  FNMADD : ∀ m (a b c : BitVec fmt.width),
    FusedMultiplyAddSpecOf sp fmt fmt fmt fmt m.toRoundingDirection (negated fmt a.toNat) b.toNat
      (negated fmt c.toNat) (bitsResult (o.FNMADD m a b c))
  FSGNJ : ∀ (a b : BitVec fmt.width), CopySignSpecOf fmt a.toNat b.toNat (o.FSGNJ a b).toNat
  FSGNJN : ∀ (a b : BitVec fmt.width),
    (o.FSGNJN a b).toNat = withSign fmt a.toNat (!(fmt.unpack b.toNat).sign)
  FSGNJX : ∀ (a b : BitVec fmt.width),
    (o.FSGNJX a b).toNat = withSign fmt a.toNat ((fmt.unpack a.toNat).sign != (fmt.unpack b.toNat).sign)
  FEQ : ∀ (a b : BitVec fmt.width), ComparisonSpecOf fmt fmt false (· == .equal) a.toNat b.toNat (o.FEQ a b)
  FLT : ∀ (a b : BitVec fmt.width), ComparisonSpecOf fmt fmt true (· == .lessThan) a.toNat b.toNat (o.FLT a b)
  FLE : ∀ (a b : BitVec fmt.width),
    ComparisonSpecOf fmt fmt true (fun r => r == .lessThan || r == .equal) a.toNat b.toNat (o.FLE a b)
  FCLASS : ∀ (a : BitVec fmt.width), (o.FCLASS a).toNat = 2 ^ classMaskBit (classify fmt a.toNat)
  FCVT_W_F : ∀ m (a : BitVec fmt.width),
    ConvertToIntegerSpecOf sp fmt m.toRoundingDirection true true 32 a.toNat (bitsResult (o.FCVT_W_F m a))
  FCVT_WU_F : ∀ m (a : BitVec fmt.width),
    ConvertToIntegerSpecOf sp fmt m.toRoundingDirection true false 32 a.toNat (bitsResult (o.FCVT_WU_F m a))
  FCVT_L_F : ∀ m (a : BitVec fmt.width),
    ConvertToIntegerSpecOf sp fmt m.toRoundingDirection true true 64 a.toNat (bitsResult (o.FCVT_L_F m a))
  FCVT_LU_F : ∀ m (a : BitVec fmt.width),
    ConvertToIntegerSpecOf sp fmt m.toRoundingDirection true false 64 a.toNat (bitsResult (o.FCVT_LU_F m a))
  FCVT_F_W : ∀ m (x : BitVec 32),
    ConvertFromIntSpecOf sp fmt m.toRoundingDirection x.toInt (bitsResult (o.FCVT_F_W m x))
  FCVT_F_WU : ∀ m (x : BitVec 32),
    ConvertFromIntSpecOf sp fmt m.toRoundingDirection x.toNat (bitsResult (o.FCVT_F_WU m x))
  FCVT_F_L : ∀ m (x : BitVec 64),
    ConvertFromIntSpecOf sp fmt m.toRoundingDirection x.toInt (bitsResult (o.FCVT_F_L m x))
  FCVT_F_LU : ∀ m (x : BitVec 64),
    ConvertFromIntSpecOf sp fmt m.toRoundingDirection x.toNat (bitsResult (o.FCVT_F_LU m x))
  FLI : ∀ (i : BitVec 5), LoadImmediateValueOf fmt (loadImmediateEntry i.toNat) (o.FLI i).toNat
  FMINM : ∀ (a b : BitVec fmt.width), MinimumSpecOf sp fmt a.toNat b.toNat (bitsResult (o.FMINM a b))
  FMAXM : ∀ (a b : BitVec fmt.width), MaximumSpecOf sp fmt a.toNat b.toNat (bitsResult (o.FMAXM a b))
  FROUND : ∀ m (a : BitVec fmt.width),
    RoundToIntegralSpecOf sp fmt m.toRoundingDirection false a.toNat (bitsResult (o.FROUND m a))
  FROUNDNX : ∀ m (a : BitVec fmt.width),
    RoundToIntegralSpecOf sp fmt m.toRoundingDirection true a.toNat (bitsResult (o.FROUNDNX m a))
  FLEQ : ∀ (a b : BitVec fmt.width),
    ComparisonSpecOf fmt fmt false (fun r => r == .lessThan || r == .equal) a.toNat b.toNat (o.FLEQ a b)
  FLTQ : ∀ (a b : BitVec fmt.width),
    ComparisonSpecOf fmt fmt false (· == .lessThan) a.toNat b.toNat (o.FLTQ a b)
  FCVTMOD_W_D : ∀ (a : BitVec fmt.width), InstructionDomain.FCVTMOD_W_D fmt a →
    ModularConvertToIntegerSpecOf fmt a.toNat (bitsResult (o.FCVTMOD_W_D a))
-- ANCHOR_END: InstructionCorrect

-- ANCHOR: ConversionCorrect
structure ConversionCorrect (sp : Specialization) (src dst : Format) (o : ConversionOps src dst) : Prop where
  FCVT : ∀ m (a : BitVec src.width),
    ConvertFormatSpecOf sp src dst m.toRoundingDirection a.toNat (bitsResult (o.FCVT m a))
-- ANCHOR_END: ConversionCorrect

-- ANCHOR: WideningCorrect
structure WideningCorrect (sp : Specialization) (narrow wide : Format) (o : WideningOps narrow wide) : Prop where
  VFWADD : ∀ m (a b : BitVec narrow.width),
    AdditionSpecOf sp narrow narrow wide m.toRoundingDirection a.toNat b.toNat (bitsResult (o.VFWADD m a b))
  VFWSUB : ∀ m (a b : BitVec narrow.width),
    SubtractionSpecOf sp narrow narrow wide m.toRoundingDirection a.toNat b.toNat (bitsResult (o.VFWSUB m a b))
  VFWMUL : ∀ m (a b : BitVec narrow.width),
    MultiplicationSpecOf sp narrow narrow wide m.toRoundingDirection a.toNat b.toNat (bitsResult (o.VFWMUL m a b))
  VFWADD_W : ∀ m (a : BitVec wide.width) (b : BitVec narrow.width),
    AdditionSpecOf sp wide narrow wide m.toRoundingDirection a.toNat b.toNat (bitsResult (o.VFWADD_W m a b))
  VFWSUB_W : ∀ m (a : BitVec wide.width) (b : BitVec narrow.width),
    SubtractionSpecOf sp wide narrow wide m.toRoundingDirection a.toNat b.toNat (bitsResult (o.VFWSUB_W m a b))
  VFWMACC : ∀ m (a b : BitVec narrow.width) (c : BitVec wide.width),
    FusedMultiplyAddSpecOf sp narrow narrow wide wide m.toRoundingDirection a.toNat b.toNat c.toNat
      (bitsResult (o.VFWMACC m a b c))
  VFWNMACC : ∀ m (a b : BitVec narrow.width) (c : BitVec wide.width),
    FusedMultiplyAddSpecOf sp narrow narrow wide wide m.toRoundingDirection (negated narrow a.toNat) b.toNat
      (negated wide c.toNat) (bitsResult (o.VFWNMACC m a b c))
  VFWMSAC : ∀ m (a b : BitVec narrow.width) (c : BitVec wide.width),
    FusedMultiplyAddSpecOf sp narrow narrow wide wide m.toRoundingDirection a.toNat b.toNat (negated wide c.toNat)
      (bitsResult (o.VFWMSAC m a b c))
  VFWNMSAC : ∀ m (a b : BitVec narrow.width) (c : BitVec wide.width),
    FusedMultiplyAddSpecOf sp narrow narrow wide wide m.toRoundingDirection (negated narrow a.toNat) b.toNat c.toNat
      (bitsResult (o.VFWNMSAC m a b c))
  VFWREDOSUM : ∀ m (init : BitVec wide.width) (xs : List (BitVec narrow.width)),
    OrderedReductionOf (fun a x s => AdditionSpecOf sp wide narrow wide m.toRoundingDirection a x s) init.toNat
      (xs.map (·.toNat)) (bitsResult (o.VFWREDOSUM m init xs))
  VFNCVT_ROD_F_F_W : ∀ (a : BitVec wide.width),
    ConvertFormatSpecOf sp wide narrow .roundToOdd a.toNat (bitsResult (o.VFNCVT_ROD_F_F_W a))
-- ANCHOR_END: WideningCorrect

-- ANCHOR: VectorCorrect
structure VectorCorrect (sp : Specialization) (fmt : Format) (o : VectorOps fmt) : Prop where
  VFRSQRT7 : ∀ (a : BitVec fmt.width), ReciprocalSquareRootEstimateSpecOf fmt a.toNat (bitsResult (o.VFRSQRT7 a))
  VFREC7 : ∀ m (a : BitVec fmt.width),
    ReciprocalEstimateSpecOf fmt m.toRoundingDirection a.toNat (bitsResult (o.VFREC7 m a))
  VMFNE : ∀ (a b : BitVec fmt.width), ComparisonSpecOf fmt fmt false (· != .equal) a.toNat b.toNat (o.VMFNE a b)
  VMFGT : ∀ (a b : BitVec fmt.width),
    ComparisonSpecOf fmt fmt true (· == .greaterThan) a.toNat b.toNat (o.VMFGT a b)
  VMFGE : ∀ (a b : BitVec fmt.width),
    ComparisonSpecOf fmt fmt true (fun r => r == .greaterThan || r == .equal) a.toNat b.toNat (o.VMFGE a b)
  VFCVT_X_F_V : ∀ m (a : BitVec fmt.width),
    ConvertToIntegerSpecOf sp fmt m.toRoundingDirection true true fmt.width a.toNat (bitsResult (o.VFCVT_X_F_V m a))
  VFCVT_XU_F_V : ∀ m (a : BitVec fmt.width),
    ConvertToIntegerSpecOf sp fmt m.toRoundingDirection true false fmt.width a.toNat
      (bitsResult (o.VFCVT_XU_F_V m a))
  VFCVT_F_X_V : ∀ m (x : BitVec fmt.width),
    ConvertFromIntSpecOf sp fmt m.toRoundingDirection x.toInt (bitsResult (o.VFCVT_F_X_V m x))
  VFCVT_F_XU_V : ∀ m (x : BitVec fmt.width),
    ConvertFromIntSpecOf sp fmt m.toRoundingDirection x.toNat (bitsResult (o.VFCVT_F_XU_V m x))
  VFNCVT_X_F_W : ∀ m (a : BitVec fmt.width),
    ConvertToIntegerSpecOf sp fmt m.toRoundingDirection true true (fmt.width / 2) a.toNat
      (bitsResult (o.VFNCVT_X_F_W m a))
  VFNCVT_XU_F_W : ∀ m (a : BitVec fmt.width),
    ConvertToIntegerSpecOf sp fmt m.toRoundingDirection true false (fmt.width / 2) a.toNat
      (bitsResult (o.VFNCVT_XU_F_W m a))
  VFWCVT_F_X_V : ∀ m (x : BitVec (fmt.width / 2)),
    ConvertFromIntSpecOf sp fmt m.toRoundingDirection x.toInt (bitsResult (o.VFWCVT_F_X_V m x))
  VFWCVT_F_XU_V : ∀ m (x : BitVec (fmt.width / 2)),
    ConvertFromIntSpecOf sp fmt m.toRoundingDirection x.toNat (bitsResult (o.VFWCVT_F_XU_V m x))
  VFREDOSUM : ∀ m (init : BitVec fmt.width) (xs : List (BitVec fmt.width)),
    OrderedReductionOf (fun a x s => AdditionSpecOf sp fmt fmt fmt m.toRoundingDirection a x s) init.toNat
      (xs.map (·.toNat)) (bitsResult (o.VFREDOSUM m init xs))
  VFREDMIN : ∀ (init : BitVec fmt.width) (xs : List (BitVec fmt.width)),
    OrderedReductionOf (fun a x s => MinimumNumberSpecOf sp fmt a x s) init.toNat (xs.map (·.toNat))
      (bitsResult (o.VFREDMIN init xs))
  VFREDMAX : ∀ (init : BitVec fmt.width) (xs : List (BitVec fmt.width)),
    OrderedReductionOf (fun a x s => MaximumNumberSpecOf sp fmt a x s) init.toNat (xs.map (·.toNat))
      (bitsResult (o.VFREDMAX init xs))
-- ANCHOR_END: VectorCorrect

-- ANCHOR: RiscvCorrect
def FflagsOf (f : StatusFlags) (n : Nat) : Prop :=
  n < 2 ^ 5 ∧ n.testBit 4 = f.invalidOperation ∧ n.testBit 3 = f.divideByZero ∧ n.testBit 2 = f.overflow
  ∧ n.testBit 1 = f.underflow ∧ n.testBit 0 = f.inexact

structure RiscvCorrect (sp : Specialization) (o : RiscvOps) : Prop where
  instructions : ∀ fmt ∈ scalarFormats, InstructionCorrect sp fmt (o.instructions fmt)
  conversions : ∀ p ∈ conversionPairs, ConversionCorrect sp p.1 p.2 (o.conversions p.1 p.2)
  widenings : ∀ p ∈ wideningPairs, WideningCorrect sp p.1 p.2 (o.widenings p.1 p.2)
  vectorOps : ∀ fmt ∈ vectorFormats, VectorCorrect sp fmt (o.vectorOps fmt)
  decode : ∀ (rm frm : BitVec 3),
    (o.decode rm frm).map RoundingMode.toRoundingDirection = selectedRoundingDirection rm.toNat frm.toNat
  F16 : FormatCorrect sp .binary16 o.F16
  F32 : FormatCorrect sp .binary32 o.F32
  F64 : FormatCorrect sp .binary64 o.F64
  F128 : FormatCorrect sp .binary128 o.F128
  toFflags : ∀ f, FflagsOf f (o.toFflags f)
  roundingModeMeaning :
    RoundingMode.RNE.toRoundingDirection = .roundTiesToEven ∧
      RoundingMode.RTZ.toRoundingDirection = .roundTowardZero ∧
      RoundingMode.RDN.toRoundingDirection = .roundTowardNegative ∧
      RoundingMode.RUP.toRoundingDirection = .roundTowardPositive ∧
      RoundingMode.RMM.toRoundingDirection = .roundTiesToAway
  unorderedSum : ∀ fmt ∈ vectorFormats, ∀ m inactive (init : BitVec fmt.width) xs,
    UnorderedSumOf sp fmt fmt m.toRoundingDirection inactive init.toNat (xs.map (·.toNat))
      (bitsResult ((o.vectorOps fmt).VFREDOSUM m init xs))
  wideningUnorderedSum : ∀ p ∈ wideningPairs, p.1 ∈ vectorFormats → ∀ m inactive (init : BitVec p.2.width) xs,
    UnorderedSumOf sp p.2 p.1 m.toRoundingDirection inactive init.toNat (xs.map (·.toNat))
      (bitsResult ((o.widenings p.1 p.2).VFWREDOSUM m init xs))
  minMaxReductionOrderIndependent : ∀ fmt ∈ vectorFormats, ∀ (init : BitVec fmt.width) xs,
    OrderIndependentReductionOf (fun a x s => MinimumNumberSpecOf sp fmt a x s) init.toNat (xs.map (·.toNat))
        (bitsResult ((o.vectorOps fmt).VFREDMIN init xs)) ∧
      OrderIndependentReductionOf (fun a x s => MaximumNumberSpecOf sp fmt a x s) init.toNat (xs.map (·.toNat))
        (bitsResult ((o.vectorOps fmt).VFREDMAX init xs))
  narrowingInHalvingSteps : ∀ m (a : BitVec Format.binary64.width),
    (((o.conversions .binary32 .binary16).FCVT m ((o.widenings .binary32 .binary64).VFNCVT_ROD_F_F_W a).1).1,
      ((o.widenings .binary32 .binary64).VFNCVT_ROD_F_F_W a).2.union
        ((o.conversions .binary32 .binary16).FCVT m ((o.widenings .binary32 .binary64).VFNCVT_ROD_F_F_W a).1).2)
      = (o.conversions .binary64 .binary16).FCVT m a
-- ANCHOR_END: RiscvCorrect

end SoftFloat.RISCV.Spec
