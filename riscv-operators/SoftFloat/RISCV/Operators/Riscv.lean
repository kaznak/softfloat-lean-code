/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Operators.Operations
import SoftFloat.Core.Operators.PerFormat
import SoftFloat.RISCV.Base.Ops
import SoftFloat.RISCV.Operators.Specialization
import SoftFloat.RISCV.Operators.Reduction
import SoftFloat.RISCV.Operators.Instructions
import SoftFloat.RISCV.Operators.Estimates

namespace SoftFloat.RISCV

-- ANCHOR: Riscv
def riscv : RiscvOps where
-- ANCHOR_END: Riscv
-- ANCHOR: Instructions
  instructions fmt :=
    let fo := perFormat (softfloat .riscv) fmt
    { FADD := fun rm a b => fo.addition rm.toRoundingDirection a b
      FSUB := fun rm a b => fo.subtraction rm.toRoundingDirection a b
      FMUL := fun rm a b => fo.multiplication rm.toRoundingDirection a b
      FDIV := fun rm a b => fo.division rm.toRoundingDirection a b
      FSQRT := fun rm a => fo.squareRoot rm.toRoundingDirection a
      FMIN := fo.minimumNumber
      FMAX := fo.maximumNumber
      FMADD := fun rm a b c => fo.fusedMultiplyAdd rm.toRoundingDirection a b c
      FMSUB := fun rm a b c => fo.fusedMultiplyAdd rm.toRoundingDirection a b (fo.negate c)
      FNMSUB := fun rm a b c => fo.fusedMultiplyAdd rm.toRoundingDirection (fo.negate a) b c
      FNMADD := fun rm a b c => fo.fusedMultiplyAdd rm.toRoundingDirection (fo.negate a) b (fo.negate c)
      FSGNJ := fo.copySign
      FSGNJN := fun a b => fo.copySign a (fo.negate b)
      FSGNJX := fun a b => fo.copySign a (if (fmt.unpack a.toNat).sign then fo.negate b else b)
      FEQ := fo.compareQuietEqual
      FLT := fo.compareSignalingLess
      FLE := fo.compareSignalingLessEqual
      FCLASS := fun a => classMask (fo.classOf a)
      FCVT_W_F := fun rm a => fo.convertToInteger rm.toRoundingDirection true true 32 a
      FCVT_WU_F := fun rm a => fo.convertToInteger rm.toRoundingDirection true false 32 a
      FCVT_L_F := fun rm a => fo.convertToInteger rm.toRoundingDirection true true 64 a
      FCVT_LU_F := fun rm a => fo.convertToInteger rm.toRoundingDirection true false 64 a
      FCVT_F_W := fun rm x => fo.convertFromInt rm.toRoundingDirection true x
      FCVT_F_WU := fun rm x => fo.convertFromInt rm.toRoundingDirection false x
      FCVT_F_L := fun rm x => fo.convertFromInt rm.toRoundingDirection true x
      FCVT_F_LU := fun rm x => fo.convertFromInt rm.toRoundingDirection false x
      FLI := loadImmediate fmt
      FMINM := fo.minimum
      FMAXM := fo.maximum
      FROUND := fun rm a => fo.roundToIntegral rm.toRoundingDirection false a
      FROUNDNX := fun rm a => fo.roundToIntegral rm.toRoundingDirection true a
      FLEQ := fo.compareQuietLessEqual
      FLTQ := fo.compareQuietLess
      FCVTMOD_W_D := fun a =>
        let flags := (fo.convertToInteger .roundTowardZero true true 32 a).2
        if (fmt.unpack a.toNat).expField = fmt.expMax then (0#32, flags)
        else ((fo.convertToInteger .roundTowardZero true true (fmt.bias + 2) a).1.setWidth 32, flags) }
-- ANCHOR_END: Instructions
-- ANCHOR: Conversions
  conversions src dst :=
    { FCVT := fun rm a =>
        let r := (softfloat .riscv).convertFormat src dst rm.toRoundingDirection a.toNat
        (BitVec.ofNat dst.width r.1, r.2) }
-- ANCHOR_END: Conversions
-- ANCHOR: Widenings
  widenings narrow wide :=
    let o := softfloat .riscv
    let bits := fun (r : Nat × StatusFlags) => ((BitVec.ofNat wide.width r.1, r.2) : BitVec wide.width × StatusFlags)
    { VFWADD := fun rm a b => bits (o.addition narrow narrow wide rm.toRoundingDirection a.toNat b.toNat)
      VFWSUB := fun rm a b => bits (o.subtraction narrow narrow wide rm.toRoundingDirection a.toNat b.toNat)
      VFWMUL := fun rm a b => bits (o.multiplication narrow narrow wide rm.toRoundingDirection a.toNat b.toNat)
      VFWADD_W := fun rm a b => bits (o.addition wide narrow wide rm.toRoundingDirection a.toNat b.toNat)
      VFWSUB_W := fun rm a b => bits (o.subtraction wide narrow wide rm.toRoundingDirection a.toNat b.toNat)
      VFWMACC := fun rm a b c =>
        bits (o.fusedMultiplyAdd narrow narrow wide wide rm.toRoundingDirection a.toNat b.toNat c.toNat)
      VFWNMACC := fun rm a b c =>
        bits (o.fusedMultiplyAdd narrow narrow wide wide rm.toRoundingDirection (o.negate narrow a.toNat) b.toNat
          (o.negate wide c.toNat))
      VFWMSAC := fun rm a b c =>
        bits (o.fusedMultiplyAdd narrow narrow wide wide rm.toRoundingDirection a.toNat b.toNat (o.negate wide c.toNat))
      VFWNMSAC := fun rm a b c =>
        bits (o.fusedMultiplyAdd narrow narrow wide wide rm.toRoundingDirection (o.negate narrow a.toNat) b.toNat
          c.toNat)
      VFWREDOSUM := fun rm =>
        reduceWithFlags fun a b => bits (o.addition wide narrow wide rm.toRoundingDirection a.toNat b.toNat)
      VFNCVT_ROD_F_F_W := fun a =>
        let r := o.convertFormat wide narrow .roundToOdd a.toNat
        (BitVec.ofNat narrow.width r.1, r.2) }
-- ANCHOR_END: Widenings
-- ANCHOR: Vector
  vectorOps fmt :=
    let fo := perFormat (softfloat .riscv) fmt
    let bits := fun (r : Nat × StatusFlags) => ((BitVec.ofNat fmt.width r.1, r.2) : BitVec fmt.width × StatusFlags)
    { VFRSQRT7 := fun a => bits (reciprocalSquareRootEstimate7 fmt a.toNat)
      VFREC7 := fun rm a => bits (reciprocalEstimate7 fmt rm a.toNat)
      VMFNE := fun a b => (softfloat .riscv).comparison fmt fmt false (· != .equal) a.toNat b.toNat
      VMFGT := fun a b => fo.compareSignalingLess b a
      VMFGE := fun a b => fo.compareSignalingLessEqual b a
      VFCVT_X_F_V := fun rm a => fo.convertToInteger rm.toRoundingDirection true true fmt.width a
      VFCVT_XU_F_V := fun rm a => fo.convertToInteger rm.toRoundingDirection true false fmt.width a
      VFCVT_F_X_V := fun rm x => fo.convertFromInt rm.toRoundingDirection true x
      VFCVT_F_XU_V := fun rm x => fo.convertFromInt rm.toRoundingDirection false x
      VFNCVT_X_F_W := fun rm a => fo.convertToInteger rm.toRoundingDirection true true (fmt.width / 2) a
      VFNCVT_XU_F_W := fun rm a => fo.convertToInteger rm.toRoundingDirection true false (fmt.width / 2) a
      VFWCVT_F_X_V := fun rm x => fo.convertFromInt rm.toRoundingDirection true x
      VFWCVT_F_XU_V := fun rm x => fo.convertFromInt rm.toRoundingDirection false x
      VFREDOSUM := fun rm => reduceWithFlags (fo.addition rm.toRoundingDirection)
      VFREDMIN := reduceWithFlags fo.minimumNumber
      VFREDMAX := reduceWithFlags fo.maximumNumber }
-- ANCHOR_END: Vector
-- ANCHOR: RoundingModeDecoding
  decode rm frm :=
    match (if rm.toNat = 7 then frm else rm).toNat with
    | 0 => some .RNE
    | 1 => some .RTZ
    | 2 => some .RDN
    | 3 => some .RUP
    | 4 => some .RMM
    | _ => none
-- ANCHOR_END: RoundingModeDecoding
-- ANCHOR: Formats
  F16 := perFormat (softfloat .riscv) .binary16
  F32 := perFormat (softfloat .riscv) .binary32
  F64 := perFormat (softfloat .riscv) .binary64
  F128 := perFormat (softfloat .riscv) .binary128
-- ANCHOR_END: Formats
-- ANCHOR: FlagBits
  toFflags f :=
    (if f.inexact then 1 else 0) +
    (if f.underflow then 2 else 0) +
    (if f.overflow then 4 else 0) +
    (if f.divideByZero then 8 else 0) +
    (if f.invalidOperation then 16 else 0)
-- ANCHOR_END: FlagBits

end SoftFloat.RISCV
