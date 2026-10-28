/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Proof.Encoding
import SoftFloat.Core.Proof.PerFormat
import SoftFloat.RISCV.Spec.Correct
import SoftFloat.RISCV.Operators.Riscv
import SoftFloat.RISCV.Proof.Formats
import SoftFloat.RISCV.Proof.Zfa

namespace SoftFloat.RISCV.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.RISCV.Spec

theorem negate_toNat {sp : Specialization} {fmt : Format} {fo : FormatOps fmt} (h : FormatCorrect sp fmt fo)
    (a : BitVec fmt.width) : (fo.negate a).toNat = negated fmt a.toNat :=
  h.negate a

theorem sign_negated (fmt : Format) (x : Nat) : (fmt.unpack (negated fmt x)).sign = !(fmt.unpack x).sign := by
  unfold negated
  rw [unpack_withSign]

theorem classMask_toClass (c : FloatClass) : (classMask c.toClass).toNat = 2 ^ classMaskBit c := by
  rcases c with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> rfl

theorem instructions_correct_of (fmt : Format)
    (hFLI : ∀ i, LoadImmediateValueOf fmt (loadImmediateEntry i.toNat) (loadImmediate fmt i).toNat)
    (hMOD : fmt = .binary64 → ∀ a,
      ModularConvertToIntegerSpecOf fmt a.toNat (bitsResult ((riscv.instructions fmt).FCVTMOD_W_D a))) :
    InstructionCorrect Specialization.riscv fmt (riscv.instructions fmt) :=
  let fo := perFormat (softfloat .riscv) fmt
  have h : FormatCorrect Specialization.riscv fmt fo := perFormat_correct riscv_valid riscv_softfloat_correct fmt
  { FADD := fun m a b => h.addition m.toRoundingDirection a b
    FSUB := fun m a b => h.subtraction m.toRoundingDirection a b
    FMUL := fun m a b => h.multiplication m.toRoundingDirection a b
    FDIV := fun m a b => h.division m.toRoundingDirection a b
    FSQRT := fun m a => h.squareRoot m.toRoundingDirection a
    FMIN := h.minimumNumber
    FMAX := h.maximumNumber
    FMADD := fun m a b c => h.fusedMultiplyAdd m.toRoundingDirection a b c
    FMSUB := fun m a b c => by
      have := h.fusedMultiplyAdd m.toRoundingDirection a b (fo.negate c)
      rwa [negate_toNat h] at this
    FNMSUB := fun m a b c => by
      have := h.fusedMultiplyAdd m.toRoundingDirection (fo.negate a) b c
      rwa [negate_toNat h] at this
    FNMADD := fun m a b c => by
      have := h.fusedMultiplyAdd m.toRoundingDirection (fo.negate a) b (fo.negate c)
      rwa [negate_toNat h, negate_toNat h] at this
    FSGNJ := h.copySign
    FSGNJN := fun a b => by
      have := h.copySign a (fo.negate b)
      unfold CopySignSpecOf at this
      show (fo.copySign a (fo.negate b)).toNat = _
      rw [this, negate_toNat h, sign_negated]
    FSGNJX := fun a b => by
      have := h.copySign a (if (fmt.unpack a.toNat).sign then fo.negate b else b)
      unfold CopySignSpecOf at this
      show (fo.copySign a (if (fmt.unpack a.toNat).sign then fo.negate b else b)).toNat = _
      rw [this]
      cases hs : (fmt.unpack a.toNat).sign
      · simp
      · simp [negate_toNat h, sign_negated]
    FEQ := h.compareQuietEqual
    FLT := h.compareSignalingLess
    FLE := h.compareSignalingLessEqual
    FCLASS := fun a => by
      have := h.classOf a
      unfold ClassSpecOf at this
      show (classMask (fo.classOf a)).toNat = _
      simp only [this, classMask_toClass]
    FCVT_W_F := fun m a => h.convertToInteger m.toRoundingDirection true true 32 a (by decide)
    FCVT_WU_F := fun m a => h.convertToInteger m.toRoundingDirection true false 32 a (by decide)
    FCVT_L_F := fun m a => h.convertToInteger m.toRoundingDirection true true 64 a (by decide)
    FCVT_LU_F := fun m a => h.convertToInteger m.toRoundingDirection true false 64 a (by decide)
    FCVT_F_W := fun m x => h.convertFromInt m.toRoundingDirection true x
    FCVT_F_WU := fun m x => h.convertFromInt m.toRoundingDirection false x
    FCVT_F_L := fun m x => h.convertFromInt m.toRoundingDirection true x
    FCVT_F_LU := fun m x => h.convertFromInt m.toRoundingDirection false x
    FLI := hFLI
    FMINM := h.minimum
    FMAXM := h.maximum
    FROUND := fun m a => h.roundToIntegral m.toRoundingDirection false a
    FROUNDNX := fun m a => h.roundToIntegral m.toRoundingDirection true a
    FLEQ := h.compareQuietLessEqual
    FLTQ := h.compareQuietLess
    FCVTMOD_W_D := fun a hd => hMOD hd a }

theorem instructions_correct :
    ∀ fmt ∈ scalarFormats,
      InstructionCorrect Specialization.riscv fmt (riscv.instructions fmt) := by
  intro fmt hfmt
  simp only [scalarFormats, List.mem_cons, List.not_mem_nil, or_false] at hfmt
  rcases hfmt with rfl | rfl | rfl | rfl
  · exact instructions_correct_of _ binary16_loadImmediate_correct (fun h => absurd h (by decide))
  · exact instructions_correct_of _ binary32_loadImmediate_correct (fun h => absurd h (by decide))
  · exact instructions_correct_of _ binary64_loadImmediate_correct (fun _ => binary64_modularConvertToInteger_correct)
  · exact instructions_correct_of _ binary128_loadImmediate_correct (fun h => absurd h (by decide))

end SoftFloat.RISCV.Proof
