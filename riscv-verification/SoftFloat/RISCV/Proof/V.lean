/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Proof.Correctness
import SoftFloat.Core.Proof.PerFormat
import SoftFloat.RISCV.Spec.Correct
import SoftFloat.RISCV.Spec.V
import SoftFloat.RISCV.Operators.Riscv
import SoftFloat.RISCV.Proof.Formats
import SoftFloat.RISCV.Proof.Instructions
import SoftFloat.RISCV.Proof.VGeneric
import SoftFloat.RISCV.Proof.VEstimate

namespace SoftFloat.RISCV.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.RISCV.Spec

theorem negate_eq_negated (fmt : Format) (a : Nat) (ha : a < 2 ^ fmt.width) :
    (softfloat Specialization.riscv).negate fmt a = negated fmt a :=
  riscv_softfloat_correct.negate fmt a ha

theorem negated_lt (fmt : Format) (a : Nat) : negated fmt a < 2 ^ fmt.width :=
  withSign_lt fmt _ _

theorem widenings_correct (narrow wide : Format) :
    WideningCorrect Specialization.riscv narrow wide (riscv.widenings narrow wide) :=
  have hc := riscv_softfloat_correct
  have haddW : ∀ (m : RoundingMode) (a : BitVec wide.width) (b : BitVec narrow.width),
      AdditionSpecOf Specialization.riscv wide narrow wide m.toRoundingDirection a.toNat b.toNat
        (bitsResult ((riscv.widenings narrow wide).VFWADD_W m a b)) := fun m a b =>
    have h := hc.addition wide narrow wide m.toRoundingDirection a.toNat b.toNat ⟨a.isLt, b.isLt⟩
    spec_bitsResult h h.1
  { VFWADD := fun m a b =>
      have h := hc.addition narrow narrow wide m.toRoundingDirection a.toNat b.toNat ⟨a.isLt, b.isLt⟩
      spec_bitsResult h h.1
    VFWSUB := fun m a b =>
      have h := hc.subtraction narrow narrow wide m.toRoundingDirection a.toNat b.toNat ⟨a.isLt, b.isLt⟩
      spec_bitsResult h h.1
    VFWMUL := fun m a b =>
      have h := hc.multiplication narrow narrow wide m.toRoundingDirection a.toNat b.toNat ⟨a.isLt, b.isLt⟩
      spec_bitsResult h h.1
    VFWADD_W := haddW
    VFWSUB_W := fun m a b =>
      have h := hc.subtraction wide narrow wide m.toRoundingDirection a.toNat b.toNat ⟨a.isLt, b.isLt⟩
      spec_bitsResult h h.1
    VFWMACC := fun m a b c =>
      have h := hc.fusedMultiplyAdd narrow narrow wide wide m.toRoundingDirection a.toNat b.toNat c.toNat
        ⟨a.isLt, b.isLt, c.isLt⟩
      spec_bitsResult h h.1
    VFWNMACC := fun m a b c => by
      have h := hc.fusedMultiplyAdd narrow narrow wide wide m.toRoundingDirection (negated narrow a.toNat) b.toNat
        (negated wide c.toNat) ⟨negated_lt _ _, b.isLt, negated_lt _ _⟩
      dsimp only [riscv]
      rw [negate_eq_negated narrow _ a.isLt, negate_eq_negated wide _ c.isLt]
      exact spec_bitsResult h h.1
    VFWMSAC := fun m a b c => by
      have h := hc.fusedMultiplyAdd narrow narrow wide wide m.toRoundingDirection a.toNat b.toNat
        (negated wide c.toNat) ⟨a.isLt, b.isLt, negated_lt _ _⟩
      dsimp only [riscv]
      rw [negate_eq_negated wide _ c.isLt]
      exact spec_bitsResult h h.1
    VFWNMSAC := fun m a b c => by
      have h := hc.fusedMultiplyAdd narrow narrow wide wide m.toRoundingDirection (negated narrow a.toNat) b.toNat
        c.toNat ⟨negated_lt _ _, b.isLt, c.isLt⟩
      dsimp only [riscv]
      rw [negate_eq_negated narrow _ a.isLt]
      exact spec_bitsResult h h.1
    VFWREDOSUM := fun m => reduceWithFlags_ordered _ (haddW m)
    VFNCVT_ROD_F_F_W := fun a =>
      have h := hc.convertFormat wide narrow .roundToOdd a.toNat a.isLt
      spec_bitsResult h (convertFormat_isEncoding riscv_valid h) }

theorem width_div_two_pos (fmt : Format) : 0 < fmt.width / 2 := by
  have := fmt.expBits_three_le
  unfold Format.width
  omega

theorem width_pos (fmt : Format) : 0 < fmt.width := by
  have := width_div_two_pos fmt
  omega

theorem vectorOps_correct (fmt : Format) (h7 : 7 ≤ fmt.fracBits) :
    VectorCorrect Specialization.riscv fmt (riscv.vectorOps fmt) :=
  have h : FormatCorrect Specialization.riscv fmt (perFormat (softfloat .riscv) fmt) :=
    perFormat_correct riscv_valid riscv_softfloat_correct fmt
  { VFRSQRT7 := fun a => spec_bitsResult (reciprocalSquareRootEstimate7_spec fmt a.toNat)
      (reciprocalSquareRootEstimate7_lt fmt h7 a.toNat)
    VFREC7 := fun m a => spec_bitsResult (reciprocalEstimate7_spec fmt m a.toNat)
      (reciprocalEstimate7_lt fmt h7 m a.toNat)
    VMFNE := fun a b => riscv_softfloat_correct.comparison fmt fmt false (· != .equal) a.toNat b.toNat trivial
    VMFGT := fun a b => comparison_greater_of_less (h.compareSignalingLess b a)
    VMFGE := fun a b => comparison_greaterEqual_of_lessEqual (h.compareSignalingLessEqual b a)
    VFCVT_X_F_V := fun m a => h.convertToInteger m.toRoundingDirection true true fmt.width a (width_pos fmt)
    VFCVT_XU_F_V := fun m a => h.convertToInteger m.toRoundingDirection true false fmt.width a (width_pos fmt)
    VFCVT_F_X_V := fun m x => h.convertFromInt m.toRoundingDirection true x
    VFCVT_F_XU_V := fun m x => h.convertFromInt m.toRoundingDirection false x
    VFNCVT_X_F_W := fun m a =>
      h.convertToInteger m.toRoundingDirection true true (fmt.width / 2) a (width_div_two_pos fmt)
    VFNCVT_XU_F_W := fun m a =>
      h.convertToInteger m.toRoundingDirection true false (fmt.width / 2) a (width_div_two_pos fmt)
    VFWCVT_F_X_V := fun m x => h.convertFromInt m.toRoundingDirection true x
    VFWCVT_F_XU_V := fun m x => h.convertFromInt m.toRoundingDirection false x
    VFREDOSUM := fun m => reduceWithFlags_ordered _ (fun a x => h.addition m.toRoundingDirection a x)
    VFREDMIN := reduceWithFlags_ordered _ h.minimumNumber
    VFREDMAX := reduceWithFlags_ordered _ h.maximumNumber }

theorem vfredusum_correct (fmt : Format) (m : RoundingMode) (inactive : Nat) (init : BitVec fmt.width)
    (xs : List (BitVec fmt.width)) :
    UnorderedSumOf Specialization.riscv fmt fmt m.toRoundingDirection inactive init.toNat (xs.map (·.toNat))
      (bitsResult ((riscv.vectorOps fmt).VFREDOSUM m init xs)) :=
  reduceWithFlags_unordered _
    (perFormat_correct riscv_valid riscv_softfloat_correct fmt |>.addition m.toRoundingDirection) inactive init xs

theorem vfwredusum_correct (narrow wide : Format) (m : RoundingMode) (inactive : Nat) (init : BitVec wide.width)
    (xs : List (BitVec narrow.width)) :
    UnorderedSumOf Specialization.riscv wide narrow m.toRoundingDirection inactive init.toNat (xs.map (·.toNat))
      (bitsResult ((riscv.widenings narrow wide).VFWREDOSUM m init xs)) :=
  reduceWithFlags_unordered _ ((widenings_correct narrow wide).VFWADD_W m) inactive init xs

theorem vfredmin_orderIndependent (fmt : Format) (init : BitVec fmt.width) (xs : List (BitVec fmt.width)) :
    OrderIndependentReductionOf (fun a x s => MinimumNumberSpecOf Specialization.riscv fmt a x s) init.toNat
      (xs.map (·.toNat)) (bitsResult ((riscv.vectorOps fmt).VFREDMIN init xs)) :=
  reduceWithFlags_orderIndependent (op := .minimumNumber) (pickLess := true) _
    (perFormat_correct riscv_valid riscv_softfloat_correct fmt).minimumNumber init xs

theorem vfredmax_orderIndependent (fmt : Format) (init : BitVec fmt.width) (xs : List (BitVec fmt.width)) :
    OrderIndependentReductionOf (fun a x s => MaximumNumberSpecOf Specialization.riscv fmt a x s) init.toNat
      (xs.map (·.toNat)) (bitsResult ((riscv.vectorOps fmt).VFREDMAX init xs)) :=
  reduceWithFlags_orderIndependent (op := .maximumNumber) (pickLess := false) _
    (perFormat_correct riscv_valid riscv_softfloat_correct fmt).maximumNumber init xs

theorem vfrsqrt7_examples :
    ((riscv.vectorOps .binary32).VFRSQRT7 0x00718abc#32).1.toNat = 0x5f080000 ∧
      ((riscv.vectorOps .binary32).VFRSQRT7 0x7f765432#32).1.toNat = 0x1f820000 := by
  decide

theorem vfrec7_examples (m : RoundingMode) :
    ((riscv.vectorOps .binary32).VFREC7 m 0x00718abc#32).1.toNat = 0x7e900000 ∧
      ((riscv.vectorOps .binary32).VFREC7 m 0x7f765432#32).1.toNat = 0x00214000 := by
  cases m <;> decide

end SoftFloat.RISCV.Proof
