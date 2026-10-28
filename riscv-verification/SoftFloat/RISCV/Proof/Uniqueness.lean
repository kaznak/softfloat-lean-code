/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Proof.Common
import SoftFloat.Core.Proof.Uniqueness
import SoftFloat.Core.Proof.ConvertToInteger
import SoftFloat.RISCV.Spec.Correct
import SoftFloat.RISCV.Spec.Agree

namespace SoftFloat.RISCV.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.RISCV.Spec

theorem bitsResult_inj {w : Nat} {r₁ r₂ : BitVec w × StatusFlags} (h : bitsResult r₁ = bitsResult r₂) : r₁ = r₂ := by
  obtain ⟨a, f⟩ := r₁
  obtain ⟨b, g⟩ := r₂
  simp only [bitsResult, Prod.mk.injEq] at h
  rw [BitVec.eq_of_toNat_eq h.1, h.2]

theorem orderedReductionOf_unique {step : Nat → Nat → Nat × StatusFlags → Prop} {good : Nat → Prop}
    (hstep : ∀ a x s t, good a → good x → step a x s → step a x t → s = t)
    (hgood : ∀ a x s, good a → good x → step a x s → good s.1) :
    ∀ (a : Nat) (xs : List Nat) (r₁ r₂ : Nat × StatusFlags), good a → (∀ x ∈ xs, good x) →
      OrderedReductionOf step a xs r₁ → OrderedReductionOf step a xs r₂ → r₁ = r₂
  | _, [], _, _, _, _, h₁, h₂ => h₁.trans h₂.symm
  | a, x :: xs, _, _, ha, hxs, ⟨s, t, hs, ht, hr⟩, ⟨s', t', hs', ht', hr'⟩ => by
    have hx := hxs x (List.mem_cons_self ..)
    obtain rfl := hstep _ _ _ _ ha hx hs hs'
    obtain rfl := orderedReductionOf_unique hstep hgood s.1 xs t t' (hgood _ _ _ ha hx hs)
      (fun y hy => hxs y (List.mem_cons_of_mem _ hy)) ht ht'
    rw [hr, hr']

theorem orderedReduction_unique_of {wa wb : Nat} {step : Nat → Nat → Nat × StatusFlags → Prop}
    (hstep : ∀ a x s t, step a x s → step a x t → s = t) (init : BitVec wa) (xs : List (BitVec wb))
    {r₁ r₂ : BitVec wa × StatusFlags}
    (h₁ : OrderedReductionOf step init.toNat (xs.map (·.toNat)) (bitsResult r₁))
    (h₂ : OrderedReductionOf step init.toNat (xs.map (·.toNat)) (bitsResult r₂)) : r₁ = r₂ :=
  bitsResult_inj (orderedReductionOf_unique (good := fun _ => True) (fun a x s t _ _ => hstep a x s t)
    (fun _ _ _ _ _ _ => trivial) _ _ _ _ trivial (fun _ _ => trivial) h₁ h₂)

theorem minMaxReduction_unique {sp : Specialization} {op : NaNOperation} {pickLess : Bool} {fmt : Format}
    (init : BitVec fmt.width) (xs : List (BitVec fmt.width)) {r₁ r₂ : BitVec fmt.width × StatusFlags}
    (h₁ : OrderedReductionOf (fun a x s => MinMaxNumberSpecOf sp op pickLess fmt a x s) init.toNat
      (xs.map (·.toNat)) (bitsResult r₁))
    (h₂ : OrderedReductionOf (fun a x s => MinMaxNumberSpecOf sp op pickLess fmt a x s) init.toNat
      (xs.map (·.toNat)) (bitsResult r₂)) : r₁ = r₂ := by
  refine bitsResult_inj (orderedReductionOf_unique (good := fun a => a < 2 ^ fmt.width)
    (fun a x s t ha hx hs ht => minMaxNumberSpecOf_unique ha hx hs ht) (fun _ _ _ _ _ hs => hs.1) _ _ _ _
    init.isLt ?_ h₁ h₂)
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx
  exact y.isLt

theorem loadImmediateEntry_ne_zero (k : Nat) (x : ℝ) (h : loadImmediateEntry k = .value x) : x ≠ 0 := by
  unfold loadImmediateEntry at h
  split at h <;> first | (cases h; norm_num) | cases h

theorem loadImmediateValueOf_unique {fmt : Format} {e : LoadImmediateEntry} (he : ∀ x, e = .value x → x ≠ 0)
    {r₁ r₂ : Nat} (h1r : r₁ < 2 ^ fmt.width) (h2r : r₂ < 2 ^ fmt.width)
    (h₁ : LoadImmediateValueOf fmt e r₁) (h₂ : LoadImmediateValueOf fmt e r₂) : r₁ = r₂ := by
  cases e with
  | value x =>
    by_cases hex : ∃ n, fmt.IsEncoding n ∧ IsFinite fmt n ∧ valR fmt n = x
    · obtain ⟨hf1, hv1⟩ := h₁.1 hex
      obtain ⟨hf2, hv2⟩ := h₂.1 hex
      exact eq_of_valR_eq fmt h1r h2r hf1 hf2 (hv1.trans hv2.symm) (hv1 ▸ he x rfl)
    · exact eq_of_classify_eq_infinity fmt h1r h2r (h₁.2 hex) (h₂.2 hex)
  | minPositiveNormal =>
    have hf1 : IsFinite fmt r₁ := by unfold IsFinite; rw [h₁.1]; trivial
    have hf2 : IsFinite fmt r₂ := by unfold IsFinite; rw [h₂.1]; trivial
    exact eq_of_valR_eq fmt h1r h2r hf1 hf2 (h₁.2.trans h₂.2.symm) (by rw [h₁.2]; positivity)
  | infinity => exact eq_of_classify_eq_infinity fmt h1r h2r h₁ h₂
  | canonicalNaN => exact h₁.trans h₂.symm

theorem modularConvertToIntegerSpecOf_unique {fmt : Format} {a : Nat} {r₁ r₂ : Nat × StatusFlags}
    (h₁ : ModularConvertToIntegerSpecOf fmt a r₁) (h₂ : ModularConvertToIntegerSpecOf fmt a r₂) : r₁ = r₂ := by
  unfold ModularConvertToIntegerSpecOf at h₁ h₂
  cases hc : classify fmt a <;> simp only [hc] at h₁ h₂
  all_goals first
    | exact h₁.trans h₂.symm
    | (refine Prod.ext (h₁.1.trans h₂.1.symm) ?_
       split_ifs at h₁ h₂
       · exact h₁.2.trans h₂.2.symm
       · exact integralFlagsOf_unique h₁.2 h₂.2)

theorem reciprocalSquareRootEstimateSpecOf_unique {fmt : Format} {a : Nat} {r₁ r₂ : Nat × StatusFlags}
    (h₁ : ReciprocalSquareRootEstimateSpecOf fmt a r₁) (h₂ : ReciprocalSquareRootEstimateSpecOf fmt a r₂) :
    r₁ = r₂ := by
  unfold ReciprocalSquareRootEstimateSpecOf at h₁ h₂
  generalize classify fmt a = c at h₁ h₂
  rcases c with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> dsimp only at h₁ h₂ <;> exact h₁.trans h₂.symm

theorem reciprocalEstimateSpecOf_unique {fmt : Format} {rm : RoundingDirection} {a : Nat}
    {r₁ r₂ : Nat × StatusFlags}
    (h₁ : ReciprocalEstimateSpecOf fmt rm a r₁) (h₂ : ReciprocalEstimateSpecOf fmt rm a r₂) : r₁ = r₂ := by
  unfold ReciprocalEstimateSpecOf at h₁ h₂
  generalize classify fmt a = c at h₁ h₂
  rcases c with _ | _ | ⟨_ | _⟩ | ⟨_ | _⟩ | ⟨_ | _⟩ | ⟨_ | _⟩ <;> dsimp only at h₁ h₂ <;>
    (try split_ifs at h₁ h₂) <;> exact h₁.trans h₂.symm

theorem instructions_agree {sp : Specialization} {fmt : Format} {o₁ o₂ : InstructionOps fmt}
    (h₁ : InstructionCorrect sp fmt o₁) (h₂ : InstructionCorrect sp fmt o₂) : InstructionAgree fmt o₁ o₂ where
  FADD m a b := bitsResult_inj (additionSpecOf_unique (h₁.FADD m a b) (h₂.FADD m a b))
  FSUB m a b := bitsResult_inj (subtractionSpecOf_unique (h₁.FSUB m a b) (h₂.FSUB m a b))
  FMUL m a b := bitsResult_inj (multiplicationSpecOf_unique (h₁.FMUL m a b) (h₂.FMUL m a b))
  FDIV m a b := bitsResult_inj (divisionSpecOf_unique (h₁.FDIV m a b) (h₂.FDIV m a b))
  FSQRT m a := bitsResult_inj (squareRootSpecOf_unique (h₁.FSQRT m a) (h₂.FSQRT m a))
  FMIN a b := bitsResult_inj (minMaxNumberSpecOf_unique a.isLt b.isLt (h₁.FMIN a b) (h₂.FMIN a b))
  FMAX a b := bitsResult_inj (minMaxNumberSpecOf_unique a.isLt b.isLt (h₁.FMAX a b) (h₂.FMAX a b))
  FMADD m a b c := bitsResult_inj (fusedMultiplyAddSpecOf_unique (h₁.FMADD m a b c) (h₂.FMADD m a b c))
  FMSUB m a b c := bitsResult_inj (fusedMultiplyAddSpecOf_unique (h₁.FMSUB m a b c) (h₂.FMSUB m a b c))
  FNMSUB m a b c := bitsResult_inj (fusedMultiplyAddSpecOf_unique (h₁.FNMSUB m a b c) (h₂.FNMSUB m a b c))
  FNMADD m a b c := bitsResult_inj (fusedMultiplyAddSpecOf_unique (h₁.FNMADD m a b c) (h₂.FNMADD m a b c))
  FSGNJ a b := BitVec.eq_of_toNat_eq ((h₁.FSGNJ a b).trans (h₂.FSGNJ a b).symm)
  FSGNJN a b := BitVec.eq_of_toNat_eq ((h₁.FSGNJN a b).trans (h₂.FSGNJN a b).symm)
  FSGNJX a b := BitVec.eq_of_toNat_eq ((h₁.FSGNJX a b).trans (h₂.FSGNJX a b).symm)
  FEQ a b := comparisonSpecOf_unique (h₁.FEQ a b) (h₂.FEQ a b)
  FLT a b := comparisonSpecOf_unique (h₁.FLT a b) (h₂.FLT a b)
  FLE a b := comparisonSpecOf_unique (h₁.FLE a b) (h₂.FLE a b)
  FCLASS a := BitVec.eq_of_toNat_eq ((h₁.FCLASS a).trans (h₂.FCLASS a).symm)
  FCVT_W_F m a := bitsResult_inj (convertToIntegerSpecOf_unique (h₁.FCVT_W_F m a) (h₂.FCVT_W_F m a))
  FCVT_WU_F m a := bitsResult_inj (convertToIntegerSpecOf_unique (h₁.FCVT_WU_F m a) (h₂.FCVT_WU_F m a))
  FCVT_L_F m a := bitsResult_inj (convertToIntegerSpecOf_unique (h₁.FCVT_L_F m a) (h₂.FCVT_L_F m a))
  FCVT_LU_F m a := bitsResult_inj (convertToIntegerSpecOf_unique (h₁.FCVT_LU_F m a) (h₂.FCVT_LU_F m a))
  FCVT_F_W m x := bitsResult_inj (convertFromIntSpecOf_unique (h₁.FCVT_F_W m x) (h₂.FCVT_F_W m x))
  FCVT_F_WU m x := bitsResult_inj (convertFromIntSpecOf_unique (h₁.FCVT_F_WU m x) (h₂.FCVT_F_WU m x))
  FCVT_F_L m x := bitsResult_inj (convertFromIntSpecOf_unique (h₁.FCVT_F_L m x) (h₂.FCVT_F_L m x))
  FCVT_F_LU m x := bitsResult_inj (convertFromIntSpecOf_unique (h₁.FCVT_F_LU m x) (h₂.FCVT_F_LU m x))
  FLI i := BitVec.eq_of_toNat_eq (loadImmediateValueOf_unique (loadImmediateEntry_ne_zero i.toNat)
    (o₁.FLI i).isLt (o₂.FLI i).isLt (h₁.FLI i) (h₂.FLI i))
  FMINM a b := bitsResult_inj (minMaxPropagateSpecOf_unique a.isLt b.isLt (h₁.FMINM a b) (h₂.FMINM a b))
  FMAXM a b := bitsResult_inj (minMaxPropagateSpecOf_unique a.isLt b.isLt (h₁.FMAXM a b) (h₂.FMAXM a b))
  FROUND m a := bitsResult_inj (roundToIntegralSpecOf_unique (h₁.FROUND m a) (h₂.FROUND m a))
  FROUNDNX m a := bitsResult_inj (roundToIntegralSpecOf_unique (h₁.FROUNDNX m a) (h₂.FROUNDNX m a))
  FLEQ a b := comparisonSpecOf_unique (h₁.FLEQ a b) (h₂.FLEQ a b)
  FLTQ a b := comparisonSpecOf_unique (h₁.FLTQ a b) (h₂.FLTQ a b)
  FCVTMOD_W_D a h := bitsResult_inj
    (modularConvertToIntegerSpecOf_unique (h₁.FCVTMOD_W_D a h) (h₂.FCVTMOD_W_D a h))

theorem conversions_agree {sp : Specialization} {src dst : Format} {o₁ o₂ : ConversionOps src dst}
    (h₁ : ConversionCorrect sp src dst o₁) (h₂ : ConversionCorrect sp src dst o₂) : ConversionAgree src dst o₁ o₂ where
  FCVT m a := bitsResult_inj (convertFormatSpecOf_unique (h₁.FCVT m a) (h₂.FCVT m a))

theorem widenings_agree {sp : Specialization} {narrow wide : Format} {o₁ o₂ : WideningOps narrow wide}
    (h₁ : WideningCorrect sp narrow wide o₁) (h₂ : WideningCorrect sp narrow wide o₂) :
    WideningAgree narrow wide o₁ o₂ where
  VFWADD m a b := bitsResult_inj (additionSpecOf_unique (h₁.VFWADD m a b) (h₂.VFWADD m a b))
  VFWSUB m a b := bitsResult_inj (subtractionSpecOf_unique (h₁.VFWSUB m a b) (h₂.VFWSUB m a b))
  VFWMUL m a b := bitsResult_inj (multiplicationSpecOf_unique (h₁.VFWMUL m a b) (h₂.VFWMUL m a b))
  VFWADD_W m a b := bitsResult_inj (additionSpecOf_unique (h₁.VFWADD_W m a b) (h₂.VFWADD_W m a b))
  VFWSUB_W m a b := bitsResult_inj (subtractionSpecOf_unique (h₁.VFWSUB_W m a b) (h₂.VFWSUB_W m a b))
  VFWMACC m a b c := bitsResult_inj (fusedMultiplyAddSpecOf_unique (h₁.VFWMACC m a b c) (h₂.VFWMACC m a b c))
  VFWNMACC m a b c := bitsResult_inj (fusedMultiplyAddSpecOf_unique (h₁.VFWNMACC m a b c) (h₂.VFWNMACC m a b c))
  VFWMSAC m a b c := bitsResult_inj (fusedMultiplyAddSpecOf_unique (h₁.VFWMSAC m a b c) (h₂.VFWMSAC m a b c))
  VFWNMSAC m a b c := bitsResult_inj (fusedMultiplyAddSpecOf_unique (h₁.VFWNMSAC m a b c) (h₂.VFWNMSAC m a b c))
  VFWREDOSUM m init xs := orderedReduction_unique_of
    (step := fun a x s => AdditionSpecOf sp wide narrow wide m.toRoundingDirection a x s)
    (fun _ _ _ _ hs ht => additionSpecOf_unique hs ht) init xs
    (h₁.VFWREDOSUM m init xs) (h₂.VFWREDOSUM m init xs)
  VFNCVT_ROD_F_F_W a := bitsResult_inj (convertFormatSpecOf_unique (h₁.VFNCVT_ROD_F_F_W a) (h₂.VFNCVT_ROD_F_F_W a))

theorem vectorOps_agree {sp : Specialization} {fmt : Format} {o₁ o₂ : VectorOps fmt}
    (h₁ : VectorCorrect sp fmt o₁) (h₂ : VectorCorrect sp fmt o₂) : VectorAgree fmt o₁ o₂ where
  VFRSQRT7 a := bitsResult_inj (reciprocalSquareRootEstimateSpecOf_unique (h₁.VFRSQRT7 a) (h₂.VFRSQRT7 a))
  VFREC7 m a := bitsResult_inj (reciprocalEstimateSpecOf_unique (h₁.VFREC7 m a) (h₂.VFREC7 m a))
  VMFNE a b := comparisonSpecOf_unique (h₁.VMFNE a b) (h₂.VMFNE a b)
  VMFGT a b := comparisonSpecOf_unique (h₁.VMFGT a b) (h₂.VMFGT a b)
  VMFGE a b := comparisonSpecOf_unique (h₁.VMFGE a b) (h₂.VMFGE a b)
  VFCVT_X_F_V m a := bitsResult_inj (convertToIntegerSpecOf_unique (h₁.VFCVT_X_F_V m a) (h₂.VFCVT_X_F_V m a))
  VFCVT_XU_F_V m a := bitsResult_inj (convertToIntegerSpecOf_unique (h₁.VFCVT_XU_F_V m a) (h₂.VFCVT_XU_F_V m a))
  VFCVT_F_X_V m x := bitsResult_inj (convertFromIntSpecOf_unique (h₁.VFCVT_F_X_V m x) (h₂.VFCVT_F_X_V m x))
  VFCVT_F_XU_V m x := bitsResult_inj (convertFromIntSpecOf_unique (h₁.VFCVT_F_XU_V m x) (h₂.VFCVT_F_XU_V m x))
  VFNCVT_X_F_W m a := bitsResult_inj (convertToIntegerSpecOf_unique (h₁.VFNCVT_X_F_W m a) (h₂.VFNCVT_X_F_W m a))
  VFNCVT_XU_F_W m a :=
    bitsResult_inj (convertToIntegerSpecOf_unique (h₁.VFNCVT_XU_F_W m a) (h₂.VFNCVT_XU_F_W m a))
  VFWCVT_F_X_V m x := bitsResult_inj (convertFromIntSpecOf_unique (h₁.VFWCVT_F_X_V m x) (h₂.VFWCVT_F_X_V m x))
  VFWCVT_F_XU_V m x := bitsResult_inj (convertFromIntSpecOf_unique (h₁.VFWCVT_F_XU_V m x) (h₂.VFWCVT_F_XU_V m x))
  VFREDOSUM m init xs := orderedReduction_unique_of
    (step := fun a x s => AdditionSpecOf sp fmt fmt fmt m.toRoundingDirection a x s)
    (fun _ _ _ _ hs ht => additionSpecOf_unique hs ht) init xs
    (h₁.VFREDOSUM m init xs) (h₂.VFREDOSUM m init xs)
  VFREDMIN init xs := minMaxReduction_unique init xs (h₁.VFREDMIN init xs) (h₂.VFREDMIN init xs)
  VFREDMAX init xs := minMaxReduction_unique init xs (h₁.VFREDMAX init xs) (h₂.VFREDMAX init xs)

end SoftFloat.RISCV.Proof
