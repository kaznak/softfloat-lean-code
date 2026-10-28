/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.RISCV.Spec.Choices
import SoftFloat.RISCV.Spec.Correct
import SoftFloat.RISCV.Spec.Agree
import SoftFloat.RISCV.Operators.Riscv
import SoftFloat.RISCV.Proof.Specialization
import SoftFloat.RISCV.Proof.Formats
import SoftFloat.RISCV.Proof.RoundingMode
import SoftFloat.RISCV.Proof.Instructions
import SoftFloat.RISCV.Proof.Conversions
import SoftFloat.RISCV.Proof.V
import SoftFloat.RISCV.Proof.Uniqueness
import SoftFloat.RISCV.Proof.RoundToOdd

namespace SoftFloat.RISCV.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.RISCV.Spec

theorem vectorOps_correct_of_mem :
    ∀ fmt ∈ vectorFormats, VectorCorrect Specialization.riscv fmt (riscv.vectorOps fmt) := by
  intro fmt hfmt
  simp only [vectorFormats, List.mem_cons, List.not_mem_nil, or_false] at hfmt
  rcases hfmt with rfl | rfl | rfl <;> exact vectorOps_correct _ (by decide)

theorem riscv_toFflags (f : StatusFlags) : FflagsOf f (riscv.toFflags f) := by
  obtain ⟨a, b, c, d, e⟩ := f
  unfold FflagsOf
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

theorem fflagsOf_unique {f : StatusFlags} {n m : Nat} (h₁ : FflagsOf f n) (h₂ : FflagsOf f m) : n = m := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 5
  · obtain ⟨-, a4, a3, a2, a1, a0⟩ := h₁
    obtain ⟨-, b4, b3, b2, b1, b0⟩ := h₂
    interval_cases i
    exacts [a0.trans b0.symm, a1.trans b1.symm, a2.trans b2.symm, a3.trans b3.symm, a4.trans b4.symm]
  · have hp : 2 ^ 5 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h₁.1 hp), Nat.testBit_lt_two_pow (lt_of_lt_of_le h₂.1 hp)]

theorem riscv_correct : RiscvCorrect Specialization.riscv riscv where
  instructions := instructions_correct
  conversions p _ := conversions_correct p.1 p.2
  widenings p _ := widenings_correct p.1 p.2
  vectorOps := vectorOps_correct_of_mem
  decode := decode_toRoundingDirection
  F16 := binary16_correct
  F32 := binary32_correct
  F64 := binary64_correct
  F128 := binary128_correct
  toFflags := riscv_toFflags
  roundingModeMeaning := toRoundingDirection_constructors
  unorderedSum fmt _ := vfredusum_correct fmt
  wideningUnorderedSum p _ _ := vfwredusum_correct p.1 p.2
  minMaxReductionOrderIndependent fmt _ init xs :=
    ⟨vfredmin_orderIndependent fmt init xs, vfredmax_orderIndependent fmt init xs⟩
  narrowingInHalvingSteps := narrowing_halving_steps

theorem riscv_choices_correct : RiscvChoices Specialization.riscv ∧ RiscvCorrect Specialization.riscv riscv :=
  ⟨riscv_choices, riscv_correct⟩

theorem riscv_agree {sp : Specialization} {o₁ o₂ : RiscvOps} (h₁ : RiscvCorrect sp o₁) (h₂ : RiscvCorrect sp o₂) :
    RiscvAgree o₁ o₂ where
  instructions fmt h := instructions_agree (h₁.instructions fmt h) (h₂.instructions fmt h)
  conversions p h := conversions_agree (h₁.conversions p h) (h₂.conversions p h)
  widenings p h := widenings_agree (h₁.widenings p h) (h₂.widenings p h)
  vectorOps fmt h := vectorOps_agree (h₁.vectorOps fmt h) (h₂.vectorOps fmt h)
  decode rm frm := decode_unique ((h₁.decode rm frm).trans (h₂.decode rm frm).symm)
  toFflags f := fflagsOf_unique (h₁.toFflags f) (h₂.toFflags f)

theorem sumTreeResultOf_transport {sp₁ sp₂ : Specialization}
    (hadd : ∀ fa fb dst rm a b r, AdditionSpecOf sp₂ fa fb dst rm a b r → AdditionSpecOf sp₁ fa fb dst rm a b r)
    {acc : Format} {rm : RoundingDirection} :
    ∀ (t : SumTree) (v : Format × Nat × StatusFlags), SumTreeResultOf sp₂ acc rm t v → SumTreeResultOf sp₁ acc rm t v
  | .leaf _ _, _, h => h
  | .node _ l t, _, ⟨hw, a, b, s, hl, ht, hs, hr⟩ =>
    ⟨hw, a, b, s, sumTreeResultOf_transport hadd l a hl, sumTreeResultOf_transport hadd t b ht,
      hadd _ _ _ _ _ _ _ hs, hr⟩
  | .identity _ t, _, ⟨hw, a, s, ht, hs, hr⟩ =>
    ⟨hw, a, s, sumTreeResultOf_transport hadd t a ht, hadd _ _ _ _ _ _ _ hs, hr⟩

theorem unorderedSumOf_transport {sp₁ sp₂ : Specialization}
    (hadd : ∀ fa fb dst rm a b r, AdditionSpecOf sp₂ fa fb dst rm a b r → AdditionSpecOf sp₁ fa fb dst rm a b r)
    (hconv : ∀ src dst rm a r, ConvertFormatSpecOf sp₂ src dst rm a r → ConvertFormatSpecOf sp₁ src dst rm a r)
    {acc elem : Format} {rm : RoundingDirection} {inactive init : Nat} {xs : List Nat} {r : Nat × StatusFlags}
    (h : UnorderedSumOf sp₂ acc elem rm inactive init xs r) : UnorderedSumOf sp₁ acc elem rm inactive init xs r := by
  obtain ⟨t, hp, hc, v, hv, c, hcv, hr⟩ := h
  refine ⟨t, hp, hc, v, sumTreeResultOf_transport hadd t v hv, c, ?_, ?_⟩
  · rcases hcv with ⟨hl, d, hd, hc'⟩ | hcv
    · exact Or.inl ⟨hl, d, hconv _ _ _ _ _ hd, hc'⟩
    · exact Or.inr hcv
  · rcases hr with hr | ⟨s, hs, hr⟩
    · exact Or.inl hr
    · exact Or.inr ⟨s, hadd _ _ _ _ _ _ _ hs, hr⟩

theorem riscvCorrect_of_riscvChoices {sp₁ sp₂ : Specialization} {o : RiscvOps}
    (c₁ : RiscvChoices sp₁) (c₂ : RiscvChoices sp₂) (h : RiscvCorrect sp₂ o) : RiscvCorrect sp₁ o := by
  have hp : sp₁.propagateNaN = sp₂.propagateNaN := by
    funext op dst xs; rw [c₁.propagateNaN, c₂.propagateNaN]
  have hf := c₁.fusedMultiplyAddZeroInfinityQuietNaNInvalid.trans
    c₂.fusedMultiplyAddZeroInfinityQuietNaNInvalid.symm
  have ht := c₁.tininess.trans c₂.tininess.symm
  have hi : sp₁.intOutOfRange = sp₂.intOutOfRange := by
    funext src rm e s w x; rw [c₁.intOutOfRange, c₂.intOutOfRange]
  obtain ⟨p₁, s₁, f₁, t₁, i₁, o₁, a₁, m₁, b₁⟩ := sp₁
  obtain ⟨p₂, s₂, f₂, t₂, i₂, o₂, a₂, m₂, b₂⟩ := sp₂
  dsimp only at hp hf ht hi
  subst hp hf ht hi
  exact
    { instructions := fun fmt hm => { h.instructions fmt hm with }
      conversions := fun p hm => { h.conversions p hm with }
      widenings := fun p hm => { h.widenings p hm with }
      vectorOps := fun fmt hm => { h.vectorOps fmt hm with }
      decode := h.decode
      F16 := { h.F16 with }
      F32 := { h.F32 with }
      F64 := { h.F64 with }
      F128 := { h.F128 with }
      toFflags := h.toFflags
      roundingModeMeaning := h.roundingModeMeaning
      unorderedSum := fun fmt hm m i init xs => by
        refine unorderedSumOf_transport ?_ ?_ (h.unorderedSum fmt hm m i init xs)
        exacts [fun _ _ _ _ _ _ _ h => h, fun _ _ _ _ _ h => h]
      wideningUnorderedSum := fun p hm hv m i init xs => by
        refine unorderedSumOf_transport ?_ ?_ (h.wideningUnorderedSum p hm hv m i init xs)
        exacts [fun _ _ _ _ _ _ _ h => h, fun _ _ _ _ _ h => h]
      minMaxReductionOrderIndependent := h.minMaxReductionOrderIndependent
      narrowingInHalvingSteps := h.narrowingInHalvingSteps }

theorem riscv_agree_of_choices {sp₁ sp₂ : Specialization} {o₁ o₂ : RiscvOps} (c₁ : RiscvChoices sp₁)
    (c₂ : RiscvChoices sp₂) (h₁ : RiscvCorrect sp₁ o₁) (h₂ : RiscvCorrect sp₂ o₂) : RiscvAgree o₁ o₂ :=
  riscv_agree h₁ (riscvCorrect_of_riscvChoices c₁ c₂ h₂)

end SoftFloat.RISCV.Proof
