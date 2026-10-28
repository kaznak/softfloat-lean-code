/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Operators
import SoftFloat.Core.Proof.Order

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Format SoftFloat.Spec

theorem magnitude_eq_compare_magE (fa fb : Format) (a b : Nat) :
    (if fa.isInfU (fa.unpack a) && fb.isInfU (fb.unpack b) then Ordering.eq
      else if fa.isInfU (fa.unpack a) then .gt
      else if fb.isInfU (fb.unpack b) then .lt
      else Ord.compare
        (fa.sigOf (fa.unpack a) <<<
          (fa.ulpExpOf (fa.unpack a) - Min.min (fa.ulpExpOf (fa.unpack a)) (fb.ulpExpOf (fb.unpack b))).toNat)
        (fb.sigOf (fb.unpack b) <<<
          (fb.ulpExpOf (fb.unpack b) - Min.min (fa.ulpExpOf (fa.unpack a)) (fb.ulpExpOf (fb.unpack b))).toNat))
      = compare (magE fa a) (magE fb b) := by
  cases hia : fa.isInfU (fa.unpack a) <;> cases hib : fb.isInfU (fb.unpack b)
  · simp only [Bool.and_self, Bool.false_eq_true, ↓reduceIte]
    rw [compare_shiftLeft_eq, magE_of_not_isInfU fa hia, magE_of_not_isInfU fb hib]
    exact compare_eq_compare_of_lt_iff EReal.coe_lt_coe_iff.symm EReal.coe_lt_coe_iff.symm
  · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [magE_of_not_isInfU fa hia, magE_of_isInfU fb hib]
    exact (compare_lt_iff_lt.mpr (EReal.coe_lt_top _)).symm
  · simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    rw [magE_of_isInfU fa hia, magE_of_not_isInfU fb hib]
    exact (compare_gt_iff_gt.mpr (EReal.coe_lt_top _)).symm
  · simp only [Bool.and_self, ↓reduceIte]
    rw [magE_of_isInfU fa hia, magE_of_isInfU fb hib]
    exact (compare_eq_iff_eq.mpr rfl).symm

theorem relation_tail_eq (X Y : EReal) (nA nB : Bool) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hXp : nA = true → 0 < X) (hYp : nB = true → 0 < Y) :
    (if nA != nB then (if nA then Relation.lessThan else .greaterThan)
      else
        match (if nA then (compare X Y).swap else compare X Y) with
        | .lt => .lessThan
        | .eq => .equal
        | .gt => .greaterThan)
      = (if (if nA then -X else X) < (if nB then -Y else Y) then Relation.lessThan
        else if (if nA then -X else X) = (if nB then -Y else Y) then .equal
        else .greaterThan) := by
  have hX0 : -X ≤ 0 := by simpa using EReal.neg_le_neg_iff.mpr hX
  have hY0 : -Y ≤ 0 := by simpa using EReal.neg_le_neg_iff.mpr hY
  cases nA <;> cases nB
  · rcases lt_trichotomy X Y with h | rfl | h
    · simp [compare_lt_iff_lt.mpr h, h]
    · simp
    · simp [compare_gt_iff_gt.mpr h, not_lt.mpr h.le, h.ne']
  · have hYp' := hYp rfl
    have h1 : -Y < X := lt_of_lt_of_le (by simpa using EReal.neg_lt_neg_iff.mpr hYp') hX
    simp [not_lt.mpr h1.le, h1.ne']
  · have hXp' := hXp rfl
    have h1 : -X < Y := lt_of_lt_of_le (by simpa using EReal.neg_lt_neg_iff.mpr hXp') hY
    simp [h1]
  · rcases lt_trichotomy X Y with h | rfl | h
    · have h' : ¬ -X < -Y := by rw [EReal.neg_lt_neg_iff]; exact not_lt.mpr h.le
      have h'' : -X ≠ -Y := fun e => h.ne (neg_inj.mp e)
      simp [compare_lt_iff_lt.mpr h, h', h'']
    · simp
    · have h' : -X < -Y := EReal.neg_lt_neg_iff.mpr h
      simp [compare_gt_iff_gt.mpr h, h']

theorem relation_eq_relationOf (fa fb : Format) (a b : Nat) :
    Format.relation fa fb a b = relationOf fa fb a b := by
  unfold Format.relation relationOf
  dsimp only
  rw [isNaNU_unpack, isNaNU_unpack]
  by_cases hn : (isNaN fa a || isNaN fb b) = true
  · simp only [hn, ↓reduceIte]
  · have hna : isNaN fa a = false := by simp_all
    have hnb : isNaN fb b = false := by simp_all
    simp only [hn, Bool.false_eq_true, ↓reduceIte]
    rw [magnitude_eq_compare_magE fa fb a b]
    by_cases hz : (isZeroU (fa.unpack a) && isZeroU (fb.unpack b)) = true
    · simp only [Bool.and_eq_true] at hz
      simp [hz, valE_of_isZeroU fa hz.1, valE_of_isZeroU fb hz.2]
    · have hz' : (isZeroU (fa.unpack a) && isZeroU (fb.unpack b)) = false := by simpa using hz
      simp only [hz', Bool.false_eq_true, ↓reduceIte]
      rw [valE_eq_magE_of_nonzero fa hna, valE_eq_magE_of_nonzero fb hnb]
      apply relation_tail_eq _ _ _ _ (magE_nonneg fa a) (magE_nonneg fb b)
      · intro h; simp only [Bool.and_eq_true, Bool.not_eq_true'] at h; exact magE_pos fa h.2
      · intro h; simp only [Bool.and_eq_true, Bool.not_eq_true'] at h; exact magE_pos fb h.2

theorem relationOf_eq_unordered_iff (fa fb : Format) (a b : Nat) :
    relationOf fa fb a b = .unordered ↔ (isNaN fa a || isNaN fb b) = true := by
  unfold relationOf
  split_ifs with h1 h2 h3 <;> simp_all

theorem comparisonSpecOf_comparison (fa fb : Format) (signaling : Bool)
    (holds : Relation → Bool) (a b : Nat) :
    ComparisonSpecOf fa fb signaling holds a b (Format.comparison fa fb signaling holds a b) := by
  unfold ComparisonSpecOf Format.comparison
  dsimp only
  rw [relation_eq_relationOf, isSNaNU_unpack, isSNaNU_unpack]
  refine ⟨rfl, ?_⟩
  have hu : (relationOf fa fb a b == .unordered) = (isNaN fa a || isNaN fb b) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, relationOf_eq_unordered_iff]
  rw [hu]
  have hsa : isSignalingNaN fa a = true → isNaN fa a = true := isSignalingNaN_imp_isNaN fa
  have hsb : isSignalingNaN fb b = true → isNaN fb b = true := isSignalingNaN_imp_isNaN fb
  congr 1
  cases signaling <;> cases h1 : isSignalingNaN fa a <;> cases h2 : isSignalingNaN fb b <;>
    cases h3 : isNaN fa a <;> cases h4 : isNaN fb b <;> simp_all

theorem softfloat_comparison (sp : Specialization) :
    ∀ fa fb signaling holds a b,
      ComparisonSpecOf fa fb signaling holds a b ((softfloat sp).comparison fa fb signaling holds a b) :=
  comparisonSpecOf_comparison

theorem comparisonSpecOf_unique {fa fb : Format} {signaling : Bool} {holds : Relation → Bool}
    {a b : Nat} {r₁ r₂ : Bool × StatusFlags}
    (h₁ : ComparisonSpecOf fa fb signaling holds a b r₁)
    (h₂ : ComparisonSpecOf fa fb signaling holds a b r₂) : r₁ = r₂ :=
  Prod.ext (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)

end SoftFloat.Proof
