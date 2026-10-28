/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Proof.Encoding
import SoftFloat.Core.Proof.Common
import SoftFloat.Core.Proof.Remainder
import SoftFloat.Core.Proof.RoundToIntegral
import SoftFloat.RISCV.Spec.V
import SoftFloat.RISCV.Operators.Riscv
import SoftFloat.RISCV.Proof.Specialization
import SoftFloat.RISCV.Proof.ZfaGeneric

namespace SoftFloat.RISCV.Proof

open SoftFloat SoftFloat.Format SoftFloat.Spec SoftFloat.Proof SoftFloat.RISCV.Spec

theorem relationOf_swap_lessThan (fmt : Format) (a b : Nat) :
    (relationOf fmt fmt b a == .lessThan) = (relationOf fmt fmt a b == .greaterThan) := by
  unfold relationOf
  rw [Bool.or_comm (isNaN fmt b)]
  by_cases hn : (isNaN fmt a || isNaN fmt b) = true
  · simp +decide [hn]
  · simp only [hn, Bool.false_eq_true, ↓reduceIte]
    rcases lt_trichotomy (valE fmt a) (valE fmt b) with h | h | h
    · simp +decide [h, not_lt.mpr h.le, h.ne']
    · simp +decide [h]
    · simp +decide [h, not_lt.mpr h.le, h.ne']

theorem relationOf_swap_lessEqual (fmt : Format) (a b : Nat) :
    (relationOf fmt fmt b a == .lessThan || relationOf fmt fmt b a == .equal)
      = (relationOf fmt fmt a b == .greaterThan || relationOf fmt fmt a b == .equal) := by
  unfold relationOf
  rw [Bool.or_comm (isNaN fmt b)]
  by_cases hn : (isNaN fmt a || isNaN fmt b) = true
  · simp +decide [hn]
  · simp only [hn, Bool.false_eq_true, ↓reduceIte]
    rcases lt_trichotomy (valE fmt a) (valE fmt b) with h | h | h
    · simp +decide [h, not_lt.mpr h.le, h.ne']
    · simp +decide [h]
    · simp +decide [h, not_lt.mpr h.le, h.ne']

theorem comparison_greater_of_less {fmt : Format} {a b : Nat} {r : Bool × StatusFlags}
    (h : ComparisonSpecOf fmt fmt true (· == .lessThan) b a r) :
    ComparisonSpecOf fmt fmt true (· == .greaterThan) a b r := by
  unfold ComparisonSpecOf at *
  refine ⟨h.1.trans (relationOf_swap_lessThan fmt a b), ?_⟩
  rw [h.2]; simp [Bool.or_comm]

theorem comparison_greaterEqual_of_lessEqual {fmt : Format} {a b : Nat} {r : Bool × StatusFlags}
    (h : ComparisonSpecOf fmt fmt true (fun r => r == .lessThan || r == .equal) b a r) :
    ComparisonSpecOf fmt fmt true (fun r => r == .greaterThan || r == .equal) a b r := by
  unfold ComparisonSpecOf at *
  refine ⟨h.1.trans (relationOf_swap_lessEqual fmt a b), ?_⟩
  rw [h.2]; simp [Bool.or_comm]

theorem union_empty (f : StatusFlags) : f.union {} = f := by
  cases f; simp [StatusFlags.union]

theorem empty_union (f : StatusFlags) : ({} : StatusFlags).union f = f := by
  cases f; simp [StatusFlags.union]

theorem union_assoc (a b c : StatusFlags) : (a.union b).union c = a.union (b.union c) := by
  cases a; cases b; cases c; simp [StatusFlags.union, Bool.or_assoc]

theorem reduceWithFlags_ordered {wa wb : Nat} {P : Nat → Nat → Nat × StatusFlags → Prop}
    (step : BitVec wa → BitVec wb → BitVec wa × StatusFlags)
    (h : ∀ a x, P a.toNat x.toNat (bitsResult (step a x))) :
    ∀ (init : BitVec wa) (xs : List (BitVec wb)),
      OrderedReductionOf P init.toNat (xs.map (·.toNat)) (bitsResult (reduceWithFlags step init xs))
  | _, [] => rfl
  | init, x :: xs => ⟨_, _, h init x, reduceWithFlags_ordered step h (step init x).1 xs, rfl⟩

theorem reduceWithFlags_last {wa wb : Nat} (step : BitVec wa → BitVec wb → BitVec wa × StatusFlags) :
    ∀ (init : BitVec wa) (x : BitVec wb) (xs : List (BitVec wb)),
      ∃ a y, (reduceWithFlags step init (x :: xs)).1 = (step a y).1
  | init, x, [] => ⟨init, x, rfl⟩
  | init, x, y :: xs => reduceWithFlags_last step (step init x).1 y xs

theorem roundR_valR (fmt : Format) (rm : RoundingDirection) {x : Nat} (hf : IsFinite fmt x) :
    roundR fmt rm (valR fmt x) = valR fmt x := by
  by_cases hz : isZeroU (fmt.unpack x) = true
  · rw [valR_eq_zero_of_isZeroU fmt hz, roundR_zero]
  · rw [valR_eq_sigOf fmt hf]
    exact roundR_signed_exact fmt rm _ (sigOf_pos fmt (by simpa using hz))
      (sigOf_lt_two_pow_sigBits fmt _ (unpack_fracField_lt fmt x)) (minQ_le_ulpExpOf fmt _)

theorem roundedResultOf_self (sp : Specialization) (fmt : Format) (rm : RoundingDirection) {x : Nat} {s : Bool}
    (hx : fmt.IsEncoding x)
    (hc : classify fmt x = .normal s ∨ classify fmt x = .subnormal s ∨ classify fmt x = .zero s) :
    RoundedResultOf sp fmt rm (valR fmt x) s (x, {}) := by
  have hf : IsFinite fmt x := by
    unfold IsFinite; rcases hc with h | h | h <;> rw [h] <;> trivial
  have hR := roundR_valR fmt rm hf
  unfold RoundedResultOf
  rw [hR]
  simp only [not_lt.mpr (abs_valR_le_maxFinite fmt hf), ↓reduceIte]
  refine ⟨hx, trivial, trivial, hf, trivial, fun h0 => ?_, trivial, by simp, by simp⟩
  simp only [h0, ↓reduceIte]
  rcases (valR_eq_zero_iff fmt x).1 h0 with h | ⟨t, ht⟩
  · exact absurd hf h
  · rcases hc with h | h | h <;> rw [h] at ht ⊢ <;> simp_all

theorem addition_nan_canonical {fa fb dst : Format} {rm : RoundingDirection} {a b : Nat} {s : Nat × StatusFlags}
    (h : AdditionSpecOf Specialization.riscv fa fb dst rm a b s) (hn : isNaN dst s.1 = true) :
    s.1 = dst.canonicalNaN := by
  have hnf : ¬ IsFinite dst s.1 := fun hf =>
    absurd hn (by rw [((isFinite_iff_not_isNaN_not_isInf dst s.1).1 hf).1]; decide)
  have hni : ∀ t, classify dst s.1 ≠ .infinity t := fun t ht =>
    absurd hn (by unfold isNaN; rw [ht]; simp)
  unfold AdditionSpecOf arithSumOf at h
  obtain ⟨_, h⟩ := h
  split_ifs at h
  · exact h.1
  · exact h.1
  · exact absurd h.1 (hni _)
  · exact absurd h.1 (hni _)
  · unfold RoundedResultOf at h
    obtain ⟨_, _, _, h⟩ := h
    split_ifs at h <;>
      first
      | exact absurd h.1 (hni _)
      | exact absurd h.1.1 hnf
      | exact absurd h.1 hnf

theorem convertFormat_self_of_addition {fa fb dst : Format} {rm rm' : RoundingDirection} {a b : Nat}
    {s : Nat × StatusFlags} (h : AdditionSpecOf Specialization.riscv fa fb dst rm a b s) :
    ConvertFormatSpecOf Specialization.riscv dst dst rm' s.1 (s.1, {}) := by
  have hE : dst.IsEncoding s.1 := h.1
  unfold ConvertFormatSpecOf
  cases hc : classify dst s.1 with
  | quietNaN =>
    have := addition_nan_canonical h (by unfold isNaN; rw [hc])
    refine ⟨this, ?_⟩
    simp [isSignalingNaN, hc]
  | signalingNaN =>
    have := addition_nan_canonical h (by unfold isNaN; rw [hc])
    rw [this, classify_canonicalNaN] at hc
    exact absurd hc (by decide)
  | infinity t => exact ⟨hE, hc, rfl⟩
  | normal t => exact roundedResultOf_self _ dst rm' hE (Or.inl hc)
  | subnormal t => exact roundedResultOf_self _ dst rm' hE (Or.inr (Or.inl hc))
  | zero t => exact roundedResultOf_self _ dst rm' hE (Or.inr (Or.inr hc))

def combTree (acc elem : Format) : SumTree → List Nat → SumTree
  | t, [] => t
  | t, x :: xs => combTree acc elem (.node acc t (.leaf elem x)) xs

theorem combTree_leaves (acc elem : Format) :
    ∀ (t : SumTree) (xs : List Nat), (combTree acc elem t xs).leaves = t.leaves ++ xs.map (elem, ·)
  | t, [] => by simp [combTree]
  | t, x :: xs => by
    rw [combTree, combTree_leaves acc elem _ xs]
    simp [SumTree.leaves]

theorem combTree_node_isLeaf (acc elem : Format) :
    ∀ (l r : SumTree) (xs : List Nat), (combTree acc elem (.node acc l r) xs).isLeaf = false
  | _, _, [] => rfl
  | _, _, _ :: xs => combTree_node_isLeaf acc elem _ _ xs

theorem combTree_result {acc elem : Format} {sp : Specialization} {rm : RoundingDirection}
    (step : BitVec acc.width → BitVec elem.width → BitVec acc.width × StatusFlags)
    (h : ∀ a x, AdditionSpecOf sp acc elem acc rm a.toNat x.toNat (bitsResult (step a x))) :
    ∀ (xs : List (BitVec elem.width)) (t : SumTree) (a : BitVec acc.width) (F : StatusFlags),
      SumTreeResultOf sp acc rm t (acc, a.toNat, F) →
      SumTreeResultOf sp acc rm (combTree acc elem t (xs.map (·.toNat)))
        (acc, (reduceWithFlags step a xs).1.toNat, F.union (reduceWithFlags step a xs).2)
  | [], t, a, F, ht => by simpa [combTree, reduceWithFlags, union_empty] using ht
  | x :: xs, t, a, F, ht => by
    have hn : SumTreeResultOf sp acc rm (.node acc t (.leaf elem x.toNat))
        (acc, (step a x).1.toNat, (F.union {}).union (step a x).2) :=
      ⟨⟨le_rfl, le_rfl⟩, _, _, _, ht, rfl, h a x, rfl⟩
    have := combTree_result step h xs _ (step a x).1 _ hn
    simpa [combTree, reduceWithFlags, union_assoc, union_empty] using this

theorem combTree_identityCount (acc elem : Format) :
    ∀ (t : SumTree) (xs : List Nat), (combTree acc elem t xs).identityCount = t.identityCount
  | t, [] => rfl
  | t, x :: xs => by
    rw [combTree, combTree_identityCount acc elem _ xs]
    simp [SumTree.identityCount]

theorem reduceWithFlags_unordered {acc elem : Format} {rm : RoundingDirection}
    (step : BitVec acc.width → BitVec elem.width → BitVec acc.width × StatusFlags)
    (h : ∀ a x, AdditionSpecOf Specialization.riscv acc elem acc rm a.toNat x.toNat (bitsResult (step a x)))
    (inactive : Nat) (init : BitVec acc.width) (xs : List (BitVec elem.width)) :
    UnorderedSumOf Specialization.riscv acc elem rm inactive init.toNat (xs.map (·.toNat))
      (bitsResult (reduceWithFlags step init xs)) := by
  cases xs with
  | nil =>
    exact ⟨.leaf acc init.toNat, by simp [SumTree.leaves], by simp [SumTree.identityCount], _, rfl, _,
      Or.inr ⟨rfl, rfl⟩, Or.inl rfl⟩
  | cons x xs =>
    have hr := combTree_result step h (x :: xs) (.leaf acc init.toNat) init {} rfl
    obtain ⟨a, y, hl⟩ := reduceWithFlags_last step init x xs
    have hc := convertFormat_self_of_addition (rm' := rm) (h a y)
    have hn : (combTree acc elem (.leaf acc init.toNat) ((x :: xs).map (·.toNat))).isLeaf = false := by
      rw [List.map_cons, combTree, combTree_node_isLeaf]
    refine ⟨combTree acc elem (.leaf acc init.toNat) ((x :: xs).map (·.toNat)), ?_, ?_, _, hr, ?_⟩
    · rw [combTree_leaves]; simp [SumTree.leaves]
    · rw [combTree_identityCount]; simp [SumTree.identityCount]
    · refine ⟨_, Or.inl ⟨Or.inl (by simp only [List.map_cons] at hn; simp [hn]), ?_⟩, Or.inl rfl⟩
      refine ⟨(((reduceWithFlags step init (x :: xs)).1).toNat, {}), ?_, ?_⟩
      · simpa [bitsResult, hl] using hc
      · simp [bitsResult, union_empty, empty_union]

def selLt (pickLess : Bool) (fmt : Format) (a b : Nat) : Prop :=
  if pickLess then minMaxLt fmt a b else minMaxLt fmt b a

theorem valE_eq_zero_of_classify_zero (fmt : Format) {a : Nat} {s : Bool} (h : classify fmt a = .zero s) :
    valE fmt a = 0 :=
  valE_of_isZeroU fmt ((classify_eq_zero_iff fmt a s).1 h).1

theorem minMaxLt_irrefl (fmt : Format) (a : Nat) : ¬ minMaxLt fmt a a := by
  rintro (h | ⟨h1, h2⟩)
  · exact lt_irrefl _ h
  · rw [h1] at h2; cases h2

theorem minMaxLt_trans (fmt : Format) {a b c : Nat} (h1 : minMaxLt fmt a b) (h2 : minMaxLt fmt b c) :
    minMaxLt fmt a c := by
  rcases h1 with h1 | ⟨ha, hb⟩ <;> rcases h2 with h2 | ⟨hb', hc⟩
  · exact Or.inl (lt_trans h1 h2)
  · left; rw [valE_eq_zero_of_classify_zero fmt hc, ← valE_eq_zero_of_classify_zero fmt hb']; exact h1
  · left; rw [valE_eq_zero_of_classify_zero fmt ha, ← valE_eq_zero_of_classify_zero fmt hb]; exact h2
  · rw [hb] at hb'; cases hb'

theorem minMaxLt_total (fmt : Format) {a b : Nat} (ha : a < 2 ^ fmt.width) (hb : b < 2 ^ fmt.width)
    (hna : isNaN fmt a = false) (hnb : isNaN fmt b = false) :
    minMaxLt fmt a b ∨ a = b ∨ minMaxLt fmt b a := by
  rcases lt_trichotomy (valE fmt a) (valE fmt b) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases eq_or_zero_ne_of_valE_eq fmt ha hb hna hnb h with h | ⟨s, hs, ht⟩
    · exact Or.inr (Or.inl h)
    · cases s
      · exact Or.inr (Or.inr (Or.inr ⟨ht, hs⟩))
      · exact Or.inl (Or.inr ⟨hs, ht⟩)
  · exact Or.inr (Or.inr (Or.inl h))

theorem selLt_irrefl (pickLess : Bool) (fmt : Format) (a : Nat) : ¬ selLt pickLess fmt a a := by
  cases pickLess <;> exact minMaxLt_irrefl fmt a

theorem selLt_trans {pickLess : Bool} {fmt : Format} {a b c : Nat} (h1 : selLt pickLess fmt a b)
    (h2 : selLt pickLess fmt b c) : selLt pickLess fmt a c := by
  cases pickLess
  · exact minMaxLt_trans fmt h2 h1
  · exact minMaxLt_trans fmt h1 h2

theorem selLt_total (pickLess : Bool) (fmt : Format) {a b : Nat} (ha : a < 2 ^ fmt.width)
    (hb : b < 2 ^ fmt.width) (hna : isNaN fmt a = false) (hnb : isNaN fmt b = false) :
    selLt pickLess fmt a b ∨ a = b ∨ selLt pickLess fmt b a := by
  rcases minMaxLt_total fmt ha hb hna hnb with h | h | h
  · cases pickLess
    · exact Or.inr (Or.inr h)
    · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · cases pickLess
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

theorem union_invalid (x y : Bool) :
    ({ invalidOperation := x } : StatusFlags).union { invalidOperation := y } = { invalidOperation := x || y } :=
  rfl

theorem minMaxNumber_cases {op : NaNOperation} {pickLess : Bool} {fmt : Format} {a b : Nat} {r : Nat × StatusFlags}
    (h : MinMaxNumberSpecOf Specialization.riscv op pickLess fmt a b r) :
    (isNaN fmt a = true ∧ isNaN fmt b = true ∧
        r = (fmt.canonicalNaN, { invalidOperation := isSignalingNaN fmt a || isSignalingNaN fmt b }))
      ∨ (isNaN fmt a = true ∧ isNaN fmt b = false ∧ r = (b, { invalidOperation := isSignalingNaN fmt a }))
      ∨ (isNaN fmt a = false ∧ isNaN fmt b = true ∧ r = (a, { invalidOperation := isSignalingNaN fmt b }))
      ∨ (isNaN fmt a = false ∧ isNaN fmt b = false ∧ r.2 = { invalidOperation := false }
          ∧ (r.1 = a ∨ r.1 = b) ∧ (selLt pickLess fmt a b → r.1 = a) ∧ (selLt pickLess fmt b a → r.1 = b)) := by
  obtain ⟨_, h⟩ := h
  cases ha : isNaN fmt a <;> cases hb : isNaN fmt b <;> simp only [ha, hb, Bool.and_self, Bool.and_false,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte] at h
  · obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
    refine Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h4, h1, fun hl => ?_, fun hl => ?_⟩))
    · cases pickLess
      · simpa using h3 hl
      · simpa using h2 hl
    · cases pickLess
      · simpa using h2 hl
      · simpa using h3 hl
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, Prod.ext h.1 h.2⟩))
  · exact Or.inr (Or.inl ⟨rfl, rfl, Prod.ext h.1 h.2⟩)
  · exact Or.inl ⟨rfl, rfl, Prod.ext h.1 h.2⟩

def MinMaxTreeInvariant (pickLess : Bool) (fmt : Format) (L : List Nat) (v : Nat × StatusFlags) : Prop :=
  (∃ b : Bool, v.2 = { invalidOperation := b }
      ∧ ((b = true ∨ isSignalingNaN fmt v.1 = true) ↔ ∃ y ∈ L, isSignalingNaN fmt y = true))
    ∧ (isNaN fmt v.1 = true ↔ ∀ y ∈ L, isNaN fmt y = true)
    ∧ (isNaN fmt v.1 = false → v.1 ∈ L ∧ ∀ y ∈ L, isNaN fmt y = false → ¬ selLt pickLess fmt y v.1)

theorem minMaxTree_invariant (op : NaNOperation) (pickLess : Bool) (fmt : Format) :
    ∀ (t : ReductionTree) (v : Nat × StatusFlags), (∀ y ∈ t.leaves, y < 2 ^ fmt.width) →
      ReductionTreeResultOf (MinMaxNumberSpecOf Specialization.riscv op pickLess fmt) t v →
      MinMaxTreeInvariant pickLess fmt t.leaves v
  | .leaf x, v, _, hv => by
    subst hv
    refine ⟨⟨false, rfl, by simp [ReductionTree.leaves]⟩, by simp [ReductionTree.leaves],
      fun _ => ⟨by simp [ReductionTree.leaves], ?_⟩⟩
    intro y hy _
    rw [List.mem_singleton.1 hy]; exact selLt_irrefl pickLess fmt x
  | .node l r, v, hL, hv => by
    obtain ⟨a, b, s, hl, hr, hs, rfl⟩ := hv
    have hLl : ∀ y ∈ l.leaves, y < 2 ^ fmt.width := fun y hy => hL y (List.mem_append_left _ hy)
    have hLr : ∀ y ∈ r.leaves, y < 2 ^ fmt.width := fun y hy => hL y (List.mem_append_right _ hy)
    obtain ⟨⟨ba, hba, hfa⟩, hna, hma⟩ := minMaxTree_invariant op pickLess fmt l a hLl hl
    obtain ⟨⟨bb, hbb, hfb⟩, hnb, hmb⟩ := minMaxTree_invariant op pickLess fmt r b hLr hr
    show MinMaxTreeInvariant pickLess fmt (l.leaves ++ r.leaves) _
    unfold MinMaxTreeInvariant
    simp only [List.mem_append]
    rcases minMaxNumber_cases hs with ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
    · -- 2 つの入力がどちらも NaN
      have hal := hna.1 h1
      have hbl := hnb.1 h2
      refine ⟨⟨ba || bb || (isSignalingNaN fmt a.1 || isSignalingNaN fmt b.1), ?_, ?_⟩, ?_, ?_⟩
      · simp only [hba, hbb, union_invalid]
      · simp only [isSignalingNaN_canonicalNaN, Bool.or_eq_true]
        constructor
        · rintro (((h | h) | (h | h)) | h)
          · obtain ⟨y, hy, h⟩ := hfa.1 (Or.inl h); exact ⟨y, Or.inl hy, h⟩
          · obtain ⟨y, hy, h⟩ := hfb.1 (Or.inl h); exact ⟨y, Or.inr hy, h⟩
          · obtain ⟨y, hy, h⟩ := hfa.1 (Or.inr h); exact ⟨y, Or.inl hy, h⟩
          · obtain ⟨y, hy, h⟩ := hfb.1 (Or.inr h); exact ⟨y, Or.inr hy, h⟩
          · cases h
        · rintro ⟨y, hy | hy, h⟩
          · rcases hfa.2 ⟨y, hy, h⟩ with h | h
            · exact Or.inl (Or.inl (Or.inl h))
            · exact Or.inl (Or.inr (Or.inl h))
          · rcases hfb.2 ⟨y, hy, h⟩ with h | h
            · exact Or.inl (Or.inl (Or.inr h))
            · exact Or.inl (Or.inr (Or.inr h))
      · simp only [isNaN_canonicalNaN, true_iff]
        rintro y (hy | hy)
        · exact hal y hy
        · exact hbl y hy
      · intro h; rw [isNaN_canonicalNaN] at h; cases h
    · -- 第 1 の入力だけが NaN
      have hal := hna.1 h1
      obtain ⟨hbm, hbmin⟩ := hmb h2
      have hsb := isSignalingNaN_eq_false_of_isNaN fmt h2
      refine ⟨⟨ba || bb || isSignalingNaN fmt a.1, ?_, ?_⟩, ?_, fun _ => ⟨Or.inr hbm, ?_⟩⟩
      · simp only [hba, hbb, union_invalid]
      · simp only [hsb, Bool.or_eq_true, Bool.false_eq_true, or_false]
        constructor
        · rintro ((h | h) | h)
          · obtain ⟨y, hy, h⟩ := hfa.1 (Or.inl h); exact ⟨y, Or.inl hy, h⟩
          · obtain ⟨y, hy, h⟩ := hfb.1 (Or.inl h); exact ⟨y, Or.inr hy, h⟩
          · obtain ⟨y, hy, h⟩ := hfa.1 (Or.inr h); exact ⟨y, Or.inl hy, h⟩
        · rintro ⟨y, hy | hy, h⟩
          · rcases hfa.2 ⟨y, hy, h⟩ with h | h
            · exact Or.inl (Or.inl h)
            · exact Or.inr h
          · rcases hfb.2 ⟨y, hy, h⟩ with h | h
            · exact Or.inl (Or.inr h)
            · rw [hsb] at h; cases h
      · simp only [h2, Bool.false_eq_true, false_iff, not_forall]
        refine ⟨b.1, Or.inr hbm, ?_⟩
        rw [h2]; simp
      · rintro y (hy | hy) hy'
        · rw [hal y hy] at hy'; cases hy'
        · exact hbmin y hy hy'
    · -- 第 2 の入力だけが NaN
      have hbl := hnb.1 h2
      obtain ⟨ham, hamin⟩ := hma h1
      have hsa := isSignalingNaN_eq_false_of_isNaN fmt h1
      refine ⟨⟨ba || bb || isSignalingNaN fmt b.1, ?_, ?_⟩, ?_, fun _ => ⟨Or.inl ham, ?_⟩⟩
      · simp only [hba, hbb, union_invalid]
      · simp only [hsa, Bool.or_eq_true, Bool.false_eq_true, or_false]
        constructor
        · rintro ((h | h) | h)
          · obtain ⟨y, hy, h⟩ := hfa.1 (Or.inl h); exact ⟨y, Or.inl hy, h⟩
          · obtain ⟨y, hy, h⟩ := hfb.1 (Or.inl h); exact ⟨y, Or.inr hy, h⟩
          · obtain ⟨y, hy, h⟩ := hfb.1 (Or.inr h); exact ⟨y, Or.inr hy, h⟩
        · rintro ⟨y, hy | hy, h⟩
          · rcases hfa.2 ⟨y, hy, h⟩ with h | h
            · exact Or.inl (Or.inl h)
            · rw [hsa] at h; cases h
          · rcases hfb.2 ⟨y, hy, h⟩ with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr h
      · simp only [h1, Bool.false_eq_true, false_iff, not_forall]
        refine ⟨a.1, Or.inl ham, ?_⟩
        rw [h1]; simp
      · rintro y (hy | hy) hy'
        · exact hamin y hy hy'
        · rw [hbl y hy] at hy'; cases hy'
    · -- どちらも NaN でない
      obtain ⟨ham, hamin⟩ := hma h1
      obtain ⟨hbm, hbmin⟩ := hmb h2
      have hsa := isSignalingNaN_eq_false_of_isNaN fmt h1
      have hsb := isSignalingNaN_eq_false_of_isNaN fmt h2
      have hns : isNaN fmt s.1 = false := by rcases h4 with h | h <;> rw [h] <;> assumption
      have hss := isSignalingNaN_eq_false_of_isNaN fmt hns
      refine ⟨⟨ba || bb || false, ?_, ?_⟩, ?_, fun _ => ⟨?_, ?_⟩⟩
      · simp only [hba, hbb, h3, union_invalid]
      · simp only [hss, Bool.or_eq_true, Bool.false_eq_true, or_false]
        constructor
        · rintro (h | h)
          · obtain ⟨y, hy, h⟩ := hfa.1 (Or.inl h); exact ⟨y, Or.inl hy, h⟩
          · obtain ⟨y, hy, h⟩ := hfb.1 (Or.inl h); exact ⟨y, Or.inr hy, h⟩
        · rintro ⟨y, hy | hy, h⟩
          · rcases hfa.2 ⟨y, hy, h⟩ with h | h
            · exact Or.inl h
            · rw [hsa] at h; cases h
          · rcases hfb.2 ⟨y, hy, h⟩ with h | h
            · exact Or.inr h
            · rw [hsb] at h; cases h
      · simp only [hns, Bool.false_eq_true, false_iff, not_forall]
        refine ⟨a.1, Or.inl ham, ?_⟩
        rw [h1]; simp
      · rcases h4 with h | h <;> rw [h]
        · exact Or.inl ham
        · exact Or.inr hbm
      · rcases selLt_total pickLess fmt (hLl _ ham) (hLr _ hbm) h1 h2 with hab | hab | hab
        · rw [h5 hab]
          rintro y (hy | hy) hy' hlt
          · exact hamin y hy hy' hlt
          · exact hbmin y hy hy' (selLt_trans hlt hab)
        · have hsa' : s.1 = a.1 := by rcases h4 with h | h <;> rw [h]; exact hab.symm
          rw [hsa']
          rintro y (hy | hy) hy' hlt
          · exact hamin y hy hy' hlt
          · rw [hab] at hlt; exact hbmin y hy hy' hlt
        · rw [h6 hab]
          rintro y (hy | hy) hy' hlt
          · exact hamin y hy hy' (selLt_trans hlt hab)
          · exact hbmin y hy hy' hlt

theorem minMaxTree_node_value {op : NaNOperation} {pickLess : Bool} {fmt : Format} {l r : ReductionTree}
    {v : Nat × StatusFlags}
    (hv : ReductionTreeResultOf (MinMaxNumberSpecOf Specialization.riscv op pickLess fmt) (.node l r) v) :
    v.1 = fmt.canonicalNaN ∨ isNaN fmt v.1 = false := by
  obtain ⟨a, b, s, _, _, hs, rfl⟩ := hv
  rcases minMaxNumber_cases hs with ⟨_, _, rfl⟩ | ⟨_, h2, rfl⟩ | ⟨h1, _, rfl⟩ | ⟨h1, h2, _, h4, _⟩
  · exact Or.inl rfl
  · exact Or.inr h2
  · exact Or.inr h1
  · right; rcases h4 with h | h <;> rw [h] <;> assumption

theorem reductionTree_leaves_ne_nil : ∀ t : ReductionTree, t.leaves ≠ []
  | .leaf _ => by simp [ReductionTree.leaves]
  | .node l _ => by simp [ReductionTree.leaves, reductionTree_leaves_ne_nil l]

theorem reductionTree_eq_leaf_of_perm {t : ReductionTree} {x : Nat} (h : t.leaves.Perm [x]) :
    t = .leaf x := by
  cases t with
  | leaf y => simpa [ReductionTree.leaves] using h
  | node l r =>
    have hlen := h.length_eq
    have h1 := List.length_pos_of_ne_nil (reductionTree_leaves_ne_nil l)
    have h2 := List.length_pos_of_ne_nil (reductionTree_leaves_ne_nil r)
    simp [ReductionTree.leaves] at hlen
    omega

theorem minMaxTree_unique (op : NaNOperation) (pickLess : Bool) (fmt : Format) {t t' : ReductionTree}
    {v v' : Nat × StatusFlags} (hp : t.leaves.Perm t'.leaves) (hL : ∀ y ∈ t.leaves, y < 2 ^ fmt.width)
    (hv : ReductionTreeResultOf (MinMaxNumberSpecOf Specialization.riscv op pickLess fmt) t v)
    (hv' : ReductionTreeResultOf (MinMaxNumberSpecOf Specialization.riscv op pickLess fmt) t' v') : v = v' := by
  have hL' : ∀ y ∈ t'.leaves, y < 2 ^ fmt.width := fun y hy => hL y (hp.mem_iff.2 hy)
  cases t with
  | leaf x =>
    have := reductionTree_eq_leaf_of_perm hp.symm
    subst this
    simp only [ReductionTree.leaves, List.perm_singleton] at hp
    cases hp
    exact hv.trans hv'.symm
  | node l r =>
    cases t' with
    | leaf x => exact absurd (reductionTree_eq_leaf_of_perm hp) (by simp)
    | node l' r' =>
      obtain ⟨⟨b, hb, hf⟩, hn, hm⟩ := minMaxTree_invariant op pickLess fmt _ v hL hv
      obtain ⟨⟨b', hb', hf'⟩, hn', hm'⟩ := minMaxTree_invariant op pickLess fmt _ v' hL' hv'
      have hs : isSignalingNaN fmt v.1 = false := by
        rcases minMaxTree_node_value hv with h | h
        · rw [h]; exact isSignalingNaN_canonicalNaN fmt
        · exact isSignalingNaN_eq_false_of_isNaN fmt h
      have hs' : isSignalingNaN fmt v'.1 = false := by
        rcases minMaxTree_node_value hv' with h | h
        · rw [h]; exact isSignalingNaN_canonicalNaN fmt
        · exact isSignalingNaN_eq_false_of_isNaN fmt h
      have hbb : b = b' := by
        rw [hs, Bool.false_eq_true, or_false] at hf
        rw [hs', Bool.false_eq_true, or_false] at hf'
        apply Bool.eq_iff_iff.2
        rw [hf, hf']
        exact ⟨fun ⟨y, hy, h⟩ => ⟨y, hp.mem_iff.1 hy, h⟩, fun ⟨y, hy, h⟩ => ⟨y, hp.mem_iff.2 hy, h⟩⟩
      have h1 : v.1 = v'.1 := by
        by_cases hall : ∀ y ∈ (ReductionTree.node l r).leaves, isNaN fmt y = true
        · have hall' : ∀ y ∈ (ReductionTree.node l' r').leaves, isNaN fmt y = true :=
            fun y hy => hall y (hp.mem_iff.2 hy)
          have e1 : v.1 = fmt.canonicalNaN := by
            rcases minMaxTree_node_value hv with h | h
            · exact h
            · rw [hn.2 hall] at h; cases h
          have e2 : v'.1 = fmt.canonicalNaN := by
            rcases minMaxTree_node_value hv' with h | h
            · exact h
            · rw [hn'.2 hall'] at h; cases h
          rw [e1, e2]
        · have hv1 : isNaN fmt v.1 = false := by
            cases h : isNaN fmt v.1
            · rfl
            · exact absurd (hn.1 h) hall
          have hv1' : isNaN fmt v'.1 = false := by
            cases h : isNaN fmt v'.1
            · rfl
            · exact absurd (fun y hy => hn'.1 h y (hp.mem_iff.1 hy)) hall
          obtain ⟨hmem, hmin⟩ := hm hv1
          obtain ⟨hmem', hmin'⟩ := hm' hv1'
          rcases selLt_total pickLess fmt (hL _ hmem) (hL' _ hmem') hv1 hv1' with h | h | h
          · exact absurd h (hmin' v.1 (hp.mem_iff.1 hmem) hv1)
          · exact h
          · exact absurd h (hmin v'.1 (hp.mem_iff.2 hmem') hv1')
      exact Prod.ext h1 (by rw [hb, hb', hbb])

def combReductionTree : ReductionTree → List Nat → ReductionTree
  | t, [] => t
  | t, x :: xs => combReductionTree (.node t (.leaf x)) xs

theorem combReductionTree_leaves :
    ∀ (t : ReductionTree) (xs : List Nat), (combReductionTree t xs).leaves = t.leaves ++ xs
  | t, [] => by simp [combReductionTree]
  | t, x :: xs => by
    rw [combReductionTree, combReductionTree_leaves _ xs]
    simp [ReductionTree.leaves]

theorem combReductionTree_result {step : Nat → Nat → Nat × StatusFlags → Prop} :
    ∀ (xs : List Nat) (t : ReductionTree) (a : Nat) (F : StatusFlags) (r : Nat × StatusFlags),
      ReductionTreeResultOf step t (a, F) → OrderedReductionOf step a xs r →
      ReductionTreeResultOf step (combReductionTree t xs) (r.1, F.union r.2)
  | [], t, a, F, r, ht, hr => by
    subst hr; simpa [combReductionTree, union_empty] using ht
  | x :: xs, t, a, F, r, ht, hr => by
    obtain ⟨s, u, hs, hu, rfl⟩ := hr
    have hn : ReductionTreeResultOf step (.node t (.leaf x)) (s.1, (F.union {}).union s.2) :=
      ⟨_, _, _, ht, rfl, hs, rfl⟩
    have := combReductionTree_result xs _ s.1 _ u hn hu
    simpa [combReductionTree, union_assoc, union_empty] using this

theorem reduceWithFlags_orderIndependent {op : NaNOperation} {pickLess : Bool} {fmt : Format}
    (step : BitVec fmt.width → BitVec fmt.width → BitVec fmt.width × StatusFlags)
    (h : ∀ a x, MinMaxNumberSpecOf Specialization.riscv op pickLess fmt a.toNat x.toNat (bitsResult (step a x)))
    (init : BitVec fmt.width) (xs : List (BitVec fmt.width)) :
    OrderIndependentReductionOf (MinMaxNumberSpecOf Specialization.riscv op pickLess fmt) init.toNat
      (xs.map (·.toNat)) (bitsResult (reduceWithFlags step init xs)) := by
  intro t v hp hv
  have hc := combReductionTree_result (xs.map (·.toNat)) (.leaf init.toNat) init.toNat {} _ rfl
    (reduceWithFlags_ordered step h init xs)
  rw [empty_union] at hc
  have hp' : t.leaves.Perm (combReductionTree (.leaf init.toNat) (xs.map (·.toNat))).leaves := by
    rw [combReductionTree_leaves]; simpa [ReductionTree.leaves] using hp
  have hL : ∀ y ∈ t.leaves, y < 2 ^ fmt.width := by
    intro y hy
    rcases List.mem_cons.1 (hp.mem_iff.1 hy) with rfl | hy
    · exact init.isLt
    · obtain ⟨x, _, rfl⟩ := List.mem_map.1 hy; exact x.isLt
  exact minMaxTree_unique op pickLess fmt hp' hL hv hc

end SoftFloat.RISCV.Proof
