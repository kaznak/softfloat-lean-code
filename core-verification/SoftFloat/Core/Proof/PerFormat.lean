/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Operators.PerFormat
import SoftFloat.Core.Proof.Encoding

namespace SoftFloat.Proof

open SoftFloat Spec

theorem toNat_ofNat_of_lt {w n : Nat} (h : n < 2 ^ w) : (BitVec.ofNat w n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem spec_ofNat {w : Nat} {P : Nat → Prop} {n : Nat} (hp : P n) (h : n < 2 ^ w) :
    P (BitVec.ofNat w n).toNat := by
  rwa [toNat_ofNat_of_lt h]

theorem spec_bitsResult {w : Nat} {P : Nat × StatusFlags → Prop} {r : Nat × StatusFlags}
    (hp : P r) (h : r.1 < 2 ^ w) :
    P (bitsResult ((BitVec.ofNat w r.1, r.2) : BitVec w × StatusFlags)) := by
  have : bitsResult ((BitVec.ofNat w r.1, r.2) : BitVec w × StatusFlags) = r := by
    simp only [bitsResult, toNat_ofNat_of_lt h]
  rwa [this]

theorem convertFormat_isEncoding {sp : Specialization} (hsp : Specialization.Valid sp)
    {src dst : Format} {rm : RoundingDirection} {a : Nat} {r : Nat × StatusFlags}
    (h : ConvertFormatSpecOf sp src dst rm a r) : dst.IsEncoding r.1 := by
  unfold ConvertFormatSpecOf at h
  split at h
  · rw [h.1]; exact (hsp.propagateNaN _ _ _).2
  · rw [h.1]; exact (hsp.propagateNaN _ _ _).2
  · exact h.1
  · exact h.1
  · exact h.1
  · exact h.1

theorem roundToIntegral_isEncoding {sp : Specialization} (hsp : Specialization.Valid sp)
    {fmt : Format} {rm : RoundingDirection} {exact : Bool} {a : Nat} {r : Nat × StatusFlags}
    (h : RoundToIntegralSpecOf sp fmt rm exact a r) : fmt.IsEncoding r.1 := by
  unfold RoundToIntegralSpecOf at h
  split at h
  · rw [h.1]; exact (hsp.propagateNaN _ _ _).2
  · rw [h.1]; exact (hsp.propagateNaN _ _ _).2
  · exact h.1
  · exact h.1
  · exact h.1
  · exact h.1

theorem toNat_emod_two_pow_lt (n : Int) (w : Nat) : (n % (2 ^ w : Int)).toNat < 2 ^ w := by
  have hpos : (0 : Int) < 2 ^ w := by positivity
  have h0 := Int.emod_nonneg n (Int.ne_of_gt hpos)
  have h1 := Int.emod_lt_of_pos n hpos
  have h2 : ((2 ^ w : Nat) : Int) = 2 ^ w := by push_cast; rfl
  omega

theorem convertToInteger_lt {sp : Specialization} (hsp : Specialization.Valid sp)
    {fmt : Format} {rm : RoundingDirection} {exact signed : Bool} {w a : Nat}
    {r : Nat × StatusFlags}
    (h : ConvertToIntegerSpecOf sp fmt rm exact signed w a r) : r.1 < 2 ^ w := by
  have hinv := hsp.intOutOfRange fmt rm exact signed w a
  unfold ConvertToIntegerSpecOf at h
  split at h
  · rw [h]; exact hinv
  · rw [h]; exact hinv
  · rw [h]; exact hinv
  all_goals
    dsimp only at h
    split at h
    · rw [h]; exact hinv
    · split at h
      · rw [h]; exact hinv
      · rw [h.1]; exact toNat_emod_two_pow_lt _ w

theorem perFormat_correct {sp : Specialization} {o : Ops} (hsp : Specialization.Valid sp)
    (hc : Correct sp o) (fmt : Format) : FormatCorrect sp fmt (perFormat o fmt) where
  addition rm a b :=
    have h := hc.addition fmt fmt fmt rm a.toNat b.toNat ⟨a.isLt, b.isLt⟩
    spec_bitsResult h h.1
  subtraction rm a b :=
    have h := hc.subtraction fmt fmt fmt rm a.toNat b.toNat ⟨a.isLt, b.isLt⟩
    spec_bitsResult h h.1
  multiplication rm a b :=
    have h := hc.multiplication fmt fmt fmt rm a.toNat b.toNat ⟨a.isLt, b.isLt⟩
    spec_bitsResult h h.1
  division rm a b :=
    have h := hc.division fmt fmt fmt rm a.toNat b.toNat ⟨a.isLt, b.isLt⟩
    spec_bitsResult h h.1
  squareRoot rm a :=
    have h := hc.squareRoot fmt fmt rm a.toNat a.isLt
    spec_bitsResult h h.1
  fusedMultiplyAdd rm a b c :=
    have h := hc.fusedMultiplyAdd fmt fmt fmt fmt rm a.toNat b.toNat c.toNat ⟨a.isLt, b.isLt, c.isLt⟩
    spec_bitsResult h h.1
  roundToIntegral rm exact a :=
    have h := hc.roundToIntegral fmt rm exact a.toNat a.isLt
    spec_bitsResult h (roundToIntegral_isEncoding hsp h)
  compareQuietEqual a b := hc.comparison fmt fmt _ _ a.toNat b.toNat trivial
  compareSignalingEqual a b := hc.comparison fmt fmt _ _ a.toNat b.toNat trivial
  compareSignalingLess a b := hc.comparison fmt fmt _ _ a.toNat b.toNat trivial
  compareQuietLess a b := hc.comparison fmt fmt _ _ a.toNat b.toNat trivial
  compareSignalingLessEqual a b := hc.comparison fmt fmt _ _ a.toNat b.toNat trivial
  compareQuietLessEqual a b := hc.comparison fmt fmt _ _ a.toNat b.toNat trivial
  convertFormat rm dst a :=
    have h := hc.convertFormat fmt dst rm a.toNat a.isLt
    spec_bitsResult h (convertFormat_isEncoding hsp h)
  convertToInteger rm exact signed w a hw :=
    have h := hc.convertToInteger fmt rm exact signed w a.toNat ⟨hw, a.isLt⟩
    spec_bitsResult h (convertToInteger_lt hsp h)
  convertFromInt rm signed _ x :=
    have h := hc.convertFromInt fmt rm (if signed then x.toInt else (x.toNat : Int)) trivial
    spec_bitsResult h h.1
  copy a :=
    have h : o.copy fmt a.toNat = a.toNat := hc.copy fmt a.toNat trivial
    spec_ofNat (P := CopySpecOf fmt a.toNat) h (by rw [h]; exact a.isLt)
  abs a :=
    have h := hc.abs fmt a.toNat a.isLt
    spec_ofNat h (h ▸ withSign_lt fmt _ _)
  negate a :=
    have h := hc.negate fmt a.toNat a.isLt
    spec_ofNat h (h ▸ withSign_lt fmt _ _)
  copySign a b :=
    have h := hc.copySign fmt a.toNat b.toNat ⟨a.isLt, b.isLt⟩
    spec_ofNat h (h ▸ withSign_lt fmt _ _)
  classOf a := hc.classOf fmt a.toNat trivial
  minimumNumber a b :=
    have h := hc.minimumNumber fmt a.toNat b.toNat ⟨a.isLt, b.isLt⟩
    spec_bitsResult h h.1
  maximumNumber a b :=
    have h := hc.maximumNumber fmt a.toNat b.toNat ⟨a.isLt, b.isLt⟩
    spec_bitsResult h h.1
  minimum a b :=
    have h := hc.minimum fmt a.toNat b.toNat ⟨a.isLt, b.isLt⟩
    spec_bitsResult h h.1
  maximum a b :=
    have h := hc.maximum fmt a.toNat b.toNat ⟨a.isLt, b.isLt⟩
    spec_bitsResult h h.1

end SoftFloat.Proof
