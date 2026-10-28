/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Proof.RoundToOdd
import SoftFloat.RISCV.Proof.V
import SoftFloat.RISCV.Proof.Conversions
import SoftFloat.RISCV.Proof.Uniqueness
import SoftFloat.RISCV.Proof.Specialization

namespace SoftFloat.RISCV.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.RISCV.Spec

theorem narrowing_halving_steps (m : RoundingMode) (a : BitVec Format.binary64.width) :
    (((riscv.conversions .binary32 .binary16).FCVT m ((riscv.widenings .binary32 .binary64).VFNCVT_ROD_F_F_W a).1).1,
      ((riscv.widenings .binary32 .binary64).VFNCVT_ROD_F_F_W a).2.union
        ((riscv.conversions .binary32 .binary16).FCVT m ((riscv.widenings .binary32 .binary64).VFNCVT_ROD_F_F_W a).1).2)
      = (riscv.conversions .binary64 .binary16).FCVT m a := by
  set s := (riscv.widenings .binary32 .binary64).VFNCVT_ROD_F_F_W a
  set t := (riscv.conversions .binary32 .binary16).FCVT m s.1
  have hs := (widenings_correct .binary32 .binary64).VFNCVT_ROD_F_F_W a
  have ht := (conversions_correct .binary32 .binary16).FCVT m s.1
  have hd := (conversions_correct .binary64 .binary16).FCVT m a
  apply bitsResult_inj
  refine convertFormatSpecOf_unique ?_ hd
  by_cases hnan : classify .binary64 a.toNat = .quietNaN ∨ classify .binary64 a.toNat = .signalingNaN
  · have hs' : (bitsResult s).1 = Format.binary32.canonicalNaN
        ∧ (bitsResult s).2 = { invalidOperation := isSignalingNaN .binary64 a.toNat } := by
      unfold ConvertFormatSpecOf convertNaNResultOf at hs
      rcases hnan with h | h <;> rw [h] at hs <;> exact hs
    have ht' : (bitsResult t).1 = Format.binary16.canonicalNaN ∧ (bitsResult t).2 = {} := by
      unfold ConvertFormatSpecOf convertNaNResultOf at ht
      have hc : classify .binary32 (bitsResult s).1 = .quietNaN := by
        rw [hs'.1]; exact classify_canonicalNaN _
      simp only [bitsResult] at hc
      rw [hc] at ht
      refine ⟨ht.1, ?_⟩
      rw [ht.2]
      have : isSignalingNaN .binary32 s.1.toNat = false := by
        have := hs'.1; simp only [bitsResult] at this; rw [this]; exact isSignalingNaN_canonicalNaN _
      rw [this]
    unfold ConvertFormatSpecOf convertNaNResultOf
    have hgoal : convertNaNResultOf Specialization.riscv .binary64 .binary16 a.toNat
        (bitsResult (t.1, s.2.union t.2)) := by
      refine ⟨ht'.1, ?_⟩
      have h1 := hs'.2; have h2 := ht'.2
      simp only [bitsResult] at h1 h2 ⊢
      rw [h1, h2]; simp [StatusFlags.union]
    rcases hnan with h | h <;> rw [h] <;> exact hgoal
  · rw [not_or] at hnan
    exact convertFormatSpecOf_two_step (by decide) (by decide) (by decide) hnan.1 hnan.2 hs ht

end SoftFloat.RISCV.Proof
