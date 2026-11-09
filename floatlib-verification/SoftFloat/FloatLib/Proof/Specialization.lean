/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Operators
import SoftFloat.Core.Proof.Encoding
import SoftFloat.FloatLib.Spec.Choices
import SoftFloat.FloatLib.Operators.Specialization

namespace SoftFloat.FloatLib.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof

theorem firstWith_eq (p : Format × Nat → Bool) (p' : Format → Nat → Bool)
    (h : ∀ f x, p (f, x) = p' f x) :
    ∀ xs i, FloatLib.firstWith p xs i = SoftFloat.FloatLib.Spec.firstNaN p' xs i
  | [], _ => rfl
  | (f, x) :: xs, i => by
    unfold FloatLib.firstWith SoftFloat.FloatLib.Spec.firstNaN
    rw [h, firstWith_eq p p' h xs (i + 1)]

theorem nanSign_eq (op : NaNOperation) (i : Nat) (s : Bool) :
    FloatLib.nanSign op i s = SoftFloat.FloatLib.Spec.floatLibNaNSign op i s := by
  cases op <;> rfl

theorem floatlib_propagateNaN (op : NaNOperation) (dst : Format) (xs : List (Format × Nat)) :
    Specialization.floatlib.propagateNaN op dst xs = SoftFloat.FloatLib.Spec.floatLibNaN op dst xs := by
  have hs := firstWith_eq (fun x => x.1.isSNaNU (x.1.unpack x.2)) isSignalingNaN
    (fun f x => isSNaNU_unpack f x)
  have hn := firstWith_eq (fun x => x.1.isNaNU (x.1.unpack x.2)) isNaN
    (fun f x => isNaNU_unpack f x)
  show FloatLib.propagateNaN op dst xs = _
  unfold FloatLib.propagateNaN SoftFloat.FloatLib.Spec.floatLibNaN
  dsimp only
  rw [hs, hn]
  split <;> rename_i h <;> rw [h]
  · rfl
  · rw [nanSign_eq]; rfl

theorem two_pow_fracBits (fmt : Format) : 2 ^ fmt.fracBits = 2 * fmt.quietBit := by
  unfold Format.quietBit
  have := one_le_fracBits fmt
  rw [← Nat.pow_succ']
  congr 1
  omega

theorem nanFrac_lt (dst : Format) (p : Nat) :
    dst.quietBit + (if p < dst.quietBit then p else 0) < 2 ^ dst.fracBits := by
  rw [two_pow_fracBits]
  have := quietBit_pos dst
  split <;> omega

theorem propagateNaN_valid (op : NaNOperation) (dst : Format) (xs : List (Format × Nat)) :
    NaNResultValid dst (FloatLib.propagateNaN op dst xs) := by
  unfold FloatLib.propagateNaN
  dsimp only
  split
  · exact ⟨classify_pack_quietNaN dst false (quietBit_lt dst) le_rfl,
      pack_lt dst false (expMax_lt dst) (quietBit_lt dst)⟩
  · unfold FloatLib.nanOf
    exact ⟨classify_pack_quietNaN dst _ (nanFrac_lt dst _) (Nat.le_add_right _ _),
      pack_lt dst _ (expMax_lt dst) (nanFrac_lt dst _)⟩

-- ANCHOR: FloatLibSpecialization
theorem floatlib_valid : SoftFloat.Spec.Specialization.Valid Specialization.floatlib where
  propagateNaN op dst xs := propagateNaN_valid op dst xs
  intOutOfRange _ _ _ _ w _ := Nat.two_pow_pos w
  totalOrderNaN _ _ _ _ := by
    refine ⟨fun x y _ _ => ?_, fun x y _ _ h₁ h₂ => ?_, fun x y z _ _ _ h₁ h₂ => ?_⟩
      <;> simp only [Specialization.floatlib, decide_eq_true_eq] at * <;> omega
  admissiblePayload _ _ _ h := by simp [Specialization.floatlib] at h
  minNumMaxNumOfEqual _ _ _ _ := Or.inl rfl
  minNumMagOfEqual _ _ _ := ⟨rfl, rfl⟩
  minNumMagNaN _ _ := ⟨rfl, rfl⟩
  scaleBOfNaNExponent fmt _ _ _ := pack_lt fmt false (expMax_lt fmt) (quietBit_lt fmt)

theorem floatlib_choices : SoftFloat.FloatLib.Spec.FloatLibChoices Specialization.floatlib where
  propagateNaN op dst xs _ := floatlib_propagateNaN op dst xs
  fusedMultiplyAddZeroInfinityQuietNaNInvalid := rfl
  tininess := rfl
-- ANCHOR_END: FloatLibSpecialization

end SoftFloat.FloatLib.Proof
