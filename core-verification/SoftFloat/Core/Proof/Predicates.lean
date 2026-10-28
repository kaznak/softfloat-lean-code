/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Operators
import SoftFloat.Core.Proof.Encoding

namespace SoftFloat.Proof

open SoftFloat SoftFloat.Format SoftFloat.Spec

theorem isSignMinusSpecOf_isSignMinus (fmt : Format) (x : Nat) :
    IsSignMinusSpecOf fmt x (fmt.isSignMinus x) :=
  rfl

theorem isNormalSpecOf_isNormal (fmt : Format) (x : Nat) :
    IsNormalSpecOf fmt x (fmt.isNormal x) := by
  unfold IsNormalSpecOf Format.isNormal
  simp [classify_eq_normal_iff]

theorem isFinite_iff_exists (fmt : Format) (x : Nat) :
    IsFinite fmt x ↔ ∃ s, classify fmt x = .zero s ∨ classify fmt x = .subnormal s
      ∨ classify fmt x = .normal s := by
  unfold IsFinite; cases classify fmt x <;> simp

theorem isFiniteSpecOf_isFinite (fmt : Format) (x : Nat) :
    IsFiniteSpecOf fmt x (fmt.isFinite x) := by
  unfold IsFiniteSpecOf Format.isFinite
  rw [← isFinite_iff_exists, isFinite_iff]
  simp

theorem isZeroSpecOf_isZero (fmt : Format) (x : Nat) : IsZeroSpecOf fmt x (fmt.isZero x) := by
  unfold IsZeroSpecOf Format.isZero
  simp [classify_eq_zero_iff]

theorem isSubnormalSpecOf_isSubnormal (fmt : Format) (x : Nat) :
    IsSubnormalSpecOf fmt x (fmt.isSubnormal x) := by
  unfold IsSubnormalSpecOf Format.isSubnormal
  simp [classify_eq_subnormal_iff]

theorem isInfiniteSpecOf_isInfinite (fmt : Format) (x : Nat) :
    IsInfiniteSpecOf fmt x (fmt.isInfinite x) := by
  unfold IsInfiniteSpecOf Format.isInfinite
  simp [classify_eq_infinity_iff]

theorem isNaNSpecOf_isNaN (fmt : Format) (x : Nat) : IsNaNSpecOf fmt x (fmt.isNaN x) := by
  unfold IsNaNSpecOf Format.isNaN
  rw [isNaNU_unpack, isNaN_iff]

theorem isSignalingSpecOf_isSignaling (fmt : Format) (x : Nat) :
    IsSignalingSpecOf fmt x (fmt.isSignaling x) := by
  unfold IsSignalingSpecOf Format.isSignaling
  rw [classify_eq_signalingNaN_iff]

theorem isCanonicalSpecOf_isCanonical (fmt : Format) {x : Nat} (hx : x < 2 ^ fmt.width) :
    IsCanonicalSpecOf fmt x (fmt.isCanonical x) :=
  iff_of_true rfl hx

theorem radixSpecOf_radix (fmt : Format) (x : Nat) : RadixSpecOf fmt x (fmt.radix x) :=
  rfl

variable (sp : Specialization)

theorem softfloat_isSignMinus_spec :
    ∀ fmt x, x < 2 ^ fmt.width → IsSignMinusSpecOf fmt x ((softfloat sp).isSignMinus fmt x) :=
  fun fmt x _ => isSignMinusSpecOf_isSignMinus fmt x

theorem softfloat_isNormal_spec :
    ∀ fmt x, x < 2 ^ fmt.width → IsNormalSpecOf fmt x ((softfloat sp).isNormal fmt x) :=
  fun fmt x _ => isNormalSpecOf_isNormal fmt x

theorem softfloat_isFinite_spec :
    ∀ fmt x, x < 2 ^ fmt.width → IsFiniteSpecOf fmt x ((softfloat sp).isFinite fmt x) :=
  fun fmt x _ => isFiniteSpecOf_isFinite fmt x

theorem softfloat_isZero_spec :
    ∀ fmt x, x < 2 ^ fmt.width → IsZeroSpecOf fmt x ((softfloat sp).isZero fmt x) :=
  fun fmt x _ => isZeroSpecOf_isZero fmt x

theorem softfloat_isSubnormal_spec :
    ∀ fmt x, x < 2 ^ fmt.width → IsSubnormalSpecOf fmt x ((softfloat sp).isSubnormal fmt x) :=
  fun fmt x _ => isSubnormalSpecOf_isSubnormal fmt x

theorem softfloat_isInfinite_spec :
    ∀ fmt x, x < 2 ^ fmt.width → IsInfiniteSpecOf fmt x ((softfloat sp).isInfinite fmt x) :=
  fun fmt x _ => isInfiniteSpecOf_isInfinite fmt x

theorem softfloat_isNaN_spec :
    ∀ fmt x, x < 2 ^ fmt.width → IsNaNSpecOf fmt x ((softfloat sp).isNaN fmt x) :=
  fun fmt x _ => isNaNSpecOf_isNaN fmt x

theorem softfloat_isSignaling_spec :
    ∀ fmt x, x < 2 ^ fmt.width → IsSignalingSpecOf fmt x ((softfloat sp).isSignaling fmt x) :=
  fun fmt x _ => isSignalingSpecOf_isSignaling fmt x

theorem softfloat_isCanonical_spec :
    ∀ fmt x, x < 2 ^ fmt.width → IsCanonicalSpecOf fmt x ((softfloat sp).isCanonical fmt x) :=
  fun fmt _ hx => isCanonicalSpecOf_isCanonical fmt hx

theorem softfloat_radix_spec :
    ∀ fmt x, x < 2 ^ fmt.width → RadixSpecOf fmt x ((softfloat sp).radix fmt x) :=
  fun fmt x _ => radixSpecOf_radix fmt x

section Unique

variable {fmt : Format} {x : Nat} {r₁ r₂ : Bool}

theorem isSignMinusSpecOf_unique (h₁ : IsSignMinusSpecOf fmt x r₁)
    (h₂ : IsSignMinusSpecOf fmt x r₂) : r₁ = r₂ :=
  h₁.trans h₂.symm

theorem isNormalSpecOf_unique (h₁ : IsNormalSpecOf fmt x r₁) (h₂ : IsNormalSpecOf fmt x r₂) :
    r₁ = r₂ :=
  Bool.eq_iff_iff.2 (h₁.trans h₂.symm)

theorem isFiniteSpecOf_unique (h₁ : IsFiniteSpecOf fmt x r₁) (h₂ : IsFiniteSpecOf fmt x r₂) :
    r₁ = r₂ :=
  Bool.eq_iff_iff.2 (h₁.trans h₂.symm)

theorem isZeroSpecOf_unique (h₁ : IsZeroSpecOf fmt x r₁) (h₂ : IsZeroSpecOf fmt x r₂) :
    r₁ = r₂ :=
  Bool.eq_iff_iff.2 (h₁.trans h₂.symm)

theorem isSubnormalSpecOf_unique (h₁ : IsSubnormalSpecOf fmt x r₁)
    (h₂ : IsSubnormalSpecOf fmt x r₂) : r₁ = r₂ :=
  Bool.eq_iff_iff.2 (h₁.trans h₂.symm)

theorem isInfiniteSpecOf_unique (h₁ : IsInfiniteSpecOf fmt x r₁)
    (h₂ : IsInfiniteSpecOf fmt x r₂) : r₁ = r₂ :=
  Bool.eq_iff_iff.2 (h₁.trans h₂.symm)

theorem isNaNSpecOf_unique (h₁ : IsNaNSpecOf fmt x r₁) (h₂ : IsNaNSpecOf fmt x r₂) :
    r₁ = r₂ :=
  Bool.eq_iff_iff.2 (h₁.trans h₂.symm)

theorem isSignalingSpecOf_unique (h₁ : IsSignalingSpecOf fmt x r₁)
    (h₂ : IsSignalingSpecOf fmt x r₂) : r₁ = r₂ :=
  Bool.eq_iff_iff.2 (h₁.trans h₂.symm)

theorem isCanonicalSpecOf_unique (h₁ : IsCanonicalSpecOf fmt x r₁)
    (h₂ : IsCanonicalSpecOf fmt x r₂) : r₁ = r₂ :=
  Bool.eq_iff_iff.2 (h₁.trans h₂.symm)

theorem radixSpecOf_unique {n₁ n₂ : Nat} (h₁ : RadixSpecOf fmt x n₁) (h₂ : RadixSpecOf fmt x n₂) :
    n₁ = n₂ :=
  h₁.trans h₂.symm

end Unique

end SoftFloat.Proof
