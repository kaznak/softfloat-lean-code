/-
Copyright (c) 2026 Kazutaka Nakamura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kazutaka Nakamura
-/
import SoftFloat.Core.Spec
import SoftFloat.Core.Proof.Encoding
import SoftFloat.Core.Proof.RoundPack
import SoftFloat.RISCV.Spec.V
import SoftFloat.RISCV.Operators.Riscv
import SoftFloat.RISCV.Proof.Specialization

namespace SoftFloat.RISCV.Proof

open SoftFloat SoftFloat.Spec SoftFloat.Proof SoftFloat.RISCV.Spec

theorem reciprocalSquareRootTable_eq : reciprocalSquareRootTable = reciprocalSquareRootEstimateTable := by
  decide

theorem reciprocalTable_eq : reciprocalTable = reciprocalEstimateTable := by
  decide

theorem canonicalNaN_eq (fmt : Format) : fmt.canonicalNaN = Spec.canonicalNaN fmt := rfl

theorem normalizedInput_eq (fmt : Format) (u : Format.Unpacked) :
    normalizedInput fmt u = (normalizedExponent fmt u, normalizedSignificand fmt u) := by
  unfold normalizedInput normalizedSignificand normalizedExponent
  split_ifs with h
  · rw [show (1 - -((fmt.fracBits - (Nat.log2 u.fracField + 1) : Nat) : Int)).toNat
        = fmt.fracBits - (Nat.log2 u.fracField + 1) + 1 by omega]
  · rfl

theorem reciprocalSquareRootEstimate7_spec (fmt : Format) (a : Nat) :
    ReciprocalSquareRootEstimateSpecOf fmt a (reciprocalSquareRootEstimate7 fmt a) := by
  unfold ReciprocalSquareRootEstimateSpecOf reciprocalSquareRootEstimate7
  rw [classify_eq_fields]
  simp only [normalizedInput_eq, canonicalNaN_eq, reciprocalSquareRootTable_eq]
  cases hs : (fmt.unpack a).sign <;> split_ifs <;> simp_all [Format.quietBit]

theorem reciprocal_outputExponent (fmt : Format) (u : Format.Unpacked) (hE : u.expField ≠ fmt.expMax)
    (hEl : u.expField < 2 ^ fmt.expBits) (hF : u.fracField < 2 ^ fmt.fracBits)
    (hnz : ¬(u.expField = 0 ∧ u.fracField = 0)) :
    ((2 * (fmt.bias : Int) - 1 - normalizedExponent fmt u < -1
        ∨ 2 * (fmt.bias : Int) < 2 * (fmt.bias : Int) - 1 - normalizedExponent fmt u)
      ↔ (u.expField = 0 ∧ u.fracField < 2 ^ (fmt.fracBits - 2)))
    ∧ (-1 ≤ 2 * (fmt.bias : Int) - 1 - normalizedExponent fmt u
      ∨ (u.expField = 0 ∧ u.fracField < 2 ^ (fmt.fracBits - 2))) := by
  have hB := expMax_eq_two_mul_bias_add_one fmt
  have hf := one_le_fracBits fmt
  have h2 : 2 ≤ fmt.fracBits := by have := fmt.sigBits_three_le; unfold Format.fracBits; omega
  have hEm : fmt.expMax = 2 ^ fmt.expBits - 1 := rfl
  unfold normalizedExponent
  by_cases h0 : u.expField = 0
  · have hF0 : u.fracField ≠ 0 := fun h => hnz ⟨h0, h⟩
    have hL : Nat.log2 u.fracField < fmt.fracBits := (Nat.log2_lt hF0).2 hF
    have hiff : Nat.log2 u.fracField < fmt.fracBits - 2 ↔ u.fracField < 2 ^ (fmt.fracBits - 2) :=
      Nat.log2_lt hF0
    simp only [h0, ↓reduceIte, true_and]
    rw [← hiff]
    omega
  · simp only [h0, ↓reduceIte, false_and, or_false, iff_false]
    have : u.expField < fmt.expMax := by omega
    omega

theorem reciprocalOverflowsToInfinity_eq (m : RoundingMode) (s : Bool) :
    reciprocalOverflowsToInfinity m s = reciprocalEstimateOverflowIsInfinite m.toRoundingDirection s := by
  cases m <;> cases s <;> rfl

theorem reciprocalEstimate7_spec (fmt : Format) (m : RoundingMode) (a : Nat) :
    ReciprocalEstimateSpecOf fmt m.toRoundingDirection a (reciprocalEstimate7 fmt m a) := by
  have key := reciprocal_outputExponent fmt (fmt.unpack a)
  have hEl := unpack_expField_lt fmt a
  have hF := unpack_fracField_lt fmt a
  unfold ReciprocalEstimateSpecOf reciprocalEstimate7
  rw [classify_eq_fields]
  simp only [normalizedInput_eq, canonicalNaN_eq, reciprocalTable_eq, reciprocalOverflowsToInfinity_eq]
  split_ifs <;> simp_all [Format.quietBit] <;> omega

theorem getD_lt {l : List Nat} {n : Nat} (h : ∀ x ∈ l, x < n) (hn : 0 < n) (i : Nat) : l.getD i 0 < n := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => simpa using hn
  | some v => simpa using h v (List.mem_of_getElem? hi)

theorem reciprocalSquareRootTable_lt : ∀ x ∈ reciprocalSquareRootTable, x < 128 := by
  have h : reciprocalSquareRootTable.all (fun x => decide (x < 128)) = true := by rfl
  simpa [List.all_eq_true] using h

theorem reciprocalTable_lt : ∀ x ∈ reciprocalTable, x < 128 := by
  have h : reciprocalTable.all (fun x => decide (x < 128)) = true := by rfl
  simpa [List.all_eq_true] using h

theorem table_entry_mul_lt (fmt : Format) (h7 : 7 ≤ fmt.fracBits) {t : Nat} (ht : t < 128) :
    t * 2 ^ (fmt.fracBits - 7) < 2 ^ fmt.fracBits := by
  have : 2 ^ fmt.fracBits = 128 * 2 ^ (fmt.fracBits - 7) := by
    rw [show (128 : Nat) = 2 ^ 7 by rfl, ← pow_add]; congr 1; omega
  rw [this]
  exact Nat.mul_lt_mul_of_pos_right ht (by positivity)

theorem reciprocalSquareRootEstimate7_lt (fmt : Format) (h7 : 7 ≤ fmt.fracBits) (a : Nat) :
    (reciprocalSquareRootEstimate7 fmt a).1 < 2 ^ fmt.width := by
  have hB := expMax_eq_two_mul_bias_add_one fmt
  have hEm := expMax_lt fmt
  have hfb := Format.fracBits_le_bias fmt
  have hEl := unpack_expField_lt fmt a
  have ht : ∀ i, reciprocalSquareRootTable.getD i 0 < 128 := getD_lt reciprocalSquareRootTable_lt (by decide)
  unfold reciprocalSquareRootEstimate7
  simp only [normalizedInput_eq]
  split_ifs with h1 h2 h3 h4 h5
  · exact canonicalNaN_lt fmt
  · exact pack_lt fmt false (by positivity) (by positivity)
  · exact canonicalNaN_lt fmt
  · exact pack_lt fmt _ hEm (by positivity)
  · exact canonicalNaN_lt fmt
  · refine pack_lt fmt false ?_ (table_entry_mul_lt fmt h7 (ht _))
    unfold normalizedExponent
    split_ifs <;> omega

theorem reciprocalEstimate7_lt (fmt : Format) (h7 : 7 ≤ fmt.fracBits) (m : RoundingMode) (a : Nat) :
    (reciprocalEstimate7 fmt m a).1 < 2 ^ fmt.width := by
  have hB := expMax_eq_two_mul_bias_add_one fmt
  have hEm := expMax_lt fmt
  have ht : ∀ i, reciprocalTable.getD i 0 < 128 := getD_lt reciprocalTable_lt (by decide)
  have hs := fun i => table_entry_mul_lt fmt h7 (ht i)
  have hf0 : 0 < 2 ^ fmt.fracBits := by positivity
  unfold reciprocalEstimate7
  simp only [normalizedInput_eq]
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact pack_lt fmt _ (by positivity) (by positivity)
  · exact canonicalNaN_lt fmt
  · exact pack_lt fmt _ hEm (by positivity)
  · exact pack_lt fmt _ hEm (by positivity)
  · exact pack_lt fmt _ (by omega) (by omega)
  · refine pack_lt fmt _ (by positivity) ?_
    have hk : 1 ≤ (1 - (2 * (fmt.bias : Int) - 1 - normalizedExponent fmt (fmt.unpack a))).toNat := by omega
    have h1 := hs (normalizedSignificand fmt (fmt.unpack a) / 2 ^ (fmt.fracBits - 7))
    calc (2 ^ fmt.fracBits + _) / 2 ^ _ ≤ (2 ^ fmt.fracBits + _) / 2 ^ 1 :=
          Nat.div_le_div_left (Nat.pow_le_pow_right (by decide) hk) (by positivity)
      _ < 2 ^ fmt.fracBits := by omega
  · exact pack_lt fmt _ (by omega) (hs _)

end SoftFloat.RISCV.Proof
