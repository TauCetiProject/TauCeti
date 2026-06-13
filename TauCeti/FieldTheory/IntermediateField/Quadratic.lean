/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Quadratic normal forms in intermediate fields

This file contains a small normal-form lemma, in characteristic not two, for adjoining one
element whose square already lies in an intermediate field.
-/

open IntermediateField

namespace TauCeti.IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- If `a` and `b` lie in `F`, then `a + b * x` lies in `F ⊔ K⟮x⟯`. -/
theorem mem_sup_adjoin_sq_of_exists {F : IntermediateField K L} {x y : L}
    (hy : ∃ a b : L, a ∈ F ∧ b ∈ F ∧ y = a + b * x) :
    y ∈ F ⊔ IntermediateField.adjoin K {x} := by
  rcases hy with ⟨a, b, ha, hb, rfl⟩
  have hF : F ≤ F ⊔ IntermediateField.adjoin K {x} := le_sup_left
  have hx : IntermediateField.adjoin K {x} ≤ F ⊔ IntermediateField.adjoin K {x} :=
    le_sup_right
  exact add_mem (hF ha)
    (mul_mem (hF hb) (hx (IntermediateField.mem_adjoin_of_mem K (Set.mem_singleton x))))

/-- If `x² ∈ F` and the extension field has characteristic not two, every element of
`F ⊔ K⟮x⟯` has the form `a + b * x` with `a, b ∈ F`. -/
theorem exists_add_mul_of_mem_sup_adjoin_sq {F : IntermediateField K L} {x : L}
    (hx2 : x ^ 2 ∈ F) [NeZero (2 : L)] {y : L}
    (hy : y ∈ F ⊔ IntermediateField.adjoin K {x}) :
    ∃ a b : L, a ∈ F ∧ b ∈ F ∧ y = a + b * x := by
  let S : IntermediateField K L :=
    { carrier := {y | ∃ a b : L, a ∈ F ∧ b ∈ F ∧ y = a + b * x}
      zero_mem' := ⟨0, 0, zero_mem F, zero_mem F, by simp⟩
      add_mem' := by
        rintro y z ⟨a, b, ha, hb, rfl⟩ ⟨c, d, hc, hd, rfl⟩
        exact ⟨a + c, b + d, add_mem ha hc, add_mem hb hd, by ring⟩
      one_mem' := ⟨1, 0, one_mem F, zero_mem F, by simp⟩
      mul_mem' := by
        rintro y z ⟨a, b, ha, hb, rfl⟩ ⟨c, d, hc, hd, rfl⟩
        refine ⟨a * c + (b * d) * x ^ 2, a * d + b * c, ?_, ?_, by ring⟩
        · exact add_mem (mul_mem ha hc) (mul_mem (mul_mem hb hd) hx2)
        · exact add_mem (mul_mem ha hd) (mul_mem hb hc)
      algebraMap_mem' := fun k => ⟨algebraMap K L k, 0, F.algebraMap_mem k, zero_mem F, by simp⟩
      inv_mem' := by
        classical
        rintro y ⟨a, b, ha, hb, rfl⟩
        by_cases hy0 : a + b * x = 0
        · exact ⟨0, 0, zero_mem F, zero_mem F, by simp [hy0]⟩
        · by_cases hD : a ^ 2 - b ^ 2 * x ^ 2 = 0
          · have hprod : (a - b * x) * (a + b * x) = 0 := by
              calc
                (a - b * x) * (a + b * x) = a ^ 2 - b ^ 2 * x ^ 2 := by ring
                _ = 0 := hD
            have hamul : a - b * x = 0 := (mul_eq_zero.mp hprod).resolve_right hy0
            have haeq : a = b * x := sub_eq_zero.mp hamul
            have hbx : b * x ≠ 0 := by
              intro h
              apply hy0
              rw [haeq, h]
              ring
            have hx0 : x ≠ 0 := by
              intro hx
              apply hbx
              rw [hx, mul_zero]
            have hden : (2 : L) * b * x ^ 2 ≠ 0 := by
              have hb0 : b ≠ 0 := left_ne_zero_of_mul hbx
              exact mul_ne_zero (mul_ne_zero (NeZero.ne (2 : L)) hb0) (pow_ne_zero 2 hx0)
            have hb0 : b ≠ 0 := left_ne_zero_of_mul hbx
            refine ⟨0, ((2 : L) * b * x ^ 2)⁻¹, zero_mem F, ?_, ?_⟩
            · exact inv_mem (mul_mem (mul_mem (F.natCast_mem 2) hb) hx2)
            · rw [haeq]
              field_simp [hden, hbx, hb0, hx0, NeZero.ne (2 : L)]
              rw [mul_zero, zero_mul, zero_add]
              norm_num [NeZero.ne (2 : L)]
          · have hDmem : a ^ 2 - b ^ 2 * x ^ 2 ∈ F :=
              sub_mem (pow_mem ha 2) (mul_mem (pow_mem hb 2) hx2)
            refine ⟨a * (a ^ 2 - b ^ 2 * x ^ 2)⁻¹,
              -b * (a ^ 2 - b ^ 2 * x ^ 2)⁻¹, ?_, ?_, ?_⟩
            · exact mul_mem ha (inv_mem hDmem)
            · exact mul_mem (neg_mem hb) (inv_mem hDmem)
            · field_simp [hD, hy0]
              ring }
  have hle : F ⊔ IntermediateField.adjoin K {x} ≤ S := by
    refine sup_le ?_ ?_
    · intro z hz
      exact ⟨z, 0, hz, zero_mem F, by simp⟩
    · rw [IntermediateField.adjoin_le_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact ⟨0, 1, zero_mem F, one_mem F, by simp⟩
  exact hle hy

/-- If `x² ∈ F` and the extension field has characteristic not two, every element of
`F ⊔ K⟮x⟯` has the form `a + b * x` with `a, b ∈ F`. -/
theorem mem_sup_adjoin_sq {F : IntermediateField K L} {x : L}
    (hx2 : x ^ 2 ∈ F) [NeZero (2 : L)] {y : L}
    (hy : y ∈ F ⊔ IntermediateField.adjoin K {x}) :
    ∃ a b : L, a ∈ F ∧ b ∈ F ∧ y = a + b * x :=
  exists_add_mul_of_mem_sup_adjoin_sq hx2 hy

/-- Membership in `F ⊔ K⟮x⟯`, for `x² ∈ F` in characteristic not two, is equivalent to
having the form `a + b * x` with `a, b ∈ F`. -/
theorem mem_sup_adjoin_sq_iff {F : IntermediateField K L} {x : L}
    (hx2 : x ^ 2 ∈ F) [NeZero (2 : L)] {y : L} :
    y ∈ F ⊔ IntermediateField.adjoin K {x} ↔
      ∃ a b : L, a ∈ F ∧ b ∈ F ∧ y = a + b * x :=
  ⟨exists_add_mul_of_mem_sup_adjoin_sq hx2, mem_sup_adjoin_sq_of_exists⟩

end TauCeti.IntermediateField
