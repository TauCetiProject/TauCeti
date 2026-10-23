/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection

/-!
# Perfectness of special linear groups

Over a field containing a nonzero element whose square is not one, the special linear group
on any finite coordinate type is perfect. Conjugation by the determinant-one diagonal matrix
with entries `a` and `a⁻¹` rescales a transvection by `a²`. Every transvection is consequently
a commutator, and transvections generate the special linear group. The hypothesis holds over
every infinite field; it excludes the small-field exceptions in rank two.

The commutator calculation generalizes Mathlib's `Matrix.commutator_diag2_transvection`
and the perfectness statement generalizes `Matrix.SL2.commutator_eq_top` to arbitrary finite
coordinate types. Generation is reused from
`Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §6d.
-/

public section

open scoped commutatorElement

namespace Matrix.SpecialLinearGroup

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {i j : ι}

/-- Conjugation by the determinant-one two-coordinate diagonal matrix rescales a transvection
by `a²`, so its commutator has parameter `b * (a² - 1)`. -/
theorem commutatorElement_diag2n_transvection (hij : i ≠ j) (a : F) (ha : a ≠ 0)
    (b : F) :
    ⁅diag2n hij a ha, transvection hij b⁆ = transvection hij (b * (a ^ 2 - 1)) := by
  have hinv : (diag2n hij a ha)⁻¹ = diag2n hij a⁻¹ (inv_ne_zero ha) := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    simp only [coe_mul, diag2n_coe, diagonal_mul_diagonal, coe_one]
    apply diagonal_eq_one.mpr
    funext k
    split_ifs <;> simp_all
  have hconj : diag2n hij a ha * transvection hij b * (diag2n hij a ha)⁻¹ =
      transvection hij (a ^ 2 * b) := by
    rw [hinv]
    apply Subtype.ext
    simp only [coe_mul, diag2n_coe, transvection_coe]
    have hc := TauCeti.diagonal_mul_transvection_mul_diagonal (i := i) (j := j)
      (v := fun k ↦ if k = i then a else if k = j then a⁻¹ else 1)
      (w := fun k ↦ if k = i then a⁻¹ else if k = j then a⁻¹⁻¹ else 1)
      (by intro k; split_ifs <;> simp_all) b
    simpa [Matrix.transvection, hij, hij.symm, pow_two, mul_assoc, mul_comm, mul_left_comm]
      using hc
  rw [commutatorElement_def, hconj, transvection_inv, ← transvection_add]
  congr 1
  ring

/-- Every transvection is in the commutator subgroup if the field contains a nonzero element
whose square is not one. -/
theorem transvection_mem_commutator (hij : i ≠ j) {a : F}
    (ha : a ≠ 0) (hasq : a ^ 2 ≠ 1) (c : F) :
    transvection hij c ∈ commutator (SpecialLinearGroup ι F) := by
  have hc : c / (a ^ 2 - 1) * (a ^ 2 - 1) = c :=
    div_mul_cancel₀ c (sub_ne_zero.mpr hasq)
  rw [← hc, ← commutatorElement_diag2n_transvection hij a ha]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- The special linear group over a field with a nonzero element whose square is not one
is perfect, in every finite rank, including ranks zero and one. -/
theorem commutator_eq_top {a : F} (ha : a ≠ 0) (hasq : a ^ 2 ≠ 1) :
    commutator (SpecialLinearGroup ι F) = ⊤ := by
  apply le_antisymm le_top
  rw [← closure_range_toSpecialLinearGroup_eq_top_of_field (ι := ι) (K := F),
    Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  rw [TransvectionStruct.toSpecialLinearGroup_mk]
  exact transvection_mem_commutator hij ha hasq c

end Matrix.SpecialLinearGroup
