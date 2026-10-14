/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection

/-!
# The commutator subgroup of the general linear group

Over a field with an element different from zero and one, the abstract commutator subgroup of
`GLₙ` is the determinant kernel. Conjugation by a diagonal matrix expresses every elementary
transvection as a commutator. The generation of `SLₙ` by transvections then supplies the reverse
inclusion to the one given by the determinant.

The hypothesis includes every field with more than two elements. It is needed in dimension two:
`GL₂(𝔽₂)` has a proper commutator subgroup, although its determinant is trivial. The statements
also include dimensions zero and one.

The proof uses `Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field`
and `TauCeti.diagonal_mul_transvection_mul_diagonal` in the imported transvection module.
-/

public section

open Matrix
open scoped commutatorElement

namespace TauCeti

noncomputable section

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {i j : ι}

/-- Every elementary transvection is a commutator when the field has an element different from
zero and one. -/
theorem transvectionUnit_mem_commutator (hij : i ≠ j) {a : K}
    (ha₀ : a ≠ 0) (ha₁ : a ≠ 1) (c : K) :
    transvectionUnit hij c ∈ commutator (GL ι K) := by
  classical
  let t : ι → Kˣ := Function.update (fun _ ↦ 1) i (Units.mk0 a ha₀)
  have htᵢ : t i = Units.mk0 a ha₀ := by simp [t]
  have htⱼ : t j = 1 := by simp [t, hij.symm]
  have hconj : diagGL t * transvectionUnit hij (c / (a - 1)) * (diagGL t)⁻¹ =
      transvectionUnit hij ((t i : K) * (c / (a - 1)) * ((t j)⁻¹ : Kˣ)) := by
    apply Units.ext
    simp only [Units.val_mul, coe_transvectionUnit, ← map_inv diagGL, diagGL_coe,
      Pi.inv_apply]
    exact diagonal_mul_transvection_mul_diagonal (fun k ↦ (t k).mul_inv) _
  have hcomm : ⁅diagGL t, transvectionUnit hij (c / (a - 1))⁆ =
      transvectionUnit hij c := by
    rw [commutatorElement_def, hconj,
      transvectionUnit_inv, ← transvectionUnit_add, htᵢ, htⱼ]
    simp only [Units.val_mk0, inv_one, Units.val_one, mul_one]
    congr 1
    field_simp
    ring
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- Over a field with more than two elements, the abstract commutator subgroup of `GLₙ` is
exactly the kernel of the unit-valued determinant. -/
theorem _root_.Matrix.GeneralLinearGroup.commutator_eq_ker_det {a : K}
    (ha₀ : a ≠ 0) (ha₁ : a ≠ 1) :
    commutator (GL ι K) = (GeneralLinearGroup.det : GL ι K →* Kˣ).ker := by
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro g _ h _
    simp [MonoidHom.mem_ker, commutatorElement_def]
  · intro g hg
    rw [← SpecialLinearGroup.range_toGL_eq_ker_det] at hg
    obtain ⟨s, rfl⟩ := hg
    have hgen := SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
      (ι := ι) (K := K)
    have hle : Subgroup.closure (Set.range (TransvectionStruct.toSpecialLinearGroup :
        TransvectionStruct ι K → SpecialLinearGroup ι K)) ≤
        (commutator (GL ι K)).comap SpecialLinearGroup.toGL := by
      rw [Subgroup.closure_le]
      rintro _ ⟨v, rfl⟩
      rcases v with ⟨i, j, hij, c⟩
      apply (Subgroup.mem_comap).mpr
      rw [TransvectionStruct.toSpecialLinearGroup_mk,
        toGL_transvection_eq_transvectionUnit]
      exact transvectionUnit_mem_commutator hij ha₀ ha₁ c
    rw [hgen] at hle
    exact hle (Subgroup.mem_top s)

end

end TauCeti
