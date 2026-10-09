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
and the diagonal-conjugation formula in the imported transvection module.
-/

public section

open Matrix
open scoped commutatorElement

namespace TauCeti

noncomputable section

variable {K : Type*} [Field K] {n : ℕ} {i j : Fin n}

/-- Every elementary transvection is a commutator when the field has an element different from
zero and one. -/
theorem transvectionUnit_mem_commutator (hij : i ≠ j) {a : K}
    (ha₀ : a ≠ 0) (ha₁ : a ≠ 1) (c : K) :
    transvectionUnit hij c ∈ commutator (GL (Fin n) K) := by
  classical
  let t : Fin n → Kˣ := Function.update (fun _ ↦ 1) i (Units.mk0 a ha₀)
  have htᵢ : t i = Units.mk0 a ha₀ := by simp [t]
  have htⱼ : t j = 1 := by simp [t, hij.symm]
  have hcomm : ⁅diagGL t, transvectionUnit hij (c / (a - 1))⁆ =
      transvectionUnit hij c := by
    rw [commutatorElement_def, diagGL_mul_transvectionUnit_mul_inv,
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
    commutator (GL (Fin n) K) = (GeneralLinearGroup.det : GL (Fin n) K →* Kˣ).ker := by
  apply le_antisymm
  · apply Subgroup.commutator_le.mpr
    intro g _ h _
    simp [MonoidHom.mem_ker, commutatorElement_def]
  · intro g hg
    let s := SpecialLinearGroup.toGLKerEquiv.symm ⟨g, hg⟩
    have hs : SpecialLinearGroup.toGL s = g :=
      congrArg Subtype.val (SpecialLinearGroup.toGLKerEquiv.apply_symm_apply ⟨g, hg⟩)
    rw [← hs]
    have hgen := SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
      (ι := Fin n) (K := K)
    have hle : Subgroup.closure (Set.range (TransvectionStruct.toSpecialLinearGroup :
        TransvectionStruct (Fin n) K → SpecialLinearGroup (Fin n) K)) ≤
        (commutator (GL (Fin n) K)).comap SpecialLinearGroup.toGL := by
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
