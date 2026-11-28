/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.Cusps
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Datum
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Action
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation
import TauCeti.GroupTheory.GroupAction.ConjAct
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.UpperRightHom
import TauCeti.NumberTheory.Modular.ConjugateTranslation

/-!
# Compatibility of Fuchsian and arithmetic cusp widths

For a subgroup `Γ ≤ SL(2, ℤ)` and a Fuchsian cusp datum `D` of `Γ.map sl2zToPSL2R` with
integral scaling `D.scaling = sl2zToPSL2R γ⁻¹`, `D.width` agrees with Mathlib's projective
cusp width `(ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty`.

## Main results

* `TauCeti.cuspDatum_width_eq_widthInfty`: equality of `D.width` and `widthInfty` at
  `D.scaling = sl2zToPSL2R γ⁻¹`.
-/

public noncomputable section

open Matrix Matrix.ProjectiveSpecialLinearGroup Matrix.SpecialLinearGroup MulAction Subgroup
open scoped MatrixGroups Pointwise

namespace TauCeti

variable {Γ : Subgroup SL(2, ℤ)}

private lemma cuspDatum_width_mem_periods {D : (Γ.map sl2zToPSL2R).CuspDatum} {γ : SL(2, ℤ)}
    (hσ : D.scaling = sl2zToPSL2R γ⁻¹) :
    D.width ∈ (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).periods := by
  obtain ⟨g₀, hg₀, hg₀_eq⟩ := Subgroup.mem_map.mp D.generator.property
  have hconj : sl2zToPSL2R (γ⁻¹ * g₀ * γ) =
      Matrix.ProjectiveSpecialLinearGroup.upperRightHom D.width := by
    simpa [map_mul, map_inv, hσ, hg₀_eq] using D.scaling_mul_generator_mul_inv
  rw [sl2zToPSL2R_apply, Matrix.ProjectiveSpecialLinearGroup.upperRightHom_apply,
    Matrix.ProjectiveSpecialLinearGroup.mk_eq_mk_iff] at hconj
  have hmem : mapGL ℝ (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) (γ⁻¹ * g₀ * γ)) ∈
      ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ)) := by
    rw [mapGL_map_intCast (R := ℝ) (S := ℝ), Subgroup.mem_conjAct_smul_iff, inv_inv]
    simpa [map_mul, map_inv, mul_assoc] using Subgroup.mem_map_of_mem (mapGL ℝ) hg₀
  rw [Subgroup.periods, Subgroup.mem_strictPeriods_iff, Subgroup.mem_adjoinNegOne_iff]
  rcases hconj with h | h
  · exact Or.inl (by rwa [← h, mapGL_transvection_eq_upperRightHom] at hmem)
  · exact Or.inr (by
      rwa [neg_eq_iff_eq_neg.mp h.symm, mapGL_neg, mapGL_transvection_eq_upperRightHom] at hmem)

private lemma mem_zmultiples_cuspDatum_width_of_mem_periods {D : (Γ.map sl2zToPSL2R).CuspDatum}
    {γ : SL(2, ℤ)} (hσ : D.scaling = sl2zToPSL2R γ⁻¹) {w : ℝ}
    (hw : w ∈ (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).periods) :
    w ∈ AddSubgroup.zmultiples D.width := by
  rw [Subgroup.periods, Subgroup.mem_strictPeriods_iff, Subgroup.mem_adjoinNegOne_iff] at hw
  obtain ⟨g₁, hg₁, hconj₁⟩ : ∃ g₁ ∈ Γ, D.scaling * sl2zToPSL2R g₁ * D.scaling⁻¹ =
      Matrix.ProjectiveSpecialLinearGroup.upperRightHom w := by
    have hT (j : ℤ) : D.scaling * sl2zToPSL2R (γ * ModularGroup.T ^ j * γ⁻¹) * D.scaling⁻¹ =
        Matrix.ProjectiveSpecialLinearGroup.upperRightHom (j : ℝ) := by
      simp only [hσ, ← map_inv, ← map_mul, inv_inv, mul_assoc, inv_mul_cancel, mul_one,
        inv_mul_cancel_left, TauCeti.UpperHalfPlane.sl2zToPSL2R_T_zpow]
    rcases hw with hp | hn
    · obtain ⟨j, rfl, hj⟩ := exists_int_eq_and_conj_T_zpow_mem_of_upperRightHom_mem_conj γ hp
      exact ⟨_, hj, hT j⟩
    · obtain ⟨j, rfl, hj⟩ :=
        exists_int_eq_and_neg_conj_T_zpow_mem_of_neg_upperRightHom_mem_conj γ hn
      exact ⟨_, hj, by rw [sl2zToPSL2R_neg]; exact hT j⟩
  have hstab : (⟨sl2zToPSL2R g₁, Subgroup.mem_map_of_mem _ hg₁⟩ : Γ.map sl2zToPSL2R) ∈
      stabilizer (Γ.map sl2zToPSL2R) D.cusp := by
    rw [mem_stabilizer_iff, Subgroup.mk_smul]
    apply MulAction.injective D.scaling; dsimp only
    rw [← inv_smul_smul D.scaling D.cusp, ← mul_smul, ← mul_smul, hconj₁, inv_smul_smul,
      D.scaling_smul_cusp, Matrix.ProjectiveSpecialLinearGroup.upperRightHom_smul_infty]
  obtain ⟨n, hn⟩ := D.mem_stabilizer_iff_conj.mp hstab
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by
    rw [hconj₁] at hn
    rw [zsmul_eq_mul, (Matrix.ProjectiveSpecialLinearGroup.upperRightHom_injective hn).symm]⟩

/-- **Compatibility of Fuchsian and arithmetic cusp widths**: at `D.scaling = sl2zToPSL2R γ⁻¹`,
`D.width` equals Mathlib's projective width `widthInfty` of `γ⁻¹ Γ γ`. -/
theorem cuspDatum_width_eq_widthInfty {D : (Γ.map sl2zToPSL2R).CuspDatum} {γ : SL(2, ℤ)}
    (hσ : D.scaling = sl2zToPSL2R γ⁻¹) :
    D.width = (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty := by
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  have hper : Γγ.adjoinNegOne.strictPeriods = AddSubgroup.zmultiples D.width :=
    le_antisymm (fun _ hw ↦ mem_zmultiples_cuspDatum_width_of_mem_periods hσ hw)
      (AddSubgroup.zmultiples_le.mpr (cuspDatum_width_mem_periods hσ))
  rw [Subgroup.widthInfty]
  exact (Subgroup.strictWidthInfty_eq_of_strictPeriods_eq_zmultiples hper D.width_pos.le).symm

end TauCeti

end
