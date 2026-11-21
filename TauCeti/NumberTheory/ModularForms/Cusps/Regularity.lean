/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
public import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation
import TauCeti.GroupTheory.GroupAction.ConjAct
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Cusp widths and regularity of cusp orbits

For `Γ ≤ SL(2, ℤ)`, this file compares the Fuchsian cusp datum width `D.width` at the integral
scaling `sl2zToPSL2R γ⁻¹` with Mathlib's projective width `widthInfty` of `γ⁻¹ Γ γ`, and for
`[Γ.FiniteIndex]` descends `Subgroup.IsRegularAtInfty` to `Γ.IsRegularCusp` on
`(Γ.map sl2zToPSL2R).CuspOrbit`.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §§2.4, 3.2.
-/

public section

open Matrix Matrix.SpecialLinearGroup MulAction OnePoint UpperHalfPlane
open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti.ModularForm

section IntegralCuspDatum

variable {Γ : Subgroup SL(2, ℤ)}

/-- If `mapGL ℝ s * upperRightHom w` (`s ∈ SL(2, ℤ)`) belongs to `γ⁻¹ Γ γ`, then `w` is an integer
`j` and `γ * (s * T ^ j) * γ⁻¹ ∈ Γ`. -/
theorem exists_int_eq_and_conj_mul_T_zpow_mem_of_mapGL_mul_upperRightHom_mem_conj
    (γ s : SL(2, ℤ)) {w : ℝ}
    (hw : mapGL ℝ s * Matrix.GeneralLinearGroup.upperRightHom w ∈
      ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))) :
    ∃ j : ℤ, w = j ∧ γ * (s * ModularGroup.T ^ j) * γ⁻¹ ∈ Γ := by
  obtain ⟨g, hg, hg_eq⟩ := Subgroup.mem_map.mp (Subgroup.mem_conjAct_inv_smul_iff.mp hw)
  set u : SL(2, ℤ) := s⁻¹ * (γ⁻¹ * g * γ) with hu_def
  have hconj : mapGL ℝ u = Matrix.GeneralLinearGroup.upperRightHom w := by
    rw [hu_def, map_mul, map_inv, map_mul, map_mul, map_inv, hg_eq]; group
  have hw_eq : w = (u 0 1 : ℝ) := by
    simpa [mapGL_coe_matrix, Matrix.GeneralLinearGroup.upperRightHom] using
      (congr_arg (fun M : GL (Fin 2) ℝ ↦ (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1) hconj).symm
  have hT : u = ModularGroup.T ^ (u 0 1) :=
    mapGL_injective (S := ℝ) (by rw [hconj, hw_eq, ModularGroup.mapGL_T_zpow_eq_upperRightHom])
  have hg_eq' : γ * (s * u) * γ⁻¹ = g := by rw [hu_def]; group
  exact ⟨u 0 1, hw_eq, by rwa [← hT, hg_eq']⟩

/-- A positive shift `upperRightHom w ∈ γ⁻¹ Γ γ` has integer translation `w = j` with
`γ * T ^ j * γ⁻¹ ∈ Γ`. -/
theorem exists_int_eq_and_conj_T_zpow_mem_of_upperRightHom_mem_conj (γ : SL(2, ℤ)) {w : ℝ}
    (hw : Matrix.GeneralLinearGroup.upperRightHom w ∈
      ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))) :
    ∃ j : ℤ, w = j ∧ γ * ModularGroup.T ^ j * γ⁻¹ ∈ Γ := by
  simpa only [one_mul] using
    exists_int_eq_and_conj_mul_T_zpow_mem_of_mapGL_mul_upperRightHom_mem_conj (Γ := Γ) γ 1
      (by simpa only [map_one, one_mul] using hw)

/-- A negative shift `-upperRightHom w ∈ γ⁻¹ Γ γ` has integer translation `w = j` with
`-(γ * T ^ j * γ⁻¹) ∈ Γ`. -/
theorem exists_int_eq_and_neg_conj_T_zpow_mem_of_neg_upperRightHom_mem_conj (γ : SL(2, ℤ)) {w : ℝ}
    (hw : -Matrix.GeneralLinearGroup.upperRightHom w ∈
      ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))) :
    ∃ j : ℤ, w = j ∧ -(γ * ModularGroup.T ^ j * γ⁻¹) ∈ Γ := by
  simpa only [neg_one_mul, mul_neg, neg_mul, one_mul] using
    exists_int_eq_and_conj_mul_T_zpow_mem_of_mapGL_mul_upperRightHom_mem_conj (Γ := Γ) γ (-1)
      (by simpa only [Matrix.SpecialLinearGroup.mapGL_neg_one, neg_one_mul] using hw)

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
    rw [mapGL_map_intCast (R := ℝ) (S := ℝ), Subgroup.mem_conjAct_inv_smul_iff]
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

/-- If `D.scaling = sl2zToPSL2R γ⁻¹`, then `D.cuspOrbit = Γ.cuspOrbitOfSL2Z γ`. -/
theorem cuspDatum_cuspOrbit_eq_of_scaling_eq [Γ.FiniteIndex] {D : (Γ.map sl2zToPSL2R).CuspDatum}
    {γ : SL(2, ℤ)} (hσ : D.scaling = sl2zToPSL2R γ⁻¹) : D.cuspOrbit = Γ.cuspOrbitOfSL2Z γ :=
  Subtype.ext <| by
    rw [D.cuspOrbit_val, Γ.cuspOrbitOfSL2Z_val, D.cusp_eq_inv_scaling_smul_infty, hσ, ← map_inv,
      inv_inv]

end IntegralCuspDatum

end TauCeti.ModularForm

namespace Subgroup

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

/-- **Regularity of a cusp orbit `C` of `Γ ≤ SL(2, ℤ)`**: `∞` is regular for `γ⁻¹ Γ γ` at every
integral representative `γ ∈ SL(2, ℤ)` of `C`. -/
def IsRegularCusp (C : (Γ.map sl2zToPSL2R).CuspOrbit) : Prop :=
  ∀ γ : SL(2, ℤ), Γ.cuspOrbitOfSL2Z γ = C →
    (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsRegularAtInfty

/-- Unfolding `Subgroup.IsRegularCusp` across module boundaries. -/
theorem isRegularCusp_def (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    Γ.IsRegularCusp C ↔ ∀ γ : SL(2, ℤ), Γ.cuspOrbitOfSL2Z γ = C →
      (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsRegularAtInfty := Iff.rfl

private lemma isRegularAtInfty_conj_of_cuspOrbitOfSL2Z_eq {γ γ' : SL(2, ℤ)}
    (h : Γ.cuspOrbitOfSL2Z γ = Γ.cuspOrbitOfSL2Z γ') :
    (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsRegularAtInfty ↔
      (ConjAct.toConjAct (mapGL ℝ γ')⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsRegularAtInfty := by
  obtain ⟨g₀, hg₀, hc⟩ := (Γ.cuspOrbitOfSL2Z_eq_iff γ γ').mp h
  set m : SL(2, ℤ) := γ⁻¹ * g₀ * γ' with hm_def
  have hm_10 : (mapGL ℝ m) 1 0 = 0 := by simpa [mapGL_coe_matrix] using hc
  have hm_div : (mapGL ℝ m) 0 0 / (mapGL ℝ m) 1 1 = 1 := by
    have had := mul_apply_one_one_eq_one_of_apply_one_zero_eq_zero hc
    rcases Int.eq_one_or_neg_one_of_mul_eq_one had with h1 | h1 <;>
      · have hm11 : m 1 1 = m 0 0 := by rw [h1] at had ⊢; omega
        simp [mapGL_coe_matrix, h1, hm11]
  have hγ' : γ' = g₀⁻¹ * γ * m := by rw [hm_def]; group
  have hconj : ConjAct.toConjAct (mapGL ℝ γ')⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ)) =
      ConjAct.toConjAct (mapGL ℝ m)⁻¹ •
        (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))) := by
    rw [hγ', map_mul, map_mul, _root_.mul_inv_rev, _root_.mul_inv_rev, ConjAct.toConjAct_mul,
      ConjAct.toConjAct_mul, mul_smul, mul_smul, map_inv (mapGL ℝ), inv_inv,
      Subgroup.conjAct_pointwise_smul_eq_self
        (Subgroup.le_normalizer (Subgroup.mem_map_of_mem _ hg₀))]
  have hsp (H : Subgroup (GL (Fin 2) ℝ)) :
      (ConjAct.toConjAct (mapGL ℝ m)⁻¹ • H).strictPeriods = H.strictPeriods := by
    ext x; rw [Subgroup.mem_strictPeriods_conj_of_upperTriangular hm_10, hm_div, one_mul]
  simp only [hconj, Subgroup.IsRegularAtInfty, Subgroup.periods, Subgroup.adjoinNegOne_conj, hsp]

/-- Regularity of `Γ.cuspOrbitOfSL2Z γ` is regularity at `∞` of `γ⁻¹ Γ γ`. -/
@[simp] theorem isRegularCusp_cuspOrbitOfSL2Z (γ : SL(2, ℤ)) :
    Γ.IsRegularCusp (Γ.cuspOrbitOfSL2Z γ) ↔
      (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsRegularAtInfty :=
  ⟨fun h ↦ h γ rfl, fun h _ hγ' ↦ (isRegularAtInfty_conj_of_cuspOrbitOfSL2Z_eq Γ hγ'.symm).mp h⟩

/-- When `-I ∈ Γ`, every cusp orbit of `Γ` is regular. -/
theorem isRegularCusp_of_neg_one_mem (h : (-1 : SL(2, ℤ)) ∈ Γ) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    Γ.IsRegularCusp C := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  rw [isRegularCusp_cuspOrbitOfSL2Z]
  exact Subgroup.isRegularAtInfty_of_neg_one_mem <| Subgroup.mem_conjAct_smul_of_mem_center
    (Subgroup.mem_center_iff.mpr fun _ ↦ by simp) (mapGL ℝ γ)⁻¹
    (by rw [← Matrix.SpecialLinearGroup.mapGL_neg_one (R := ℤ)]; exact Subgroup.mem_map_of_mem _ h)

end Subgroup

end
