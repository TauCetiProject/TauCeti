/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
public import TauCeti.NumberTheory.ModularForms.Cusps.Basic
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Cusp widths and regularity of cusp orbits

For a finite-index subgroup `Γ ≤ SL(2, ℤ)`, every cusp orbit `C : (Γ.map sl2zToPSL2R).CuspOrbit` of
its effective Fuchsian image is represented by `Γ.cuspOrbitOfSL2Z γ` (`γ • ∞`) for some
`γ ∈ SL(2, ℤ)`. This file compares the normalized Fuchsian cusp datum width `D.width` at the
integral scaling `sl2zToPSL2R γ⁻¹` with Mathlib's projective width `widthInfty` of the conjugated
arithmetic subgroup `γ⁻¹ Γ γ`, and descends `Subgroup.IsRegularAtInfty` to a representative-
independent regularity predicate `Γ.IsRegularCusp C` on `(Γ.map sl2zToPSL2R).CuspOrbit`.

## Main definitions

* `Subgroup.IsRegularCusp`: regularity of a cusp orbit `C` of `Γ ≤ SL(2, ℤ)`.

## Main results

* `TauCeti.ModularForm.exists_int_eq_and_conj_mul_T_zpow_mem_of_mapGL_mul_upperRightHom_mem_conj`:
  if `mapGL ℝ s * upperRightHom w` lies in `γ⁻¹ Γ γ`, then `w` is an integer `j` and
  `γ (s Tʲ) γ⁻¹ ∈ Γ`, with `s = 1` and `s = -1` giving the positive and negative shift cases.
* `TauCeti.ModularForm.cuspDatum_width_eq_widthInfty`: at `D.scaling = sl2zToPSL2R γ⁻¹`, the datum
  width `D.width` equals the projective width `widthInfty` of `γ⁻¹ Γ γ`.
* `Subgroup.isRegularCusp_cuspOrbitOfSL2Z`: regularity of `Γ.cuspOrbitOfSL2Z γ` is regularity at `∞`
  of `γ⁻¹ Γ γ`.
* `Subgroup.isRegularCusp_of_neg_one_mem`: when `-I ∈ Γ`, every cusp orbit of `Γ` is regular.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §§2.4, 3.2.
-/

public section

open Matrix Matrix.SpecialLinearGroup MulAction OnePoint UpperHalfPlane
open scoped MatrixGroups ModularForm Pointwise

namespace TauCeti.ModularForm

section IntegralCuspDatum

variable {Γ : Subgroup SL(2, ℤ)}

/-- If `mapGL ℝ s * upperRightHom w` (`s ∈ SL(2, ℤ)`) belongs to the conjugated subgroup `γ⁻¹ Γ γ`,
then `w` is an integer `j` and `γ * (s * T ^ j) * γ⁻¹ ∈ Γ`. Specializing to `s = 1` and `s = -1`
covers both positive and negative shifts in `γ⁻¹ Γ γ`. -/
theorem exists_int_eq_and_conj_mul_T_zpow_mem_of_mapGL_mul_upperRightHom_mem_conj
    (γ s : SL(2, ℤ)) {w : ℝ}
    (hw : mapGL ℝ s * Matrix.GeneralLinearGroup.upperRightHom w ∈
      ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))) :
    ∃ j : ℤ, w = j ∧ γ * (s * ModularGroup.T ^ j) * γ⁻¹ ∈ Γ := by
  rw [Subgroup.mem_conj_mapGL_inv_iff] at hw
  obtain ⟨g, hg, hg_eq⟩ := Subgroup.mem_map.mp hw
  set u : SL(2, ℤ) := s⁻¹ * (γ⁻¹ * g * γ) with hu_def
  have hconj : mapGL ℝ u = Matrix.GeneralLinearGroup.upperRightHom w := by
    rw [hu_def, map_mul, map_inv, map_mul, map_mul, map_inv, hg_eq]
    group
  have hw_eq : w = (u 0 1 : ℝ) := by
    have h01 := congr_arg (fun M : GL (Fin 2) ℝ ↦ (M : Matrix (Fin 2) (Fin 2) ℝ) 0 1) hconj
    simpa [mapGL_coe_matrix, Matrix.GeneralLinearGroup.upperRightHom] using h01.symm
  have hT : u = ModularGroup.T ^ (u 0 1) :=
    mapGL_injective (S := ℝ) (by rw [hconj, hw_eq, ModularGroup.mapGL_T_zpow_eq_upperRightHom])
  have hj_mem : γ * (s * ModularGroup.T ^ (u 0 1)) * γ⁻¹ ∈ Γ := by
    have : γ * (s * u) * γ⁻¹ = g := by rw [hu_def]; group
    rwa [← hT, this]
  exact ⟨u 0 1, hw_eq, hj_mem⟩

/-- A positive shift `upperRightHom w` in `γ⁻¹ Γ γ` has integer translation `w = j` with
`γ * T ^ j * γ⁻¹ ∈ Γ`. -/
theorem exists_int_eq_and_conj_T_zpow_mem_of_upperRightHom_mem_conj (γ : SL(2, ℤ)) {w : ℝ}
    (hw : Matrix.GeneralLinearGroup.upperRightHom w ∈
      ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))) :
    ∃ j : ℤ, w = j ∧ γ * ModularGroup.T ^ j * γ⁻¹ ∈ Γ := by
  simpa only [one_mul] using
    exists_int_eq_and_conj_mul_T_zpow_mem_of_mapGL_mul_upperRightHom_mem_conj (Γ := Γ) γ 1
      (by simpa only [map_one, one_mul] using hw)

/-- A negative shift `-upperRightHom w` in `γ⁻¹ Γ γ` has integer translation `w = j` with
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
    D.width ∈
      (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).periods := by
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  obtain ⟨g₀, hg₀, hg₀_eq⟩ := Subgroup.mem_map.mp D.generator.2
  have hconj : sl2zToPSL2R (γ⁻¹ * g₀ * γ) =
      Matrix.ProjectiveSpecialLinearGroup.upperRightHom D.width := by
    simpa [map_mul, map_inv, hσ, hg₀_eq] using D.scaling_mul_generator_mul_inv
  rw [sl2zToPSL2R_apply, Matrix.ProjectiveSpecialLinearGroup.upperRightHom_apply,
    Matrix.ProjectiveSpecialLinearGroup.mk_eq_mk_iff] at hconj
  have hmem_conj : mapGL ℝ (γ⁻¹ * g₀ * γ) ∈ Γγ := by
    rw [Subgroup.mem_conj_mapGL_inv_iff]
    simpa [map_mul, map_inv, mul_assoc] using Subgroup.mem_map_of_mem (mapGL ℝ) hg₀
  rw [← mapGL_map_intCast (R := ℝ) (S := ℝ) (γ⁻¹ * g₀ * γ)] at hmem_conj
  rw [Subgroup.periods, Subgroup.mem_strictPeriods_iff, Subgroup.mem_adjoinNegOne_iff]
  rcases hconj with hpos | hneg
  · left
    rwa [← hpos, mapGL_transvection_eq_upperRightHom] at hmem_conj
  · right
    rwa [neg_eq_iff_eq_neg.mp hneg.symm, mapGL_neg,
      mapGL_transvection_eq_upperRightHom] at hmem_conj

private lemma exists_mem_sl2zToPSL2R_conj_eq_upperRightHom_of_mem_periods {γ : SL(2, ℤ)} {w : ℝ}
    (hw : w ∈ (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).periods) :
    ∃ g₁ ∈ Γ, sl2zToPSL2R (γ⁻¹ * g₁ * γ) =
      Matrix.ProjectiveSpecialLinearGroup.upperRightHom w := by
  rw [Subgroup.periods, Subgroup.mem_strictPeriods_iff, Subgroup.mem_adjoinNegOne_iff] at hw
  rcases hw with hp | hn
  · obtain ⟨j, rfl, hj⟩ := exists_int_eq_and_conj_T_zpow_mem_of_upperRightHom_mem_conj γ hp
    refine ⟨γ * ModularGroup.T ^ j * γ⁻¹, hj, ?_⟩
    have hconj : γ⁻¹ * (γ * ModularGroup.T ^ j * γ⁻¹) * γ = ModularGroup.T ^ j := by group
    rw [hconj, TauCeti.UpperHalfPlane.sl2zToPSL2R_T_zpow]
  · obtain ⟨j, rfl, hj⟩ := exists_int_eq_and_neg_conj_T_zpow_mem_of_neg_upperRightHom_mem_conj γ hn
    refine ⟨-(γ * ModularGroup.T ^ j * γ⁻¹), hj, ?_⟩
    have hconj : γ⁻¹ * -(γ * ModularGroup.T ^ j * γ⁻¹) * γ = -ModularGroup.T ^ j := by
      simp [mul_assoc]
    rw [hconj, sl2zToPSL2R_neg, TauCeti.UpperHalfPlane.sl2zToPSL2R_T_zpow]

private lemma widthInfty_mem_zmultiples_cuspDatum_width {D : (Γ.map sl2zToPSL2R).CuspDatum}
    {γ : SL(2, ℤ)} (hσ : D.scaling = sl2zToPSL2R γ⁻¹) :
    (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty ∈
      AddSubgroup.zmultiples D.width := by
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  obtain ⟨g₁, hg₁, hconj₁⟩ :=
    exists_mem_sl2zToPSL2R_conj_eq_upperRightHom_of_mem_periods Γγ.widthInfty_mem_periods
  have hconj₁' : D.scaling * sl2zToPSL2R g₁ * D.scaling⁻¹ =
      Matrix.ProjectiveSpecialLinearGroup.upperRightHom Γγ.widthInfty := by
    simpa [hσ, map_mul, map_inv] using hconj₁
  have hstab : (⟨sl2zToPSL2R g₁, Subgroup.mem_map_of_mem _ hg₁⟩ : Γ.map sl2zToPSL2R) ∈
      stabilizer (Γ.map sl2zToPSL2R) D.cusp := by
    rw [mem_stabilizer_iff, Subgroup.mk_smul]
    apply MulAction.injective D.scaling
    calc D.scaling • sl2zToPSL2R g₁ • D.cusp
        = (D.scaling * sl2zToPSL2R g₁ * D.scaling⁻¹) • D.scaling • D.cusp := by
            rw [mul_smul, mul_smul, inv_smul_smul]
      _ = D.scaling • D.cusp := by
            rw [hconj₁', D.scaling_smul_cusp,
              Matrix.ProjectiveSpecialLinearGroup.upperRightHom_smul_infty]
  obtain ⟨n, hn⟩ := D.mem_stabilizer_iff_conj.mp hstab
  rw [hconj₁'] at hn
  exact AddSubgroup.mem_zmultiples_iff.mpr
    ⟨n, by rw [zsmul_eq_mul, (Matrix.ProjectiveSpecialLinearGroup.upperRightHom_injective hn).symm]⟩

variable [Γ.FiniteIndex]

/-- If a normalized cusp datum `D` of `Γ.map sl2zToPSL2R` has scaling `sl2zToPSL2R γ⁻¹`, then its
cusp orbit is `Γ.cuspOrbitOfSL2Z γ`. -/
theorem cuspDatum_cuspOrbit_eq_of_scaling_eq {D : (Γ.map sl2zToPSL2R).CuspDatum} {γ : SL(2, ℤ)}
    (hσ : D.scaling = sl2zToPSL2R γ⁻¹) :
    D.cuspOrbit = Γ.cuspOrbitOfSL2Z γ := by
  apply Subtype.ext
  rw [D.cuspOrbit_val, Γ.cuspOrbitOfSL2Z_val, D.cusp_eq_inv_scaling_smul_infty, hσ, ← map_inv,
    inv_inv]

/-- **Compatibility of Fuchsian and arithmetic cusp widths.** At an integral scaling
`D.scaling = sl2zToPSL2R γ⁻¹`, the normalized Fuchsian cusp width `D.width` agrees with Mathlib's
projective width `widthInfty` of the conjugated arithmetic group `γ⁻¹ Γ γ`. -/
theorem cuspDatum_width_eq_widthInfty {D : (Γ.map sl2zToPSL2R).CuspDatum} {γ : SL(2, ℤ)}
    (hσ : D.scaling = sl2zToPSL2R γ⁻¹) :
    D.width =
      (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).widthInfty := by
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp
    (Γγ.periods_eq_zmultiples_widthInfty ▸ cuspDatum_width_mem_periods hσ)
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp
    (widthInfty_mem_zmultiples_cuspDatum_width hσ)
  rw [zsmul_eq_mul] at hm hn
  have hmn : (m : ℝ) * n = 1 := mul_right_cancel₀ D.width_pos.ne' <| by
    calc (m : ℝ) * n * D.width
        = m * (n * D.width) := mul_assoc _ _ _
      _ = m * Γγ.widthInfty := by rw [hn]
      _ = 1 * D.width := by rw [hm, one_mul]
  have hm_pos : 0 ≤ m := by
    have : (0 : ℝ) < m * Γγ.widthInfty := hm ▸ D.width_pos
    exact_mod_cast (pos_of_mul_pos_left this Γγ.widthInfty_pos.le).le
  have hm1 : m = 1 := Int.eq_one_of_mul_eq_one_right hm_pos (by exact_mod_cast hmn)
  rw [← hm, hm1, Int.cast_one, one_mul]

end IntegralCuspDatum

end TauCeti.ModularForm

namespace Subgroup

/-- **Regularity of a cusp orbit `C` of `Γ ≤ SL(2, ℤ)`.** A cusp orbit is regular when at every
integral matrix `γ ∈ SL(2, ℤ)` representing it, `∞` is a regular cusp of the conjugated subgroup
`γ⁻¹ Γ γ` (`Subgroup.IsRegularAtInfty`); `Subgroup.isRegularCusp_cuspOrbitOfSL2Z` shows that all
representatives agree. -/
def IsRegularCusp (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) : Prop :=
  ∀ γ : SL(2, ℤ), Γ.cuspOrbitOfSL2Z γ = C →
    (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsRegularAtInfty

/-- Unfolding `Subgroup.IsRegularCusp` across module boundaries. -/
theorem isRegularCusp_def (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    Γ.IsRegularCusp C ↔ ∀ γ : SL(2, ℤ), Γ.cuspOrbitOfSL2Z γ = C →
      (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsRegularAtInfty :=
  Iff.rfl

private lemma isRegularAtInfty_conj_of_cuspOrbitOfSL2Z_eq {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    {γ γ' : SL(2, ℤ)} (h : Γ.cuspOrbitOfSL2Z γ = Γ.cuspOrbitOfSL2Z γ') :
    (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsRegularAtInfty ↔
      (ConjAct.toConjAct (mapGL ℝ γ')⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsRegularAtInfty := by
  obtain ⟨g₀, hg₀, hc⟩ := (Γ.cuspOrbitOfSL2Z_eq_iff γ γ').mp h
  set m : SL(2, ℤ) := γ⁻¹ * g₀ * γ' with hm_def
  have hγ' : γ' = g₀⁻¹ * γ * m := by rw [hm_def]; group
  have hm_10 : (mapGL ℝ m) 1 0 = 0 := by
    simpa [mapGL_coe_matrix] using hc
  have hm_div : (mapGL ℝ m) 0 0 / (mapGL ℝ m) 1 1 = 1 := by
    have had : m 0 0 * m 1 1 = 1 := mul_apply_one_one_eq_one_of_apply_one_zero_eq_zero hc
    have heq : m 0 0 = m 1 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one had with h1 | h1
      · rw [h1, one_mul] at had
        rw [h1, had]
      · rw [h1, neg_one_mul, neg_eq_iff_eq_neg] at had
        rw [h1, had]
    have hd0 : ((m 1 1 : ℤ) : ℝ) ≠ 0 := by
      exact_mod_cast right_ne_zero_of_mul_eq_one had
    simpa [mapGL_coe_matrix, heq] using div_self hd0
  have hΓg₀ : ConjAct.toConjAct (mapGL ℝ g₀⁻¹)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ)) =
      (Γ : Subgroup (GL (Fin 2) ℝ)) := by
    rw [map_inv (mapGL ℝ), inv_inv]
    exact Subgroup.conjAct_pointwise_smul_eq_self
      (Subgroup.le_normalizer (Subgroup.mem_map_of_mem _ hg₀))
  have hconj : ConjAct.toConjAct (mapGL ℝ γ')⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ)) =
      ConjAct.toConjAct (mapGL ℝ m)⁻¹ •
        (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))) := by
    rw [hγ', map_mul, map_mul, _root_.mul_inv_rev, _root_.mul_inv_rev,
      ConjAct.toConjAct_mul, ConjAct.toConjAct_mul, mul_smul, mul_smul, hΓg₀]
  set Γγ := ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))
  have hsp : (ConjAct.toConjAct (mapGL ℝ m)⁻¹ • Γγ).strictPeriods = Γγ.strictPeriods := by
    ext x
    rw [Subgroup.mem_strictPeriods_conj_of_upperTriangular hm_10, hm_div, one_mul]
  have hp : (ConjAct.toConjAct (mapGL ℝ m)⁻¹ • Γγ).periods = Γγ.periods := by
    ext x
    rw [Subgroup.periods, Subgroup.periods, Subgroup.adjoinNegOne_conj,
      Subgroup.mem_strictPeriods_conj_of_upperTriangular hm_10, hm_div, one_mul]
  rw [hconj, Subgroup.IsRegularAtInfty, Subgroup.IsRegularAtInfty, hsp, hp]

/-- Regularity of `Γ.cuspOrbitOfSL2Z γ` is regularity at `∞` of `γ⁻¹ Γ γ`. -/
@[simp]
theorem isRegularCusp_cuspOrbitOfSL2Z (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (γ : SL(2, ℤ)) :
    Γ.IsRegularCusp (Γ.cuspOrbitOfSL2Z γ) ↔
      (ConjAct.toConjAct (mapGL ℝ γ)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ))).IsRegularAtInfty :=
  ⟨fun h ↦ h γ rfl, fun h _ hγ' ↦
    (isRegularAtInfty_conj_of_cuspOrbitOfSL2Z_eq hγ'.symm).mp h⟩

/-- When `-I ∈ Γ`, every cusp orbit of `Γ` is regular. -/
theorem isRegularCusp_of_neg_one_mem (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (h : (-1 : SL(2, ℤ)) ∈ Γ) (C : (Γ.map sl2zToPSL2R).CuspOrbit) :
    Γ.IsRegularCusp C := by
  obtain ⟨γ, rfl⟩ := Γ.cuspOrbitOfSL2Z_surjective C
  rw [isRegularCusp_cuspOrbitOfSL2Z]
  refine Subgroup.isRegularAtInfty_of_neg_one_mem
    (Subgroup.mem_conjAct_smul_of_mem_center (Subgroup.mem_center_iff.mpr fun _ ↦ by simp)
      (mapGL ℝ γ)⁻¹ ?_)
  rw [← Matrix.SpecialLinearGroup.mapGL_neg_one (R := ℤ)]
  exact Subgroup.mem_map_of_mem (mapGL ℝ) h

end Subgroup

end
