/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.Cusps
public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
import TauCeti.GroupTheory.GroupAction.ConjAct
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Regularity of cusp orbits

For finite-index `Γ ≤ SL(2, ℤ)`, this file descends `Subgroup.IsRegularAtInfty` to
`Γ.IsRegularCusp` on `(Γ.map sl2zToPSL2R).CuspOrbit` and records invariance across integral
representatives `γ ∈ SL(2, ℤ)` and automatic regularity when `-I ∈ Γ`.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], §§2.4, 3.2.
-/

public section

open Matrix Matrix.SpecialLinearGroup MulAction OnePoint UpperHalfPlane
open scoped MatrixGroups ModularForm Pointwise

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
