/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.Cusps
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.LevelOne
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Finite
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.FiniteIndex
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation
import TauCeti.GroupTheory.GroupAction.ConjAct
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import TauCeti.NumberTheory.Modular.ConjugateTranslation

/-!
# Finite-index modular groups as cofinite Fuchsian groups

Every finite-index subgroup of `SL(2, ℤ)` gives a cofinite subgroup of `PSL(2, ℝ)`.
Its parabolic fixed points are exactly the rational boundary points: equivalently, the
orbit of infinity under the full modular group. The subgroup can split this one modular
orbit into several cusp orbits: every cusp orbit is that of `γ • ∞` for some `γ ∈ SL(2, ℤ)`,
and two such orbits agree exactly when `γ⁻¹ h γ'` fixes `∞` for some `h` in the subgroup.
These facts allow the compactified Fuchsian quotient and its cusp charts to be used for
congruence modular curves, and reduce counting cusps to arithmetic in `SL(2, ℤ)`; in
particular there are finitely many cusp orbits.
It also identifies the Fuchsian cusp datum width `D.width` and orbit `D.cuspOrbit` at an
integral scaling `sl2zToPSL2R γ⁻¹` with `widthInfty` of `γ⁻¹ Γ γ` and `Γ.cuspOrbitOfSL2Z γ`.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §§2.3–2.4.
-/

public noncomputable section

open Matrix Matrix.ProjectiveSpecialLinearGroup Matrix.SpecialLinearGroup MulAction OnePoint
  Subgroup
open scoped MatrixGroups Pointwise

namespace Subgroup

variable (H : Subgroup SL(2, ℤ)) [H.FiniteIndex]

/-- A finite-index subgroup of `SL(2, ℤ)` has cofinite effective image in `PSL(2, ℝ)`.
This formulation applies directly to `Γ(N)`, `Γ₀(N)`, and `Γ₁(N)`. -/
theorem isCofinite_map_sl2zToPSL2R :
    (H.map sl2zToPSL2R).IsCofinite := by
  apply (Subgroup.isCofinite_iff_isCofinite_and_finiteIndex
    H.map_sl2zToPSL2R_le_range_psl2zToPSL2R).mpr
  exact ⟨TauCeti.ModularGroup.isCofinite_psl2zToPSL2RRange,
    Subgroup.isFiniteRelIndex_iff_finiteIndex.mp inferInstance⟩

/-- The parabolic fixed points of a finite-index integral modular subgroup are the
rational boundary points, described as the full modular orbit of infinity. -/
theorem isCuspPoint_map_sl2zToPSL2R_iff_orbit_infty (c : OnePoint ℝ) :
    (H.map sl2zToPSL2R).IsCuspPoint c ↔
      c ∈ orbit psl2zToPSL2R.range (∞ : OnePoint ℝ) := by
  rw [Subgroup.isCuspPoint_iff_of_isFiniteRelIndex
    H.map_sl2zToPSL2R_le_range_psl2zToPSL2R]
  constructor
  · exact TauCeti.ModularGroup.cuspPoint_mem_orbit_infty
  · intro hc
    obtain ⟨g, hg⟩ := mem_orbit_iff.mp hc
    rw [← hg]
    exact TauCeti.ModularGroup.isCuspPoint_infty.smul g

/-- The cusp points of a finite-index subgroup of `SL(2, ℤ)` are exactly the image of
`ℙ¹(ℚ)` in the real projective boundary. -/
theorem isCuspPoint_map_sl2zToPSL2R_iff_rat (c : OnePoint ℝ) :
    (H.map sl2zToPSL2R).IsCuspPoint c ↔
      c ∈ Set.range (OnePoint.map Rat.cast) :=
  (Subgroup.isCuspPoint_iff_of_isFiniteRelIndex
    H.map_sl2zToPSL2R_le_range_psl2zToPSL2R).trans
    ((TauCeti.ModularGroup.isCuspPoint_iff_isCusp c).trans isCusp_SL2Z_iff)

/-- The point `γ • ∞` of the projective boundary is a cusp point of the effective image of a
finite-index subgroup of `SL(2, ℤ)`. -/
theorem isCuspPoint_map_sl2zToPSL2R_smul_infty (γ : SL(2, ℤ)) :
    (H.map sl2zToPSL2R).IsCuspPoint (sl2zToPSL2R γ • (∞ : OnePoint ℝ)) := by
  rw [isCuspPoint_map_sl2zToPSL2R_iff_orbit_infty]
  exact mem_orbit_iff.mpr ⟨⟨sl2zToPSL2R γ,
    TauCeti.range_sl2zToPSL2R_eq_range_psl2zToPSL2R ▸ ⟨γ, rfl⟩⟩, rfl⟩

/-- The cusp orbit of `γ • ∞` for the effective image of a finite-index subgroup `H` of
`SL(2, ℤ)`. -/
def cuspOrbitOfSL2Z (γ : SL(2, ℤ)) : (H.map sl2zToPSL2R).CuspOrbit :=
  (H.map sl2zToPSL2R).cuspOrbitMk
    ⟨sl2zToPSL2R γ • ∞, mem_cuspPoints.mpr (H.isCuspPoint_map_sl2zToPSL2R_smul_infty γ)⟩

/-- The cusp orbit of `γ • ∞`, as a boundary orbit. -/
@[simp]
theorem cuspOrbitOfSL2Z_val (γ : SL(2, ℤ)) :
    (H.cuspOrbitOfSL2Z γ : (H.map sl2zToPSL2R).BoundaryOrbit) =
      Quotient.mk'' (sl2zToPSL2R γ • (∞ : OnePoint ℝ)) :=
  cuspOrbitMk_val _

/-- Every cusp orbit of a finite-index subgroup of `SL(2, ℤ)` is the orbit of `γ • ∞` for some
`γ ∈ SL(2, ℤ)`. -/
theorem cuspOrbitOfSL2Z_surjective : Function.Surjective H.cuspOrbitOfSL2Z := by
  intro C
  obtain ⟨⟨c, hc⟩, rfl⟩ := cuspOrbitMk_surjective C
  obtain ⟨⟨_, p, rfl⟩, rfl⟩ := mem_orbit_iff.mp
    ((isCuspPoint_map_sl2zToPSL2R_iff_orbit_infty H c).mp (mem_cuspPoints.mp hc))
  induction p using QuotientGroup.induction_on with
  | H γ => exact ⟨γ, by simp [cuspOrbitOfSL2Z]⟩

/-- **The cusp orbits of `γ • ∞` and `γ' • ∞` agree** exactly when `γ⁻¹ h γ'` fixes `∞`, that is
has vanishing lower-left entry, for some `h ∈ H`. -/
theorem cuspOrbitOfSL2Z_eq_iff (γ γ' : SL(2, ℤ)) :
    H.cuspOrbitOfSL2Z γ = H.cuspOrbitOfSL2Z γ' ↔ ∃ h ∈ H, (γ⁻¹ * h * γ') 1 0 = 0 := by
  have key (h : SL(2, ℤ)) : sl2zToPSL2R h • sl2zToPSL2R γ' • (∞ : OnePoint ℝ) =
      sl2zToPSL2R γ • ∞ ↔ (γ⁻¹ * h * γ') 1 0 = 0 := by
    rw [← TauCeti.sl2zToPSL2R_smul_infty_eq_infty_iff, map_mul, map_mul, map_inv, mul_smul,
      mul_smul, inv_smul_eq_iff]
  rw [cuspOrbitOfSL2Z, cuspOrbitOfSL2Z, cuspOrbitMk_eq_iff, mem_orbit_iff]
  simp only [Subtype.exists, Subgroup.mk_smul, Subgroup.mem_map, exists_prop]
  constructor
  · rintro ⟨_, ⟨h, hh, rfl⟩, hγ⟩
    exact ⟨h, hh, (key h).mp hγ⟩
  · rintro ⟨h, hh, hγ⟩
    exact ⟨_, ⟨h, hh, rfl⟩, (key h).mpr hγ⟩

/-- The matrices `γ` and `-γ` represent the same cusp orbit. -/
@[simp]
theorem cuspOrbitOfSL2Z_neg (γ : SL(2, ℤ)) : H.cuspOrbitOfSL2Z (-γ) = H.cuspOrbitOfSL2Z γ :=
  (H.cuspOrbitOfSL2Z_eq_iff _ _).mpr ⟨1, H.one_mem, by simp⟩

/-- A finite-index subgroup of `SL(2, ℤ)` has finitely many cusp orbits, since its image in
`PSL(2, ℝ)` is cofinite. -/
instance finite_cuspOrbit_map_sl2zToPSL2R : Finite (H.map sl2zToPSL2R).CuspOrbit :=
  H.isCofinite_map_sl2zToPSL2R.finite_cuspOrbit

end Subgroup

namespace TauCeti

section IntegralCuspDatum

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

end TauCeti

end
