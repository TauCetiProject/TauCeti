/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.LevelOne
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.FiniteIndex

/-!
# Finite-index modular groups as cofinite Fuchsian groups

Every finite-index subgroup of `SL(2, ℤ)` gives a cofinite subgroup of `PSL(2, ℝ)`.
Its parabolic fixed points are exactly the rational boundary points: equivalently, the
orbit of infinity under the full modular group. The subgroup can split this one modular
orbit into several cusp orbits. These facts allow the compactified Fuchsian quotient and
its cusp charts to be used for congruence modular curves.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §§2.3–2.4.
-/

public noncomputable section

open Matrix Matrix.ProjectiveSpecialLinearGroup MulAction OnePoint Subgroup
open scoped MatrixGroups

namespace Subgroup

variable (H : Subgroup SL(2, ℤ)) [H.FiniteIndex]

private theorem finiteRelIndex_map_sl2zToPSL2R :
    (H.map sl2zToPSL2R).IsFiniteRelIndex psl2zToPSL2R.range := by
  have htop : (⊤ : Subgroup SL(2, ℤ)).map sl2zToPSL2R =
      psl2zToPSL2R.range := by
    rw [← TauCeti.range_sl2zToPSL2R_eq_range_psl2zToPSL2R]
    ext x
    simp
  rw [← htop]
  have hH : H.IsFiniteRelIndex (⊤ : Subgroup SL(2, ℤ)) :=
    Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr inferInstance
  exact hH.map sl2zToPSL2R

/-- A finite-index subgroup of `SL(2, ℤ)` has cofinite effective image in `PSL(2, ℝ)`.
This formulation applies directly to `Γ(N)`, `Γ₀(N)`, and `Γ₁(N)`. -/
theorem isCofinite_map_sl2zToPSL2R :
    (H.map sl2zToPSL2R).IsCofinite := by
  have hle : H.map sl2zToPSL2R ≤ psl2zToPSL2R.range := by
    rw [← TauCeti.range_sl2zToPSL2R_eq_range_psl2zToPSL2R]
    exact Subgroup.map_le_range sl2zToPSL2R H
  apply (Subgroup.isCofinite_iff_isCofinite_and_finiteIndex hle).mpr
  exact ⟨TauCeti.ModularGroup.isCofinite_psl2zToPSL2RRange,
    Subgroup.isFiniteRelIndex_iff_finiteIndex.mp (finiteRelIndex_map_sl2zToPSL2R H)⟩

/-- The parabolic fixed points of a finite-index integral modular subgroup are the
rational boundary points, described as the full modular orbit of infinity. -/
theorem isCuspPoint_map_sl2zToPSL2R_iff_orbit_infty (c : OnePoint ℝ) :
    (H.map sl2zToPSL2R).IsCuspPoint c ↔
      c ∈ orbit psl2zToPSL2R.range (∞ : OnePoint ℝ) := by
  have hle : H.map sl2zToPSL2R ≤ psl2zToPSL2R.range := by
    rw [← TauCeti.range_sl2zToPSL2R_eq_range_psl2zToPSL2R]
    exact Subgroup.map_le_range sl2zToPSL2R H
  let _ : (H.map sl2zToPSL2R).IsFiniteRelIndex psl2zToPSL2R.range :=
    finiteRelIndex_map_sl2zToPSL2R H
  rw [Subgroup.isCuspPoint_iff_of_isFiniteRelIndex hle]
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
      c ∈ Set.range (OnePoint.map Rat.cast) := by
  have hle : H.map sl2zToPSL2R ≤ psl2zToPSL2R.range := by
    rw [← TauCeti.range_sl2zToPSL2R_eq_range_psl2zToPSL2R]
    exact Subgroup.map_le_range sl2zToPSL2R H
  let _ : (H.map sl2zToPSL2R).IsFiniteRelIndex psl2zToPSL2R.range :=
    finiteRelIndex_map_sl2zToPSL2R H
  exact (Subgroup.isCuspPoint_iff_of_isFiniteRelIndex hle).trans
    ((TauCeti.ModularGroup.isCuspPoint_iff_isCusp c).trans isCusp_SL2Z_iff)

end Subgroup
