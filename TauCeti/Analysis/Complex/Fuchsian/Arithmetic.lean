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

The image in `PSL(2, ℝ)` of a subgroup `H ≤ SL(2, ℤ)` has index `[SL(2, ℤ) : ±H]` in the
image of the full modular group, since `{±I}` acts trivially.

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

omit [H.FiniteIndex] in
/-- **The arithmetic index of a modular subgroup.** The image of `H ≤ SL(2, ℤ)` in `PSL(2, ℝ)`
has index `[SL(2, ℤ) : ±H]` in the image of `SL(2, ℤ)`, since `sl2zToPSL2R` has kernel `{±I}`. -/
theorem relIndex_map_sl2zToPSL2R :
    (H.map sl2zToPSL2R).relIndex psl2zToPSL2R.range = H.withCenter.index := by
  rw [← TauCeti.range_sl2zToPSL2R_eq_range_psl2zToPSL2R, ← index_comap, comap_map_eq,
    sl2zToPSL2R_ker, withCenter_def]

/-- A finite-index subgroup of `SL(2, ℤ)` has finite-index image in the level-one group. -/
instance isFiniteRelIndex_map_sl2zToPSL2R :
    (H.map sl2zToPSL2R).IsFiniteRelIndex psl2zToPSL2R.range :=
  ⟨H.relIndex_map_sl2zToPSL2R ▸ FiniteIndex.index_ne_zero⟩

/-- A finite-index subgroup of `SL(2, ℤ)` has cofinite effective image in `PSL(2, ℝ)`.
This formulation applies directly to `Γ(N)`, `Γ₀(N)`, and `Γ₁(N)`. -/
theorem isCofinite_map_sl2zToPSL2R :
    (H.map sl2zToPSL2R).IsCofinite := by
  apply (Subgroup.isCofinite_iff_isCofinite_and_finiteIndex H.map_sl2zToPSL2R_le_range).mpr
  exact ⟨TauCeti.ModularGroup.isCofinite_psl2zToPSL2RRange,
    Subgroup.isFiniteRelIndex_iff_finiteIndex.mp inferInstance⟩

/-- The parabolic fixed points of a finite-index integral modular subgroup are the
rational boundary points, described as the full modular orbit of infinity. -/
theorem isCuspPoint_map_sl2zToPSL2R_iff_orbit_infty (c : OnePoint ℝ) :
    (H.map sl2zToPSL2R).IsCuspPoint c ↔
      c ∈ orbit psl2zToPSL2R.range (∞ : OnePoint ℝ) := by
  rw [Subgroup.isCuspPoint_iff_of_isFiniteRelIndex H.map_sl2zToPSL2R_le_range]
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
  (Subgroup.isCuspPoint_iff_of_isFiniteRelIndex H.map_sl2zToPSL2R_le_range).trans
    ((TauCeti.ModularGroup.isCuspPoint_iff_isCusp c).trans isCusp_SL2Z_iff)

end Subgroup
