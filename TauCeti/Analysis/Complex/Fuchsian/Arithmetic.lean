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
orbit into several cusp orbits: every cusp orbit is that of `γ • ∞` for some `γ ∈ SL(2, ℤ)`,
and two such orbits agree exactly when `γ⁻¹ h γ'` fixes `∞` for some `h` in the subgroup.
These facts allow the compactified Fuchsian quotient and its cusp charts to be used for
congruence modular curves, and reduce counting cusps to arithmetic in `SL(2, ℤ)`; in
particular there are finitely many cusp orbits.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §§2.3–2.4.
-/

public noncomputable section

open Matrix Matrix.ProjectiveSpecialLinearGroup MulAction OnePoint Subgroup
open scoped MatrixGroups

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

/-- Multiplying the representative on the left by an element of `H` does not change the cusp
orbit. -/
@[simp]
theorem cuspOrbitOfSL2Z_mul_left {h : SL(2, ℤ)} (hh : h ∈ H) (γ : SL(2, ℤ)) :
    H.cuspOrbitOfSL2Z (h * γ) = H.cuspOrbitOfSL2Z γ :=
  (H.cuspOrbitOfSL2Z_eq_iff _ _).mpr ⟨h, hh, by simp⟩

/-- A finite-index subgroup of `SL(2, ℤ)` has finitely many cusp orbits: the cusp orbit of
`γ • ∞` depends only on the coset `H γ`, and there are finitely many such cosets. -/
instance finite_cuspOrbit_map_sl2zToPSL2R : Finite (H.map sl2zToPSL2R).CuspOrbit := by
  let f : SL(2, ℤ) ⧸ H → (H.map sl2zToPSL2R).CuspOrbit :=
    Quotient.lift (fun γ ↦ H.cuspOrbitOfSL2Z γ⁻¹) fun γ γ' hγ ↦ by
      rw [show γ⁻¹ = γ⁻¹ * γ' * γ'⁻¹ by group,
        H.cuspOrbitOfSL2Z_mul_left (QuotientGroup.leftRel_apply.mp hγ)]
  refine Finite.of_surjective f fun C ↦ ?_
  obtain ⟨γ, rfl⟩ := H.cuspOrbitOfSL2Z_surjective C
  exact ⟨QuotientGroup.mk γ⁻¹, by simp [f]⟩

end Subgroup
