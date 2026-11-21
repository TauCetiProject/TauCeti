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
import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.Cofinite
import TauCeti.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Modular subgroups in `PSL(2, ℝ)` and their cusps

For any subgroup `Γ' ≤ PSL(2, ℤ)`, the Fuchsian cusp points and cusp orbits of `Γ'.map psl2zToPSL2R`
agree with Mathlib's `IsCusp` and `CuspOrbits` for `Γ'.liftSL ≤ SL(2, ℤ)`
(`Subgroup.isCuspPoint_map_psl2zToPSL2R_iff_isCusp`, `Subgroup.fuchsianCuspOrbitEquivCuspOrbits`).

Every finite-index subgroup of `SL(2, ℤ)` or `PSL(2, ℤ)` gives a cofinite subgroup of
`PSL(2, ℝ)`, with compact cusp compactification.
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
open scoped MatrixGroups Modular

namespace Subgroup

/-- For any `Γ' ≤ PSL(2, ℤ)`, the Fuchsian cusp points of `Γ'.map psl2zToPSL2R` are exactly
Mathlib's cusps of `Γ'.liftSL ≤ SL(2, ℤ)`. -/
theorem isCuspPoint_map_psl2zToPSL2R_iff_isCusp (Γ' : Subgroup PSL(2, ℤ)) (c : OnePoint ℝ) :
    (Γ'.map psl2zToPSL2R).IsCuspPoint c ↔ IsCusp c (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) := by
  constructor
  · intro hc
    obtain ⟨⟨_, g, hg, rfl⟩, hfix, hpar⟩ :=
      Subgroup.isCuspPoint_iff_exists_mem_stabilizer_isParabolic.mp hc
    induction g using QuotientGroup.induction_on with
    | H a =>
      exact ⟨Matrix.SpecialLinearGroup.mapGL ℝ a,
        Subgroup.mem_map_of_mem _ (Subgroup.mem_liftSL.mpr hg),
        (TauCeti.isParabolic_psl2zToPSL2R_iff a).mp hpar,
        (TauCeti.psl2zToPSL2R_smul_boundary a c) ▸ (mem_stabilizer_iff.mp hfix)⟩
  · rintro ⟨p, hp, hpar, hfix⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hp
    apply Subgroup.isCuspPoint_iff_exists_mem_stabilizer_isParabolic.mpr
    refine ⟨⟨psl2zToPSL2R (a : PSL(2, ℤ)),
      Subgroup.mem_map_of_mem _ (Subgroup.mem_liftSL.mp ha)⟩, ?_, ?_⟩
    · exact mem_stabilizer_iff.mpr (by
        simpa only [MulAction.subgroup_smul_def, TauCeti.psl2zToPSL2R_smul_boundary] using hfix)
    · exact (TauCeti.isParabolic_psl2zToPSL2R_iff a).mpr hpar

private theorem mem_orbit_map_psl2zToPSL2R_iff (Γ' : Subgroup PSL(2, ℤ)) (c₁ c₂ : OnePoint ℝ) :
    c₁ ∈ orbit (Γ'.map psl2zToPSL2R) c₂ ↔
      c₁ ∈ orbit (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) c₂ := by
  simp only [mem_orbit_iff, Subtype.exists, Subgroup.smul_def]
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, hsmul⟩
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective g
    exact ⟨Matrix.SpecialLinearGroup.mapGL ℝ γ,
      Subgroup.mem_map_of_mem _ (Subgroup.mem_liftSL.mpr hg),
      by rwa [← TauCeti.psl2zToPSL2R_smul_boundary]⟩
  · rintro ⟨_, ⟨γ, hγ, rfl⟩, hsmul⟩
    exact ⟨psl2zToPSL2R (γ : PSL(2, ℤ)),
      Subgroup.mem_map_of_mem _ (Subgroup.mem_liftSL.mp hγ),
      by rwa [TauCeti.psl2zToPSL2R_smul_boundary]⟩

/-- **Fuchsian vs. Mathlib cusp orbits.** For any `Γ' ≤ PSL(2, ℤ)`, the Fuchsian cusp orbits
`(Γ'.map psl2zToPSL2R).CuspOrbit` biject onto Mathlib's `CuspOrbits Γ'.liftSL`. -/
def fuchsianCuspOrbitEquivCuspOrbits (Γ' : Subgroup PSL(2, ℤ)) :
    (Γ'.map psl2zToPSL2R).CuspOrbit ≃ CuspOrbits (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) :=
  let invFun : CuspOrbits (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ)) →
      (Γ'.map psl2zToPSL2R).CuspOrbit :=
    Quotient.lift
      (fun c ↦ (Γ'.map psl2zToPSL2R).cuspOrbitMk ⟨c.val, Subgroup.mem_cuspPoints.mpr
        ((isCuspPoint_map_psl2zToPSL2R_iff_isCusp Γ' c.val).mpr
          (mem_cuspsSubMulAction.mp c.property))⟩)
      fun _ _ h ↦ by
        rw [Subgroup.cuspOrbitMk_eq_iff, mem_orbit_map_psl2zToPSL2R_iff]
        obtain ⟨g, hg⟩ := mem_orbit_iff.mp (orbitRel_apply.mp h)
        exact mem_orbit_iff.mpr ⟨g, congrArg Subtype.val hg⟩
  (Equiv.ofBijective invFun
    ⟨fun a b hab ↦ by
      induction a using Quotient.inductionOn with | h c₁ =>
      induction b using Quotient.inductionOn with | h c₂ =>
      dsimp only [invFun] at hab
      rw [Quotient.lift_mk, Quotient.lift_mk, Subgroup.cuspOrbitMk_eq_iff,
        mem_orbit_map_psl2zToPSL2R_iff] at hab
      obtain ⟨g, hg⟩ := mem_orbit_iff.mp hab
      exact Quotient.sound (orbitRel_apply.mpr (mem_orbit_iff.mpr ⟨g, Subtype.ext hg⟩)),
    fun C ↦ by
      obtain ⟨c, rfl⟩ := Subgroup.cuspOrbitMk_surjective C
      exact ⟨Quotient.mk'' ⟨c.val, mem_cuspsSubMulAction.mpr
        ((isCuspPoint_map_psl2zToPSL2R_iff_isCusp Γ' c.val).mp
          (Subgroup.mem_cuspPoints.mp c.property))⟩, rfl⟩⟩).symm

/-- `fuchsianCuspOrbitEquivCuspOrbits` sends a Mathlib cusp orbit back to the corresponding
Fuchsian cusp orbit. -/
@[simp]
theorem fuchsianCuspOrbitEquivCuspOrbits_symm_mk (Γ' : Subgroup PSL(2, ℤ))
    (c : cuspsSubMulAction (Γ'.liftSL : Subgroup (GL (Fin 2) ℝ))) :
    (fuchsianCuspOrbitEquivCuspOrbits Γ').symm (Quotient.mk'' c) =
      (Γ'.map psl2zToPSL2R).cuspOrbitMk ⟨c.val, Subgroup.mem_cuspPoints.mpr
        ((isCuspPoint_map_psl2zToPSL2R_iff_isCusp Γ' c.val).mpr
          (mem_cuspsSubMulAction.mp c.property))⟩ :=
  (rfl)

/-- `fuchsianCuspOrbitEquivCuspOrbits` sends the Fuchsian cusp orbit of `c` to the Mathlib cusp
orbit of `c`. -/
@[simp]
theorem fuchsianCuspOrbitEquivCuspOrbits_cuspOrbitMk (Γ' : Subgroup PSL(2, ℤ))
    (c : (Γ'.map psl2zToPSL2R).cuspPoints) :
    fuchsianCuspOrbitEquivCuspOrbits Γ' ((Γ'.map psl2zToPSL2R).cuspOrbitMk c) =
      Quotient.mk'' ⟨c.val, mem_cuspsSubMulAction.mpr
        ((isCuspPoint_map_psl2zToPSL2R_iff_isCusp Γ' c.val).mp
          (Subgroup.mem_cuspPoints.mp c.property))⟩ :=
  (Equiv.eq_symm_apply _).mp rfl

variable (H : Subgroup SL(2, ℤ)) [H.FiniteIndex]

/-- A finite-index subgroup of `SL(2, ℤ)` has cofinite effective image in `PSL(2, ℝ)`.
This formulation applies directly to `Γ(N)`, `Γ₀(N)`, and `Γ₁(N)`. -/
theorem isCofinite_map_sl2zToPSL2R :
    (H.map sl2zToPSL2R).IsCofinite := by
  apply (Subgroup.isCofinite_iff_isCofinite_and_finiteIndex
    H.map_sl2zToPSL2R_le_range_psl2zToPSL2R).mpr
  exact ⟨TauCeti.ModularGroup.isCofinite_psl2zToPSL2RRange,
    Subgroup.isFiniteRelIndex_iff_finiteIndex.mp inferInstance⟩

/-- A finite-index subgroup of `PSL(2, ℤ)` has cofinite effective image in `PSL(2, ℝ)`. -/
theorem isCofinite_map_psl2zToPSL2R (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex] :
    (Γ'.map psl2zToPSL2R).IsCofinite := by
  rw [← Γ'.map_liftSL_sl2zToPSL2R]
  exact Γ'.liftSL.isCofinite_map_sl2zToPSL2R

/-- The compactified modular curve `X(Γ')` of a finite-index `Γ' ≤ PSL(2, ℤ)` is compact. -/
theorem compactSpace_compactifiedQuotient_map_psl2zToPSL2R (Γ' : Subgroup PSL(2, ℤ))
    [Γ'.FiniteIndex] : CompactSpace (Γ'.map psl2zToPSL2R).CompactifiedQuotient :=
  (isCofinite_map_psl2zToPSL2R Γ').compactSpace_compactifiedQuotient

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

/-- The point `psl2zToPSL2R g • ∞` of the projective boundary is a cusp point of the effective
image of a finite-index subgroup of `PSL(2, ℤ)`. -/
theorem isCuspPoint_map_psl2zToPSL2R_smul_infty (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex]
    (g : PSL(2, ℤ)) :
    (Γ'.map psl2zToPSL2R).IsCuspPoint (psl2zToPSL2R g • (∞ : OnePoint ℝ)) := by
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective g
  rw [← Γ'.map_liftSL_sl2zToPSL2R, psl2zToPSL2R_mk]
  exact Γ'.liftSL.isCuspPoint_map_sl2zToPSL2R_smul_infty γ

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
