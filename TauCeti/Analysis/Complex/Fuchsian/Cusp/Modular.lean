/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ModularForms.Cusps
public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Basic

/-!
# Comparison between Fuchsian and Mathlib modular cusps

For any subgroup `Γ' ≤ PSL(2, ℤ)`, the Fuchsian cusp points and cusp orbits of
`Γ'.map psl2zToPSL2R ≤ PSL(2, ℝ)` agree with Mathlib's `IsCusp` and `CuspOrbits` for
`Γ'.liftSL ≤ SL(2, ℤ)`.

## Main statements

* `Subgroup.isCuspPoint_map_psl2zToPSL2R_iff_isCusp`: Fuchsian cusp points of `Γ'.map psl2zToPSL2R`
  coincide with Mathlib's cusps of `Γ'.liftSL`.
* `Subgroup.fuchsianCuspOrbitEquivCuspOrbits`: bijection between `(Γ'.map psl2zToPSL2R).CuspOrbit`
  and `CuspOrbits Γ'.liftSL`.
-/

public noncomputable section

open Matrix Matrix.ProjectiveSpecialLinearGroup MulAction OnePoint
open scoped MatrixGroups

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

end Subgroup
