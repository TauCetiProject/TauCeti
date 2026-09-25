/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Compactness
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.Cusps

/-!
# Compactness of the level-one modular compactification

The modular group has one cusp orbit, represented by infinity. Its standard closed fundamental
domain has a compact truncation at each height. These two facts turn the general compactness
criterion for Fuchsian compactifications into compactness of the level-one carrier.

Mathlib's `ModularGroup.isCompact_truncatedFundamentalDomain` supplies the geometric compact
set, and `isCusp_SL2Z_iff'` supplies the classification of modular cusps.

## Main results

* `TauCeti.ModularGroup.cuspOrbitInfty` and `instUniqueCuspOrbit`: the unique modular cusp orbit.
* `TauCeti.ModularGroup.compactSpace_compactifiedQuotient`: compactness of the level-one
  compactified quotient.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §2.4.
-/

public section

noncomputable section

open Matrix Matrix.ProjectiveSpecialLinearGroup Matrix.SpecialLinearGroup MulAction OnePoint Set
  TauCeti.Subgroup.CuspDatum UpperHalfPlane
open scoped MatrixGroups Modular

namespace TauCeti.ModularGroup

private theorem psl2zToPSL2R_smul_boundary (a : SL(2, ℤ)) (c : OnePoint ℝ) :
    psl2zToPSL2R (a : PSL(2, ℤ)) • c = mapGL ℝ a • c := by
  rw [psl2zToPSL2R_mk, sl2zToPSL2R_apply, OnePoint.pslMk_smul]
  rfl

private theorem isParabolic_psl2zToPSL2R_iff (a : SL(2, ℤ)) :
    IsParabolic (psl2zToPSL2R (a : PSL(2, ℤ))) ↔ (mapGL ℝ a).IsParabolic := by
  rw [psl2zToPSL2R_mk, sl2zToPSL2R_apply, isParabolic_mk_iff]
  rfl

private theorem isCuspPoint_iff_isCusp (c : OnePoint ℝ) :
    psl2zToPSL2R.range.IsCuspPoint c ↔ _root_.IsCusp c 𝒮ℒ := by
  constructor
  · intro hc
    obtain ⟨⟨p, hp⟩, hfix, hpar⟩ :=
      (Subgroup.isCuspPoint_iff_exists_mem_stabilizer_isParabolic).mp hc
    obtain ⟨a, rfl⟩ := hp
    induction a using QuotientGroup.induction_on with
    | H a =>
      exact ⟨mapGL ℝ a, ⟨a, rfl⟩,
        (isParabolic_psl2zToPSL2R_iff a).mp hpar,
        (psl2zToPSL2R_smul_boundary a c) ▸ (mem_stabilizer_iff.mp hfix)⟩
  · rintro ⟨p, ⟨a, rfl⟩, hpar, hfix⟩
    apply (Subgroup.isCuspPoint_iff_exists_mem_stabilizer_isParabolic).mpr
    refine ⟨⟨psl2zToPSL2R (a : PSL(2, ℤ)), ⟨a, rfl⟩⟩, ?_, ?_⟩
    · exact mem_stabilizer_iff.mpr (by
        simpa only [MulAction.subgroup_smul_def, psl2zToPSL2R_smul_boundary] using hfix)
    · exact (isParabolic_psl2zToPSL2R_iff a).mpr hpar

/-- Every cusp of the effective level-one modular group is equivalent to infinity. -/
theorem cuspPoint_mem_orbit_infty {c : OnePoint ℝ}
    (hc : psl2zToPSL2R.range.IsCuspPoint c) :
    c ∈ orbit psl2zToPSL2R.range (∞ : OnePoint ℝ) := by
  obtain ⟨a, ha⟩ := (_root_.isCusp_SL2Z_iff').mp ((isCuspPoint_iff_isCusp c).mp hc)
  refine mem_orbit_iff.mpr ⟨⟨psl2zToPSL2R (a : PSL(2, ℤ)), ⟨a, rfl⟩⟩, ?_⟩
  simpa only [MulAction.subgroup_smul_def, psl2zToPSL2R_smul_boundary] using ha.symm

/-- Infinity is a cusp point of the effective level-one modular group. -/
theorem isCuspPoint_infty :
    psl2zToPSL2R.range.IsCuspPoint (∞ : OnePoint ℝ) := by
  apply (isCuspPoint_iff_isCusp ∞).mpr
  exact (_root_.isCusp_SL2Z_iff').mpr ⟨1, by simp⟩

/-- The unique cusp orbit of the effective level-one modular group, represented by infinity. -/
def cuspOrbitInfty : psl2zToPSL2R.range.CuspOrbit :=
  psl2zToPSL2R.range.cuspOrbitMk ⟨(∞ : OnePoint ℝ), Subgroup.mem_cuspPoints.mpr
    isCuspPoint_infty⟩

@[simp]
theorem cuspOrbitInfty_val :
    (cuspOrbitInfty : psl2zToPSL2R.range.BoundaryOrbit) = Quotient.mk'' (∞ : OnePoint ℝ) :=
  Subgroup.cuspOrbitMk_val _

/-- The effective level-one modular group has exactly one cusp orbit. -/
instance instUniqueCuspOrbit : Unique psl2zToPSL2R.range.CuspOrbit where
  default := cuspOrbitInfty
  uniq C := by
    obtain ⟨c, rfl⟩ := Subgroup.cuspOrbitMk_surjective C
    apply (Subgroup.cuspOrbitMk_eq_iff _ _).mpr
    exact cuspPoint_mem_orbit_infty (Subgroup.mem_cuspPoints.mp c.property)

/-- The level-one modular orbit space becomes compact after its unique cusp orbit is adjoined.
The compact sets used here are Mathlib's truncated closed modular fundamental domains. -/
@[instance]
theorem compactSpace_compactifiedQuotient :
    CompactSpace psl2zToPSL2R.range.CompactifiedQuotient := by
  let Γ := psl2zToPSL2R.range
  have : Finite Γ.CuspOrbit := inferInstance
  obtain ⟨D, -, hDs⟩ :=
    isCuspPoint_infty.exists_cuspDatum (σ := (1 : PSL(2, ℝ))) (by simp)
  have hD (C : Γ.CuspOrbit) : D.cuspOrbit = C := by
    exact Subsingleton.elim _ _
  apply Subgroup.CompactifiedQuotient.compactSpace_of_compact_truncations
    (D := fun _ ↦ D) (fun C ↦ hD C)
  intro A
  refine ⟨_root_.ModularGroup.truncatedFundamentalDomain (A D.cuspOrbit),
    _root_.ModularGroup.isCompact_truncatedFundamentalDomain _, ?_⟩
  intro q
  induction q using Quotient.inductionOn with
  | h z =>
    obtain ⟨g, hg⟩ := _root_.ModularGroup.exists_smul_mem_fd z
    have hq : (Quotient.mk (orbitRel Γ ℍ) (g • z)) =
        Quotient.mk (orbitRel Γ ℍ) z := by
      have h := orbitRel.Quotient.quotient_smul_eq
        (g := (⟨psl2zToPSL2R (g : PSL(2, ℤ)), ⟨(g : PSL(2, ℤ)), rfl⟩⟩ : Γ)) (a := z)
      simpa only [MulAction.subgroup_smul_def, UpperHalfPlane.psl2zToPSL2R_smul,
        UpperHalfPlane.pslMk_smul] using h
    by_cases hy : (g • z).im ≤ A D.cuspOrbit
    · left
      exact ⟨g • z, ⟨hg, hy⟩, hq⟩
    · right
      refine ⟨D.cuspOrbit, g • z, ?_, hq⟩
      rw [mem_horodisc, hDs, one_smul]
      exact lt_of_not_ge hy

end TauCeti.ModularGroup
