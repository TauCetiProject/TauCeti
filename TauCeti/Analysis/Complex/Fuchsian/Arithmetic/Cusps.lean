/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic.Basic
import TauCeti.GroupTheory.DoubleCoset.Orbits

/-!
# Double-coset description of Fuchsian cusp orbits

For a finite-index subgroup `Γ' ≤ PSL(2, ℤ)`, the double cosets `Γ' \ PSL(2, ℤ) / ⟨T⟩` are in
canonical bijection with the Fuchsian cusp orbits `(Γ'.map psl2zToPSL2R).CuspOrbit`
(`TauCeti.ModularGroup.doubleCosetEquivFuchsianCuspOrbit`), sending `Γ' g ⟨T⟩` to the cusp orbit
of `psl2zToPSL2R g • ∞`.
-/

public noncomputable section

open Matrix Matrix.ProjectiveSpecialLinearGroup MulAction OnePoint Subgroup
open scoped MatrixGroups

namespace TauCeti.ModularGroup

/-- Map from left cosets `PSL(2, ℤ) ⧸ Γ'` to Fuchsian cusp orbits, sending `g Γ'` to the cusp
orbit of `psl2zToPSL2R g⁻¹ • ∞`. -/
def cosetToFuchsianCuspOrbit (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex]
    (q : PSL(2, ℤ) ⧸ Γ') : (Γ'.map psl2zToPSL2R).CuspOrbit :=
  ⟨inverseTranslateOrbit Γ' (∞ : OnePoint ℝ) q, by
    induction q using QuotientGroup.induction_on with | H g =>
    rw [inverseTranslateOrbit_mk, Subgroup.isCuspOrbit_mk_iff]
    exact Γ'.isCuspPoint_map_psl2zToPSL2R_smul_infty g⁻¹⟩

@[simp]
theorem cosetToFuchsianCuspOrbit_val (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex]
    (q : PSL(2, ℤ) ⧸ Γ') :
    (cosetToFuchsianCuspOrbit Γ' q : (Γ'.map psl2zToPSL2R).BoundaryOrbit) =
      inverseTranslateOrbit Γ' (∞ : OnePoint ℝ) q :=
  (rfl)

@[simp]
theorem cosetToFuchsianCuspOrbit_mk (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex]
    (g : PSL(2, ℤ)) :
    cosetToFuchsianCuspOrbit Γ' (g : PSL(2, ℤ) ⧸ Γ') =
      (Γ'.map psl2zToPSL2R).cuspOrbitMk
        ⟨psl2zToPSL2R g⁻¹ • (∞ : OnePoint ℝ),
          Subgroup.mem_cuspPoints.mpr (Γ'.isCuspPoint_map_psl2zToPSL2R_smul_infty g⁻¹)⟩ :=
  Subtype.ext
    (by rw [cosetToFuchsianCuspOrbit_val, inverseTranslateOrbit_mk, Subgroup.cuspOrbitMk_val])

private def orbitToFuchsianCuspOrbit (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex] :
    orbitRel.Quotient (Subgroup.zpowers (_root_.ModularGroup.T : PSL(2, ℤ)))
        (PSL(2, ℤ) ⧸ Γ') →
      (Γ'.map psl2zToPSL2R).CuspOrbit :=
  Quotient.lift (cosetToFuchsianCuspOrbit Γ') fun q₁ q₂ h ↦ Subtype.ext <|
    (inverseTranslateOrbit_eq_iff_mem_orbit_zpowers Γ' psl2zToPSL2R_smul_infty_eq_infty_iff
      q₁ q₂).mpr (orbitRel_apply.mp h)

private theorem orbitToFuchsianCuspOrbit_mk (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex]
    (q : PSL(2, ℤ) ⧸ Γ') :
    orbitToFuchsianCuspOrbit Γ' (Quotient.mk _ q) = cosetToFuchsianCuspOrbit Γ' q :=
  (rfl)

private def orbitEquivFuchsianCuspOrbit (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex] :
    orbitRel.Quotient (Subgroup.zpowers (_root_.ModularGroup.T : PSL(2, ℤ)))
        (PSL(2, ℤ) ⧸ Γ') ≃
      (Γ'.map psl2zToPSL2R).CuspOrbit :=
  Equiv.ofBijective (orbitToFuchsianCuspOrbit Γ')
    ⟨fun a b hab ↦ by
      induction a using Quotient.inductionOn with | h q₁ =>
      induction b using Quotient.inductionOn with | h q₂ =>
      rw [orbitToFuchsianCuspOrbit_mk, orbitToFuchsianCuspOrbit_mk, Subtype.ext_iff,
        cosetToFuchsianCuspOrbit_val, cosetToFuchsianCuspOrbit_val,
        inverseTranslateOrbit_eq_iff_mem_orbit_zpowers Γ' psl2zToPSL2R_smul_infty_eq_infty_iff]
        at hab
      exact Quotient.sound' (orbitRel_apply.mpr hab),
    fun C ↦ by
      obtain ⟨c, rfl⟩ := Subgroup.cuspOrbitMk_surjective C
      obtain ⟨⟨_, g, rfl⟩, hc⟩ := mem_orbit_iff.mp
        (TauCeti.ModularGroup.cuspPoint_mem_orbit_infty
          ((Subgroup.mem_cuspPoints.mp c.property).mono (Γ'.map_le_range psl2zToPSL2R)))
      refine ⟨Quotient.mk _ ((g⁻¹ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ'), Subtype.ext ?_⟩
      rw [orbitToFuchsianCuspOrbit_mk, cosetToFuchsianCuspOrbit_mk, inv_inv,
        Subgroup.cuspOrbitMk_val, Subgroup.cuspOrbitMk_val]
      simpa [Subgroup.smul_def] using congrArg Quotient.mk'' hc⟩

private theorem orbitEquivFuchsianCuspOrbit_mk (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex]
    (q : PSL(2, ℤ) ⧸ Γ') :
    orbitEquivFuchsianCuspOrbit Γ' (Quotient.mk _ q) = cosetToFuchsianCuspOrbit Γ' q :=
  (rfl)

/-- **Double cosets and Fuchsian cusp orbits.** For any finite-index `Γ' ≤ PSL(2, ℤ)`, the double
cosets `Γ' \ PSL(2, ℤ) / ⟨T⟩` biject onto the Fuchsian cusp orbits
`(Γ'.map psl2zToPSL2R).CuspOrbit`, sending `Γ' g ⟨T⟩` to the cusp orbit of `psl2zToPSL2R g • ∞`. -/
def doubleCosetEquivFuchsianCuspOrbit (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex] :
    DoubleCoset.Quotient (Γ' : Set PSL(2, ℤ))
        (Subgroup.zpowers (_root_.ModularGroup.T : PSL(2, ℤ))) ≃
      (Γ'.map psl2zToPSL2R).CuspOrbit :=
  (TauCeti.orbitQuotientEquivDoubleCoset Γ'
    (Subgroup.zpowers (_root_.ModularGroup.T : PSL(2, ℤ)))).symm.trans
    (orbitEquivFuchsianCuspOrbit Γ')

/-- Evaluating `doubleCosetEquivFuchsianCuspOrbit` on the double coset `Γ' g ⟨T⟩` gives the
Fuchsian cusp orbit of `psl2zToPSL2R g • ∞`. -/
@[simp]
theorem doubleCosetEquivFuchsianCuspOrbit_mk (Γ' : Subgroup PSL(2, ℤ)) [Γ'.FiniteIndex]
    (g : PSL(2, ℤ)) :
    doubleCosetEquivFuchsianCuspOrbit Γ'
        (DoubleCoset.mk Γ' (Subgroup.zpowers (_root_.ModularGroup.T : PSL(2, ℤ))) g) =
      (Γ'.map psl2zToPSL2R).cuspOrbitMk
        ⟨psl2zToPSL2R g • (∞ : OnePoint ℝ),
          Subgroup.mem_cuspPoints.mpr (Γ'.isCuspPoint_map_psl2zToPSL2R_smul_infty g)⟩ := by
  have hsymm : (TauCeti.orbitQuotientEquivDoubleCoset Γ'
      (Subgroup.zpowers (_root_.ModularGroup.T : PSL(2, ℤ)))).symm
      (DoubleCoset.mk Γ' (Subgroup.zpowers (_root_.ModularGroup.T : PSL(2, ℤ))) g) =
      Quotient.mk _ ((g⁻¹ : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ Γ') :=
    (Equiv.symm_apply_eq _).mpr <| by simp
  rw [doubleCosetEquivFuchsianCuspOrbit, Equiv.trans_apply, hsymm,
    orbitEquivFuchsianCuspOrbit_mk, cosetToFuchsianCuspOrbit_mk, inv_inv]

end TauCeti.ModularGroup
