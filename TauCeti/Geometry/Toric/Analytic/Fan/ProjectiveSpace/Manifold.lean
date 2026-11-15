/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Toric.Analytic.Fan.Manifold
public import TauCeti.Geometry.Toric.Analytic.Fan.ProjectiveSpace.Charts
public import TauCeti.Geometry.Toric.Analytic.Fan.ProjectiveSpace.Comparison
public import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace

/-!
# Toric projective space is biholomorphic to complex projective space

The analytic realization of the standard projective-space fan carries the complex structure
glued from its affine toric charts. Complex projective space, modelled as the circle quotient of
the unit sphere, carries its standard atlas of homogeneous-ratio charts. This file shows that the
homogeneous-coordinate comparison `TauCeti.Toric.projectiveSpaceHomeomorph` between them is a
biholomorphism.

The two chart systems match up exactly. The maximal cone omitting the ray `k` corresponds to the
affine open where the homogeneous coordinate `k` is nonzero, and on it the homogeneous ratios
`X_j / X_k` of the comparison are the toric homogeneous coordinates, which evaluate characters
(`TauCeti.Toric.preimage_projectiveSpaceHomeomorph_affineOpen` and
`TauCeti.Toric.ratio_projectiveSpaceHomeomorph_analyticAffineChartι`). Both directions are
therefore holomorphic chart by chart, for the complex structure of any extending basis on the
toric charts.

## Main declarations

* `TauCeti.Toric.contMDiff_projectiveSpaceHomeomorph`,
  `TauCeti.Toric.contMDiff_projectiveSpaceHomeomorph_symm`: the comparison and its inverse are
  holomorphic.
* `TauCeti.Toric.projectiveSpaceDiffeomorph`: the comparison as a biholomorphism.

## References

* W. Fulton, *Introduction to Toric Varieties*, §1.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§3.1 and 3.4.
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti.Toric

universe u

variable {N V : Type u} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {n : ℕ} (b : Module.Basis (Fin n) ℤ N) {i : N →+ V} (hi : IsIntegralLattice i)

local notation "Φ" => Fan.projectiveSpace b hi
local notation "hΦ" => Fan.isRegular_projectiveSpace b hi

/-- The comparison from toric projective space to the sphere quotient is holomorphic. -/
theorem contMDiff_projectiveSpaceHomeomorph (r : ℕ∞ω) :
    let _ := (Φ).analyticChartedSpace hΦ
    ContMDiff 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) 𝓘(ℂ, Fin n → ℂ) r
      (projectiveSpaceHomeomorph b hi) := by
  intro _ p
  obtain ⟨k, x, rfl⟩ := exists_projectiveSpaceMaximalCone_chart b hi p
  have hσ := isRegularCone_projectiveSpaceCone b hi (S := {k}ᶜ) (by simp)
  obtain ⟨l, B, hB⟩ := hσ.exists_basis_sum
  have : Finite (ToricRay (projectiveSpaceCone b i {k}ᶜ)) := ToricRay.finite_of_fg hσ.fg
  let κ := Finite.equivFin (ToricRay (projectiveSpaceCone b i {k}ᶜ))
  let g := ((Φ).analyticChartGenerators (Fan.projectiveSpaceMaximalCone b hi k)).2
  let _ := affinePointTopology g
  let _ := coneChartedSpace hi hσ.toIsToricCone hB κ g
  let P := (Φ).analyticAffineChartPartialDiffeomorph hΦ (Fan.projectiveSpaceMaximalCone b hi k)
    hB κ g r
  let k' := (finSuccEquiv n).symm k
  have hp : (Φ).analyticAffineChartι hΦ (Fan.projectiveSpaceMaximalCone b hi k) x ∈ P.target := by
    rw [Fan.analyticAffineChartPartialDiffeomorph_target]
    exact mem_range_self x
  -- In the toric chart, the standard chart coordinates are characters, hence holomorphic.
  have hcoord : ContMDiff 𝓘(ℂ, (Fin (Nat.card (ToricRay (projectiveSpaceCone b i {k}ᶜ))) → ℂ) ×
      (Fin l → ℂ)) 𝓘(ℂ, Fin n → ℂ) r
      fun y : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)) ↦
        fun j : Fin n ↦ projectiveSpaceHomogeneousCoordinate b hi k y
          (finSuccEquiv n (k'.succAbove j)) := by
    rw [contMDiff_pi_module_iff]
    exact fun j ↦ (contMDiff_apply_single hi hσ.toIsToricCone hB κ g _ r).congr fun y ↦
      projectiveSpaceHomogeneousCoordinate_def b hi k y _
  refine ((((ComplexProjectiveSpace.contMDiff_affineChart_symm k' r).comp hcoord).comp_contMDiffOn
    P.symm.contMDiffOn).contMDiffAt (P.open_target.mem_nhds hp)).congr_of_eventuallyEq ?_
  filter_upwards [P.open_target.mem_nhds hp] with y hy
  have hy' := P.right_inv hy
  rw [Fan.analyticAffineChartPartialDiffeomorph_apply] at hy'
  have hsource :
      projectiveSpaceHomeomorph b hi y ∈ (ComplexProjectiveSpace.affineChart k').source := by
    rw [ComplexProjectiveSpace.affineChart_source, ← mem_preimage,
      preimage_projectiveSpaceHomeomorph_affineOpen]
    exact ⟨_, hy'⟩
  rw [← (ComplexProjectiveSpace.affineChart k').left_inv hsource]
  exact congrArg _ ((congrArg (fun q ↦ ComplexProjectiveSpace.affineChart k'
    (projectiveSpaceHomeomorph b hi q)) hy').symm.trans
      (affineChart_projectiveSpaceHomeomorph_analyticAffineChartι b hi k (P.symm y)))

/-- The inverse comparison from the sphere quotient to toric projective space is holomorphic. -/
theorem contMDiff_projectiveSpaceHomeomorph_symm (r : ℕ∞ω) :
    let _ := (Φ).analyticChartedSpace hΦ
    ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) r
      (projectiveSpaceHomeomorph b hi).symm := by
  intro _ p
  obtain ⟨k₀, hk₀⟩ := ComplexProjectiveSpace.exists_mem_affineOpen p
  obtain ⟨k, rfl⟩ := (finSuccEquiv n).symm.surjective k₀
  have hσ := isRegularCone_projectiveSpaceCone b hi (S := {k}ᶜ) (by simp)
  obtain ⟨l, B, hB⟩ := hσ.exists_basis_sum
  have : Finite (ToricRay (projectiveSpaceCone b i {k}ᶜ)) := ToricRay.finite_of_fg hσ.fg
  let κ := Finite.equivFin (ToricRay (projectiveSpaceCone b i {k}ᶜ))
  let g := ((Φ).analyticChartGenerators (Fan.projectiveSpaceMaximalCone b hi k)).2
  let _ := affinePointTopology g
  let _ := coneChartedSpace hi hσ.toIsToricCone hB κ g
  let D := projectiveSpacePointDiffeomorph b hi k hB κ g r
  let k' := (finSuccEquiv n).symm k
  have hopen := (ComplexProjectiveSpace.isOpen_affineOpen k').mem_nhds hk₀
  -- The model space of `D` carries the classical `Fintype` instance on `{j // j ≠ k}`, because
  -- `projectiveSpacePointDiffeomorph` is stated for an arbitrary index type; use the same one.
  let _ : DecidableEq (Fin n) := fun a b ↦ Classical.propDecidable (a = b)
  -- On the affine open of `k'`, the toric coordinates are affine in the standard chart.
  have hratio : ContDiff ℂ r fun z : Fin n → ℂ ↦
      fun j : {j : Option (Fin n) // j ≠ k} ↦
        Fin.insertNth (α := fun _ ↦ ℂ) k' 1 z ((finSuccEquiv n).symm j) :=
    contDiff_pi.2 fun j ↦
      contDiff_pi.1 ((contDiff_const (c := (1 : ℂ))).finInsertNth (F := fun _ ↦ ℂ) k'
        contDiff_id) ((finSuccEquiv n).symm j)
  refine (((((Φ).contMDiff_analyticAffineChartι hΦ (Fan.projectiveSpaceMaximalCone b hi k)
    hB κ g r).comp D.symm.contMDiff).comp hratio.contMDiff).comp_contMDiffOn
      (ComplexProjectiveSpace.contMDiffOn_affineChart k' r)
      |>.contMDiffAt hopen).congr_of_eventuallyEq ?_
  have hD : ⇑D.symm = ⇑(projectiveSpacePointHomeomorph b hi k g).symm := by
    rw [← Diffeomorph.coe_toHomeomorph_symm, projectiveSpacePointDiffeomorph_toHomeomorph]
  filter_upwards [hopen] with q hq
  simp only [projectiveSpaceHomeomorph_symm_eq_of_mem_affineOpen b hi k hq, Function.comp_apply,
    hD, ComplexProjectiveSpace.insertNth_affineChart k' hq, k', g]

/-- Homogeneous coordinates identify the analytic realization of the standard projective-space
fan biholomorphically with complex projective space, the circle quotient of the unit sphere with
its standard homogeneous-ratio atlas. -/
noncomputable def projectiveSpaceDiffeomorph (r : ℕ∞ω) :
    let _ := (Φ).analyticChartedSpace hΦ
    Diffeomorph 𝓘(ℂ, Fin (Module.finrank ℤ N) → ℂ) 𝓘(ℂ, Fin n → ℂ)
      ((Φ).analyticRealization hΦ) (ComplexProjectiveSpace n) r :=
  let _ := (Φ).analyticChartedSpace hΦ
  { toEquiv := (projectiveSpaceHomeomorph b hi).toEquiv
    contMDiff_toFun := contMDiff_projectiveSpaceHomeomorph b hi r
    contMDiff_invFun := contMDiff_projectiveSpaceHomeomorph_symm b hi r }

/-- The projective-space biholomorphism is the homogeneous-coordinate comparison. -/
@[simp]
theorem coe_projectiveSpaceDiffeomorph (r : ℕ∞ω) :
    ⇑(projectiveSpaceDiffeomorph b hi r) = projectiveSpaceHomeomorph b hi := (rfl)

/-- The inverse projective-space biholomorphism is the inverse homogeneous-coordinate
comparison. -/
@[simp]
theorem coe_projectiveSpaceDiffeomorph_symm (r : ℕ∞ω) :
    letI := (Φ).analyticChartedSpace hΦ
    ⇑(projectiveSpaceDiffeomorph b hi r).symm = (projectiveSpaceHomeomorph b hi).symm := (rfl)

end TauCeti.Toric
