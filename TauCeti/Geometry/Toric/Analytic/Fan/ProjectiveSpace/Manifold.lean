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
`X_j / X_k` of the comparison are the toric homogeneous coordinates, which evaluate characters.
Both directions are therefore holomorphic chart by chart, for the complex structure of any
extending basis on the toric charts.

## Main declarations

* `TauCeti.Toric.ratio_projectiveSpaceHomeomorph_analyticAffineChartι`: on a toric maximal chart,
  the homogeneous ratios of the comparison are the toric homogeneous coordinates.
* `TauCeti.Toric.preimage_projectiveSpaceHomeomorph_affineOpen`: the standard affine open where
  `X_k` is nonzero corresponds to the toric chart of the maximal cone omitting `k`.
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

/-- On the toric chart of the maximal cone omitting `k`, the homogeneous ratios `X_j / X_k` of the
comparison with the sphere quotient are the normalized toric homogeneous coordinates. -/
@[simp]
theorem ratio_projectiveSpaceHomeomorph_analyticAffineChartι (k : Option (Fin n))
    (x : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)))
    (j : Fin (n + 1)) :
    ComplexProjectiveSpace.ratio ((finSuccEquiv n).symm k) j
        (projectiveSpaceHomeomorph b hi
          ((Φ).analyticAffineChartι hΦ (Fan.projectiveSpaceMaximalCone b hi k) x)) =
      projectiveSpaceHomogeneousCoordinate b hi k x (finSuccEquiv n j) := by
  have hn := norm_ne_zero_iff.2 (projectiveSpaceHomogeneousVector_ne_zero b hi k x)
  rw [projectiveSpaceHomeomorph_apply_chart, ComplexProjectiveSpace.ratio_mk]
  simp only [NormedSpace.normalize, PiLp.smul_apply, projectiveSpaceHomogeneousVector_apply,
    Equiv.apply_symm_apply, projectiveSpaceHomogeneousCoordinate_self, Complex.real_smul,
    mul_one]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (inv_ne_zero hn))

/-- The standard affine open of complex projective space where the homogeneous coordinate `k` is
nonzero corresponds to the toric chart of the maximal cone omitting the ray `k`. -/
theorem preimage_projectiveSpaceHomeomorph_affineOpen (k : Option (Fin n)) :
    projectiveSpaceHomeomorph b hi ⁻¹'
        ComplexProjectiveSpace.affineOpen ((finSuccEquiv n).symm k) =
      range ((Φ).analyticAffineChartι hΦ (Fan.projectiveSpaceMaximalCone b hi k)) := by
  ext p
  constructor
  · intro hp
    obtain ⟨v, hv⟩ := ComplexProjectiveSpace.mk_surjective n (projectiveSpaceHomeomorph b hi p)
    have hk : v.1 ((finSuccEquiv n).symm k) ≠ 0 := by simpa [← hv] using hp
    refine ⟨_, (projectiveSpaceHomeomorph_symm_mk b hi v k hk).symm.trans ?_⟩
    rw [hv, Homeomorph.symm_apply_apply]
  · rintro ⟨x : AffineSemigroupComplexPoint (dualSemigroup hi (projectiveSpaceCone b i {k}ᶜ)),
      rfl⟩
    have h := ratio_projectiveSpaceHomeomorph_analyticAffineChartι b hi k x
      ((finSuccEquiv n).symm k)
    rw [Equiv.apply_symm_apply, projectiveSpaceHomogeneousCoordinate_self] at h
    exact (ComplexProjectiveSpace.mem_affineOpen_iff _ _).2 (ne_of_eq_of_ne h one_ne_zero)

/-- On the standard affine open where `X_k` is nonzero, the inverse comparison is the point of
the toric chart of the maximal cone omitting `k` with toric coordinates the homogeneous ratios
`X_j / X_k`. -/
theorem projectiveSpaceHomeomorph_symm_eq_of_mem_affineOpen (k : Option (Fin n))
    {p : ComplexProjectiveSpace n}
    (hp : p ∈ ComplexProjectiveSpace.affineOpen ((finSuccEquiv n).symm k)) :
    let _ := affinePointTopology ((Φ).analyticChartGenerators
      (Fan.projectiveSpaceMaximalCone b hi k)).2
    (projectiveSpaceHomeomorph b hi).symm p =
      (Φ).analyticAffineChartι hΦ (Fan.projectiveSpaceMaximalCone b hi k)
        ((projectiveSpacePointHomeomorph b hi k
          ((Φ).analyticChartGenerators (Fan.projectiveSpaceMaximalCone b hi k)).2).symm
          (fun j ↦ ComplexProjectiveSpace.ratio ((finSuccEquiv n).symm k)
            ((finSuccEquiv n).symm j) p)) := by
  obtain ⟨v, rfl⟩ := ComplexProjectiveSpace.mk_surjective n p
  have hk : v.1 ((finSuccEquiv n).symm k) ≠ 0 := by simpa using hp
  simp only [ComplexProjectiveSpace.ratio_mk]
  exact projectiveSpaceHomeomorph_symm_mk b hi v k hk

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
  have hparam : ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) r
      (ComplexProjectiveSpace.affineChart k').symm := by
    rw [← contMDiffOn_univ, ← ComplexProjectiveSpace.affineChart_target k']
    exact contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (ComplexProjectiveSpace.mem_atlas_iff _ |>.2 ⟨k', rfl⟩))
  refine (((hparam.comp hcoord).comp_contMDiffOn P.symm.contMDiffOn).contMDiffAt
    (P.open_target.mem_nhds hp)).congr_of_eventuallyEq ?_
  filter_upwards [P.open_target.mem_nhds hp] with y hy
  have hy' := P.right_inv hy
  rw [Fan.analyticAffineChartPartialDiffeomorph_apply] at hy'
  have hsource :
      projectiveSpaceHomeomorph b hi y ∈ (ComplexProjectiveSpace.affineChart k').source := by
    rw [ComplexProjectiveSpace.affineChart_source, ← mem_preimage,
      preimage_projectiveSpaceHomeomorph_affineOpen]
    exact ⟨_, hy'⟩
  rw [← (ComplexProjectiveSpace.affineChart k').left_inv hsource]
  congr 1
  funext j
  have h := ratio_projectiveSpaceHomeomorph_analyticAffineChartι b hi k (P.symm y)
    (k'.succAbove j)
  rw [ComplexProjectiveSpace.affineChart_apply]
  exact (congrArg (fun q ↦ ComplexProjectiveSpace.ratio k' (k'.succAbove j)
    (projectiveSpaceHomeomorph b hi q)) hy').symm.trans h

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
        Fin.insertNth (α := fun _ ↦ ℂ) k' 1 z ((finSuccEquiv n).symm j) := by
    refine contDiff_pi.2 fun j ↦ ?_
    induction (finSuccEquiv n).symm j using k'.succAboveCases with
    | x => simpa only [Fin.insertNth_apply_same] using contDiff_const
    | p j => simpa only [Fin.insertNth_apply_succAbove] using contDiff_apply ℂ (fun _ ↦ ℂ) j
  have hchart : ContMDiffOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) r
      (ComplexProjectiveSpace.affineChart k') (ComplexProjectiveSpace.affineOpen k') := by
    rw [← ComplexProjectiveSpace.affineChart_source k']
    exact contMDiffOn_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (ComplexProjectiveSpace.mem_atlas_iff _ |>.2 ⟨k', rfl⟩))
  refine (((((Φ).contMDiff_analyticAffineChartι hΦ (Fan.projectiveSpaceMaximalCone b hi k)
    hB κ g r).comp D.symm.contMDiff).comp hratio.contMDiff).comp_contMDiffOn hchart
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
