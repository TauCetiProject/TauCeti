/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Examples and non-examples of finite-regularity almost complex structures

On a complex normed space `V`, multiplication by `i` is the smooth structure
`SmoothAlmostComplexStructure.ofComplexManifold V V`, so it is a structure of every regularity
`ℓ`. Its chart expression is the constant map `i`, as for every constant structure.

The identity endomorphism is never an almost complex structure: `id ∘ id = id`, while
`-id ≠ id` on a nontrivial real vector space. In particular a smooth endomorphism field on `ℂ`
equal to `i` on the closed unit disc and to `id` outside the disc of radius `2` squares to `-1`
on the unit disc but is not the field of any structure: the square identity is required at
every point, not on an open set.

## Main declarations

* `ContMDiffAlmostComplexStructure.toEndomorphism_ne_id`: no fibre of a structure is the identity.
* `ContMDiffAlmostComplexStructure.inChart_const`,
  `ContMDiffAlmostComplexStructure.inChart_toContMDiff_ofComplexManifold_self`: the chart
  expression of a constant structure, and of the structure `i`, is constant.
* `ContMDiffAlmostComplexStructure.cutoffSection`,
  `ContMDiffAlmostComplexStructure.not_exists_toEndomorphism_eq_cutoffSection`: the cut-off
  section and its rejection.
-/

public noncomputable section

open Bundle Metric
open scoped ContDiff Manifold

namespace TauCeti

namespace ContMDiffAlmostComplexStructure

section Identity

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {n : ℕ∞}

/-- No fibre of an almost complex structure is the identity, at any regularity: the identity
squares to itself, and `id ≠ -id` on a nontrivial real vector space. -/
theorem toEndomorphism_ne_id (J : ContMDiffAlmostComplexStructure I n M) (x : M) :
    J.toEndomorphism x ≠ ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  intro h
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have hJv : J x (J x v) = -v := J.apply_apply x v
  have hxv : J x v = v := congrArg (fun A : TangentSpace I x →L[ℝ] TangentSpace I x ↦ A v) h
  rw [hxv, hxv] at hJv
  have h2 : (2 : ℝ) • v = 0 := by
    rw [two_smul]
    nth_rw 1 [hJv]
    exact neg_add_cancel v
  exact hv ((smul_eq_zero.mp h2).resolve_left two_ne_zero)

/-- The identity section is not the endomorphism field of any almost complex structure, at any
regularity, on a nonempty manifold modelled on a nontrivial space. -/
theorem not_exists_toEndomorphism_eq_id [Nonempty M] :
    ¬∃ J : ContMDiffAlmostComplexStructure I n M,
      ∀ x, J.toEndomorphism x = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
  rintro ⟨J, hJ⟩
  obtain ⟨x⟩ := ‹Nonempty M›
  exact J.toEndomorphism_ne_id x (hJ x)

end Identity

section ComplexConstant

/-- The chart expression of a constant structure on its model space is the constant map. -/
@[simp]
theorem inChart_const {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (n : ℕ∞)
    (Jc : W →L[ℝ] W) (hJc : ∀ v, Jc (Jc v) = -v) (x z : W) :
    (const n Jc hJc).inChart x z = Jc := by
  rw [inChart_def, const_toEndomorphism_apply]
  exact inCoordinates_tangent_bundle_core_model_space _ _ _ _ _

/-- On a complex normed space `V`, for example `ℂⁿ`, multiplication by `i` is a structure of
every regularity `n`, and its chart expression is constantly multiplication by `i`. -/
theorem inChart_toContMDiff_ofComplexManifold_self {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] (n : ℕ∞) (x z : V) :
    ((SmoothAlmostComplexStructure.ofComplexManifold V V).toContMDiff n).inChart x z =
      Complex.I • ContinuousLinearMap.id ℝ V := by
  rw [inChart_def, SmoothAlmostComplexStructure.toContMDiff_toEndomorphism_apply,
    SmoothAlmostComplexStructure.toEndomorphism_ofComplexManifold]
  exact inCoordinates_tangent_bundle_core_model_space _ _ _ _ _

end ComplexConstant

section Cutoff

/-- A smooth cutoff on `ℂ`, equal to `1` on the closed unit disc and to `0` outside the open
disc of radius `2`. -/
def unitDiscCutoff : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩

@[simp]
theorem unitDiscCutoff_rIn : unitDiscCutoff.rIn = 1 := (rfl)

@[simp]
theorem unitDiscCutoff_rOut : unitDiscCutoff.rOut = 2 := (rfl)

theorem unitDiscCutoff_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) : unitDiscCutoff z = 1 :=
  unitDiscCutoff.one_of_mem_closedBall (by simpa using hz)

theorem unitDiscCutoff_of_two_le_norm {z : ℂ} (hz : 2 ≤ ‖z‖) : unitDiscCutoff z = 0 :=
  unitDiscCutoff.zero_of_le_dist (by simpa using hz)

/-- The endomorphism field `χ • i + (1 - χ) • id` on `ℂ`, where `χ` is `unitDiscCutoff`. -/
def cutoffField (z : ℂ) : ℂ →L[ℝ] ℂ :=
  unitDiscCutoff z • (Complex.I • ContinuousLinearMap.id ℝ ℂ) +
    (1 - unitDiscCutoff z) • ContinuousLinearMap.id ℝ ℂ

/-- The cut-off field is smooth. -/
theorem contDiff_cutoffField : ContDiff ℝ ∞ cutoffField := by
  have hχ : ContDiff ℝ ∞ (unitDiscCutoff : ℂ → ℝ) := unitDiscCutoff.contDiff
  exact (hχ.smul contDiff_const).add ((contDiff_const.sub hχ).smul contDiff_const)

theorem cutoffField_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) :
    cutoffField z = Complex.I • ContinuousLinearMap.id ℝ ℂ := by
  ext v
  simp [cutoffField, unitDiscCutoff_of_norm_le_one hz]

theorem cutoffField_of_two_le_norm {z : ℂ} (hz : 2 ≤ ‖z‖) :
    cutoffField z = ContinuousLinearMap.id ℝ ℂ := by
  ext v
  simp [cutoffField, unitDiscCutoff_of_two_le_norm hz]

/-- On the closed unit disc the cut-off field squares to minus the identity. -/
theorem cutoffField_cutoffField_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) (v : ℂ) :
    cutoffField z (cutoffField z v) = -v := by
  rw [cutoffField_of_norm_le_one hz]
  simp [← mul_assoc]

/-- Outside the disc of radius `2` the cut-off field fails the square identity. -/
theorem cutoffField_comp_ne_neg_id {z : ℂ} (hz : 2 ≤ ‖z‖) :
    (cutoffField z).comp (cutoffField z) ≠ -ContinuousLinearMap.id ℝ ℂ := by
  rw [cutoffField_of_two_le_norm hz]
  intro h
  have h1 := congrArg (fun A : ℂ →L[ℝ] ℂ ↦ A 1) h
  norm_num at h1

/-- The cut-off field as a smooth section of the tangent endomorphism bundle of `ℂ`. -/
def cutoffSection :
    ContMDiffSection 𝓘(ℝ, ℂ) (ℂ →L[ℝ] ℂ) ∞
      (fun z : ℂ ↦ TangentSpace 𝓘(ℝ, ℂ) z →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) z) :=
  endomorphismOfModel cutoffField contDiff_cutoffField

@[simp]
theorem cutoffSection_apply (z : ℂ) : cutoffSection z = cutoffField z :=
  endomorphismOfModel_apply _ _ z

/-- The smooth cut-off section is not the field of an almost complex structure of any regularity:
it squares to `-1` on the unit disc, but the identity is required at every point. -/
theorem not_exists_toEndomorphism_eq_cutoffSection {n : ℕ∞} :
    ¬∃ J : ContMDiffAlmostComplexStructure 𝓘(ℝ, ℂ) n ℂ,
      ∀ z, J.toEndomorphism z = cutoffSection z := by
  rintro ⟨J, hJ⟩
  have h2 : 2 ≤ ‖(2 : ℂ)‖ := by simp
  refine J.toEndomorphism_ne_id 2 ?_
  rw [hJ, cutoffSection_apply, cutoffField_of_two_le_norm h2]
  rfl

end Cutoff

end ContMDiffAlmostComplexStructure

end TauCeti
