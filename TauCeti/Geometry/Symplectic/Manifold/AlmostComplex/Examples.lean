/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Chart
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Examples and non-examples of finite-regularity almost complex structures

On a complex normed space `V`, multiplication by `i` is the smooth structure
`SmoothAlmostComplexStructure.ofComplexManifold V V`, so it is a structure of every regularity
`ℓ`. Its chart expression is the constant map `i`
(`SmoothAlmostComplexStructure.inChart_ofComplexManifold_self`, beside the structure in
`TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure`).

The identity endomorphism is never an almost complex structure: `id ∘ id = id`, while
`-id ≠ id` on a nontrivial real vector space
(`ContMDiffAlmostComplexStructure.toEndomorphism_ne_id`). In particular a smooth endomorphism
field on `ℂ` equal to `i` on the closed unit disc and to `id` outside the disc of radius `2`
squares to `-1` on the unit disc but is not the field of any structure: the square identity
`J ∘ J = -1` is required at every point, not only on an open set.

## Main declarations

* `ContMDiffAlmostComplexStructure.cutoffSection`,
  `ContMDiffAlmostComplexStructure.not_exists_toEndomorphism_eq_cutoffSection`: the cut-off
  section and its rejection.
-/

public noncomputable section

open Bundle Metric
open scoped ContDiff Manifold

namespace TauCeti

namespace ContMDiffAlmostComplexStructure

section Cutoff

/-- A smooth cutoff on `ℂ`, equal to `1` on the closed unit disc and to `0` outside the open
disc of radius `2`. -/
def unitDiscCutoff : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩

@[simp]
theorem unitDiscCutoff_rIn : unitDiscCutoff.rIn = 1 := (rfl)

@[simp]
theorem unitDiscCutoff_rOut : unitDiscCutoff.rOut = 2 := (rfl)

@[simp]
theorem unitDiscCutoff_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) : unitDiscCutoff z = 1 :=
  unitDiscCutoff.one_of_mem_closedBall (by simpa using hz)

@[simp]
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

@[simp]
theorem cutoffField_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) :
    cutoffField z = Complex.I • ContinuousLinearMap.id ℝ ℂ := by
  ext v
  simp [cutoffField, unitDiscCutoff_of_norm_le_one hz]

@[simp]
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
  Manifold.tangentEndomorphismOfModel cutoffField contDiff_cutoffField

@[simp]
theorem cutoffSection_apply (z : ℂ) : cutoffSection z = cutoffField z :=
  Manifold.tangentEndomorphismOfModel_apply _ _ z

/-- The smooth cut-off section is not the field of an almost complex structure of any regularity:
it squares to `-1` on the unit disc, but equals `id` outside radius `2`, and the square identity
`J ∘ J = -1` is required at every point, not only on an open set. -/
theorem not_exists_toEndomorphism_eq_cutoffSection {n : ℕ∞} :
    ¬∃ J : ContMDiffAlmostComplexStructure 𝓘(ℝ, ℂ) n ℂ,
      ∀ z, J.toEndomorphism z = cutoffSection z := by
  rintro ⟨J, hJ⟩
  have h2 : 2 ≤ ‖(2 : ℂ)‖ := by simp
  refine J.toEndomorphism_ne_id 2 ?_
  rw [hJ, cutoffSection_apply, cutoffField_of_two_le_norm h2]
  -- `TangentSpace 𝓘(ℝ, ℂ) 2` unfolds to `ℂ`, so both sides are the identity of `ℂ`.
  rfl

end Cutoff

end ContMDiffAlmostComplexStructure

end TauCeti
