/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.BoxIntegral.Basic

/-!
# Box integrals against the volume along linear maps

Box integrals against the volume can be moved along a linear isometry, so that results can
pass to the completion of the codomain.
-/

public section

noncomputable section

open BoxIntegral

variable {ι E F : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A linear map commutes with the integral sum of a function against `BoxAdditiveMap.volume` over
a tagged prepartition: the sums of `e ∘ g` are the images under `e` of those of `g`. -/
protected theorem LinearMap.integralSum_volume_comp (e : E →ₗ[ℝ] F) {I : Box ι}
    (g : (ι → ℝ) → E) (π : TaggedPrepartition I) :
    integralSum (fun x ↦ e (g x)) BoxAdditiveMap.volume π =
      e (integralSum g BoxAdditiveMap.volume π) := by
  simp only [integralSum, BoxAdditiveMap.volume_apply, map_sum, map_smul]

/-- A linear isometry `e : E →ₗᵢ[ℝ] F` preserves and reflects the box integral against the volume
with a prescribed value: `e ∘ g` has integral `e z` if and only if `g` has integral `z`. The
integral sums of `e ∘ g` are the images of those of `g`, and `e` preserves distances. This does not
assert that every integral of `e ∘ g` is of this form, since an integral in `F` need not lie in the
range of `e`. -/
protected theorem LinearIsometry.hasIntegral_volume_comp_iff (e : E →ₗᵢ[ℝ] F) {I : Box ι}
    {l : IntegrationParams} {g : (ι → ℝ) → E} {z : E} :
    HasIntegral I l (fun x ↦ e (g x)) BoxAdditiveMap.volume (e z) ↔
      HasIntegral I l g BoxAdditiveMap.volume z := by
  have h (π : TaggedPrepartition I) : integralSum (fun x ↦ e (g x)) BoxAdditiveMap.volume π =
      e (integralSum g BoxAdditiveMap.volume π) :=
      LinearMap.integralSum_volume_comp e.toLinearMap g π
  simp only [hasIntegral_iff, h, LinearIsometry.dist_map]
