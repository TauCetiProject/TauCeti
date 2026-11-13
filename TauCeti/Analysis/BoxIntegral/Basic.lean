/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.BoxIntegral.Basic

/-!
# Box integrals along linear maps

Box integrals against the volume (or any scalar box-additive map) can be moved along a linear
isometry, so that results can pass to the completion of the codomain.
-/

public section

noncomputable section

open BoxIntegral MeasureTheory

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A linear map commutes with the integral sum of a function against the scalar box-additive map
`vol.toSMul` over a tagged prepartition: the sums of `e ∘ g` are the images under `e` of those of
`g`. -/
protected theorem LinearMap.integralSum_toSMul_comp (e : E →ₗ[ℝ] F) {I : Box ι}
    (g : (ι → ℝ) → E) (vol : ι →ᵇᵃ ℝ) (π : TaggedPrepartition I) :
    integralSum (fun x ↦ e (g x)) vol.toSMul π = e (integralSum g vol.toSMul π) := by
  simp only [integralSum, BoxAdditiveMap.toSMul_apply, map_sum, map_smul]

/-- A linear isometry `e : E →ₗᵢ[ℝ] F` preserves and reflects the box integral against `vol.toSMul`
with a prescribed value: `e ∘ g` has integral `e z` if and only if `g` has integral `z`. This does
not assert that every integral of `e ∘ g` is of this form, since an integral in `F` need not lie in
the range of `e`. -/
protected theorem LinearIsometry.hasIntegral_toSMul_comp_iff [Fintype ι] (e : E →ₗᵢ[ℝ] F)
    {I : Box ι} {l : IntegrationParams} {g : (ι → ℝ) → E} {vol : ι →ᵇᵃ ℝ} {z : E} :
    HasIntegral I l (fun x ↦ e (g x)) vol.toSMul (e z) ↔ HasIntegral I l g vol.toSMul z := by
  have h (π : TaggedPrepartition I) : integralSum (fun x ↦ e (g x)) vol.toSMul π =
      e (integralSum g vol.toSMul π) := LinearMap.integralSum_toSMul_comp e.toLinearMap g vol π
  simp only [hasIntegral_iff, h, LinearIsometry.dist_map]

/-- The volume specialization of `LinearIsometry.hasIntegral_toSMul_comp_iff`. -/
protected theorem LinearIsometry.hasIntegral_volume_comp_iff [Fintype ι] (e : E →ₗᵢ[ℝ] F)
    {I : Box ι} {l : IntegrationParams} {g : (ι → ℝ) → E} {z : E} :
    HasIntegral I l (fun x ↦ e (g x)) BoxAdditiveMap.volume (e z) ↔
      HasIntegral I l g BoxAdditiveMap.volume z :=
  e.hasIntegral_toSMul_comp_iff (vol := (volume : Measure (ι → ℝ)).toBoxAdditive)
