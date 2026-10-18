/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution

import Mathlib.MeasureTheory.Group.Integral

/-!
# Convolution existence and continuous linear maps

An essentially bounded function convolves with an integrable function at every point of a
measurable additive group with a measure invariant under left translations and negation
(`MeasureTheory.convolutionExists_of_ae_norm_le_of_integrable` and
`MeasureTheory.convolutionExists_of_integrable_of_ae_norm_le`). No topology on the group or
sigma-finiteness of the measure is required.

A continuous linear map `L : F →L[𝕜] F'` between real or complex Banach spaces commutes with
convolution against a scalar kernel `ρ : G → 𝕜`: `ρ ⋆ (L ∘ f) = L (ρ ⋆ f)` at every point where
`ρ ⋆ f` exists (`ContinuousLinearMap.convolution_lsmul_comp_comm`). This is the convolution form
of `ContinuousLinearMap.integral_comp_comm`. It lets a mollification be moved through a continuous
linear map, for instance to mollify the image of a function in a dual space.
-/

public section

open MeasureTheory
open scoped Convolution

namespace MeasureTheory

variable {G E E' F : Type*} {f : G → E} {g : G → E'} {M : ℝ}

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [AddGroup G] [MeasurableSpace G]
  [MeasurableAdd G] [MeasurableNeg G] {μ : Measure G} [μ.IsAddLeftInvariant] [μ.IsNegInvariant]
  (L : E →L[𝕜] E' →L[𝕜] F)

/-- An essentially bounded function convolves with an integrable function at every point. -/
theorem convolutionExists_of_ae_norm_le_of_integrable (hf : AEStronglyMeasurable f μ)
    (hfM : ∀ᵐ t ∂μ, ‖f t‖ ≤ M) (hg : Integrable g μ) : ConvolutionExists f g L μ := fun x => by
  refine ((hg.comp_sub_left x).norm.const_mul (‖L‖ * M)).mono'
    (L.aestronglyMeasurable_comp₂ hf (hg.comp_sub_left x).aestronglyMeasurable) ?_
  filter_upwards [hfM] with t ht
  refine (L.le_opNorm₂ _ _).trans ?_
  gcongr

/-- An integrable function convolves with an essentially bounded function at every point. -/
theorem convolutionExists_of_integrable_of_ae_norm_le (hf : Integrable f μ)
    (hg : AEStronglyMeasurable g μ) (hgM : ∀ᵐ t ∂μ, ‖g t‖ ≤ M) : ConvolutionExists f g L μ :=
  fun x => by
    have hsub := (Measure.measurePreserving_sub_left μ x).quasiMeasurePreserving
    refine ((hf.norm.const_mul ‖L‖).mul_const M).mono'
      (L.aestronglyMeasurable_comp₂ hf.aestronglyMeasurable
        (hg.comp_quasiMeasurePreserving hsub)) ?_
    filter_upwards [hsub.ae hgM] with t ht
    refine (L.le_opNorm₂ _ _).trans ?_
    gcongr

end MeasureTheory

/-- A continuous linear map commutes with convolution against a scalar kernel, at every point
where the convolution exists. -/
theorem ContinuousLinearMap.convolution_lsmul_comp_comm {𝕜 G F F' : Type*} [RCLike 𝕜] [Sub G]
    [MeasurableSpace G] {μ : Measure G} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
    [CompleteSpace F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [NormedSpace ℝ F']
    [CompleteSpace F'] (L : F →L[𝕜] F') {ρ : G → 𝕜} {f : G → F} {x : G}
    (h : ConvolutionExistsAt ρ f x (ContinuousLinearMap.lsmul 𝕜 𝕜) μ) :
    (ρ ⋆[ContinuousLinearMap.lsmul 𝕜 𝕜, μ] fun y ↦ L (f y)) x =
      L ((ρ ⋆[ContinuousLinearMap.lsmul 𝕜 𝕜, μ] f) x) := by
  simpa only [convolution_lsmul, ContinuousLinearMap.lsmul_apply, map_smul] using
    L.integral_comp_comm h.integrable
