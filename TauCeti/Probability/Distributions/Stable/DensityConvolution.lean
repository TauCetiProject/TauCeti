/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convolution.Density
public import TauCeti.Probability.Distributions.Stable.Operations
public import TauCeti.Probability.Distributions.Stable.PDF

/-!
# Convolution factorization of scalar stable densities

The measure-level convolution formula for scalar stable laws lifts to a pointwise convolution
formula for their continuous real densities.  The proof first presents the convolution of the
two input laws by the ordinary Bochner convolution of their densities.  Equality of the output
measure identifies the two densities almost everywhere, and continuity upgrades this to
pointwise equality.

This is the density-level factorization used to transfer exact support information to strict
positivity of stable densities.

## Main results

* `TauCeti.Probability.integrable_stablePDFReal` proves integrability of the chosen stable density
  for every parameter value.
* `TauCeti.Probability.stablePDFReal_convolution_stablePDFReal_of_eq` is the pointwise density
  counterpart of `stableMeasure_conv_stableMeasure_of_eq`.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer, 2020,
  chapter 1.
-/

public section

open MeasureTheory ProbabilityTheory Set ContinuousLinearMap
open scoped Convolution ENNReal NNReal

namespace TauCeti.Probability

variable {α β : ℝ} {s : ℝ≥0}

/-- The chosen real stable density is integrable for every parameter value.  At zero scale and
at invalid parameters this uses the library's zero-density convention. -/
theorem integrable_stablePDFReal (α β : ℝ) (s : ℝ≥0) (m : ℝ) :
    Integrable (stablePDFReal α β s m) := by
  rcases eq_zero_or_pos s with rfl | hs
  · rw [show stablePDFReal α β 0 m = 0 by
      funext x
      exact stablePDFReal_zero_scale α β m x]
    exact integrable_zero ℝ ℝ volume
  · have hmeasure := stableMeasure_eq_withDensity α β hs m
    simp_rw [funext (stablePDF_eq_ofReal α β s m)] at hmeasure
    exact Probability.integrable_of_eq_withDensity hmeasure
      (measurable_stablePDFReal α β s m).aemeasurable
      (.of_forall fun x ↦ stablePDFReal_nonneg α β s m x)

/-- The pointwise convolution factorization of two stable densities of a common shape.

The hypotheses are the same scale, skewness, and `S₁`-location equations as in
`stableMeasure_conv_stableMeasure_of_eq`.  Positive input scales ensure that all three chosen
densities represent their laws. -/
theorem stablePDFReal_convolution_stablePDFReal_of_eq (hα : α ∈ Ioc 0 2) {β₁ β₂ : ℝ}
    (hβ₁ : |β₁| ≤ 1) (hβ₂ : |β₂| ≤ 1) (hβ : |β| ≤ 1) {s₁ s₂ s : ℝ≥0}
    (hs₁ : 0 < s₁) (hs₂ : 0 < s₂) {m₁ m₂ m : ℝ}
    (hs : (s : ℝ) ^ α = (s₁ : ℝ) ^ α + (s₂ : ℝ) ^ α)
    (hskew : β * (s : ℝ) ^ α = β₁ * (s₁ : ℝ) ^ α + β₂ * (s₂ : ℝ) ^ α)
    (hm : stableS1Location α β s m =
      stableS1Location α β₁ s₁ m₁ + stableS1Location α β₂ s₂ m₂) :
    stablePDFReal α β₁ s₁ m₁ ⋆[mul ℝ ℝ] stablePDFReal α β₂ s₂ m₂ =
      stablePDFReal α β s m := by
  have hs0 : 0 < s := by
    rw [← NNReal.coe_pos]
    by_contra hsn
    have hscoe : (s : ℝ) = 0 :=
      le_antisymm (not_lt.mp hsn) (NNReal.coe_nonneg s)
    have hpow : (s : ℝ) ^ α = 0 :=
      (Real.rpow_eq_zero (NNReal.coe_nonneg s) hα.1.ne').2 hscoe
    rw [hpow] at hs
    have hrhs : 0 < (s₁ : ℝ) ^ α + (s₂ : ℝ) ^ α :=
      add_pos (Real.rpow_pos_of_pos (NNReal.coe_pos.2 hs₁) α)
        (Real.rpow_pos_of_pos (NNReal.coe_pos.2 hs₂) α)
    linarith
  have hfint := integrable_stablePDFReal α β₁ s₁ m₁
  have hgcont := continuous_stablePDFReal α β₂ s₂ m₂
  have hf0 : 0 ≤ stablePDFReal α β₁ s₁ m₁ :=
    fun x ↦ stablePDFReal_nonneg α β₁ s₁ m₁ x
  have hg0 : 0 ≤ stablePDFReal α β₂ s₂ m₂ :=
    fun x ↦ stablePDFReal_nonneg α β₂ s₂ m₂ x
  let C := Real.Gamma α⁻¹ / (Real.pi * α * s₂)
  have hgC : ∀ x, ‖stablePDFReal α β₂ s₂ m₂ x‖ ≤ C := fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
    exact stablePDFReal_le hα hβ₂ hs₂ m₂ x
  have hconv : ConvolutionExists (stablePDFReal α β₁ s₁ m₁)
      (stablePDFReal α β₂ s₂ m₂) (mul ℝ ℝ) volume :=
    convolutionExists_of_integrable_of_ae_norm_le (mul ℝ ℝ) hfint
      hgcont.aestronglyMeasurable (Filter.Eventually.of_forall hgC)
  have hconvcont : Continuous
      (stablePDFReal α β₁ s₁ m₁ ⋆[mul ℝ ℝ] stablePDFReal α β₂ s₂ m₂) :=
    (show BddAbove (range fun x ↦ ‖stablePDFReal α β₂ s₂ m₂ x‖) from
      ⟨C, forall_mem_range.2 hgC⟩).continuous_convolution_right_of_integrable
        (mul ℝ ℝ) hfint hgcont
  have hmeasure :
      volume.withDensity (fun x ↦ ENNReal.ofReal (stablePDFReal α β₁ s₁ m₁ x)) ∗
          volume.withDensity (fun x ↦ ENNReal.ofReal (stablePDFReal α β₂ s₂ m₂ x)) =
        volume.withDensity (fun x ↦ ENNReal.ofReal
          ((stablePDFReal α β₁ s₁ m₁ ⋆[mul ℝ ℝ]
            stablePDFReal α β₂ s₂ m₂) x)) :=
    conv_withDensity_ofReal_eq_withDensity_convolution
      (measurable_stablePDFReal α β₁ s₁ m₁) (measurable_stablePDFReal α β₂ s₂ m₂)
      hf0 hg0 hconv
  have hdensityMeasure :
      volume.withDensity (fun x ↦ ENNReal.ofReal
          ((stablePDFReal α β₁ s₁ m₁ ⋆[mul ℝ ℝ]
            stablePDFReal α β₂ s₂ m₂) x)) =
        volume.withDensity (fun x ↦ ENNReal.ofReal (stablePDFReal α β s m x)) := by
    have hpdf₁ := stableMeasure_eq_withDensity α β₁ hs₁ m₁
    have hpdf₂ := stableMeasure_eq_withDensity α β₂ hs₂ m₂
    have hpdf := stableMeasure_eq_withDensity α β hs0 m
    simp_rw [funext (stablePDF_eq_ofReal α β₁ s₁ m₁)] at hpdf₁
    simp_rw [funext (stablePDF_eq_ofReal α β₂ s₂ m₂)] at hpdf₂
    simp_rw [funext (stablePDF_eq_ofReal α β s m)] at hpdf
    rw [← hmeasure, ← hpdf₁, ← hpdf₂,
      stableMeasure_conv_stableMeasure_of_eq hα hβ₁ hβ₂ hβ hs hskew hm, hpdf]
  have hlt : ∫⁻ x, ENNReal.ofReal
      ((stablePDFReal α β₁ s₁ m₁ ⋆[mul ℝ ℝ]
        stablePDFReal α β₂ s₂ m₂) x) ≠ ∞ := by
    apply isFiniteMeasure_withDensity_iff.mp
    rw [hdensityMeasure]
    have hpdf := stableMeasure_eq_withDensity α β hs0 m
    simp_rw [funext (stablePDF_eq_ofReal α β s m)] at hpdf
    rw [← hpdf]
    infer_instance
  have haeENN : (fun x ↦ ENNReal.ofReal
      ((stablePDFReal α β₁ s₁ m₁ ⋆[mul ℝ ℝ]
        stablePDFReal α β₂ s₂ m₂) x)) =ᵐ[volume]
      fun x ↦ ENNReal.ofReal (stablePDFReal α β s m x) :=
    (withDensity_eq_iff hconvcont.measurable.ennreal_ofReal.aemeasurable
      (measurable_stablePDFReal α β s m).ennreal_ofReal.aemeasurable hlt).1 hdensityMeasure
  have hae :
      (stablePDFReal α β₁ s₁ m₁ ⋆[mul ℝ ℝ] stablePDFReal α β₂ s₂ m₂) =ᵐ[volume]
        stablePDFReal α β s m := by
    filter_upwards [haeENN] with x hx
    exact (ENNReal.ofReal_eq_ofReal_iff
      (by rw [convolution_def]; exact integral_nonneg fun y ↦ mul_nonneg (hf0 y) (hg0 (x - y)))
      (stablePDFReal_nonneg α β s m x)).mp hx
  exact (Continuous.ae_eq_iff_eq volume hconvcont (continuous_stablePDFReal α β s m)).1 hae

end TauCeti.Probability
