/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Convolution.Density
public import TauCeti.MeasureTheory.Measure.WithDensity
public import TauCeti.Probability.Distributions.Stable.Operations
public import TauCeti.Probability.Distributions.Stable.PDF

/-!
# Convolution factorization of scalar stable densities

The measure-level convolution formula for scalar stable laws lifts to a pointwise convolution
formula for their continuous real densities. The two input laws have a common stability index
and positive scales, and their output parameters satisfy the scale, skewness, and `S₁`-location
equations from the measure-level convolution theorem.

This is the density-level factorization used to transfer exact support information to strict
positivity of stable densities.

## Main results

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
  have hgbdd : BddAbove (range fun x ↦ ‖stablePDFReal α β₂ s₂ m₂ x‖) :=
    ⟨C, forall_mem_range.2 hgC⟩
  have hconvcont : Continuous
      (stablePDFReal α β₁ s₁ m₁ ⋆[mul ℝ ℝ] stablePDFReal α β₂ s₂ m₂) :=
    hgbdd.continuous_convolution_right_of_integrable (mul ℝ ℝ) hfint hgcont
  have hmeasure :
      volume.withDensity (fun x ↦ ENNReal.ofReal (stablePDFReal α β₁ s₁ m₁ x)) ∗
          volume.withDensity (fun x ↦ ENNReal.ofReal (stablePDFReal α β₂ s₂ m₂ x)) =
        volume.withDensity (fun x ↦ ENNReal.ofReal
          ((stablePDFReal α β₁ s₁ m₁ ⋆[mul ℝ ℝ]
            stablePDFReal α β₂ s₂ m₂) x)) :=
    conv_withDensity_ofReal_eq_withDensity_convolution
      (measurable_stablePDFReal α β₁ s₁ m₁) (measurable_stablePDFReal α β₂ s₂ m₂)
      hf0 hg0 (Filter.Eventually.of_forall hconv)
  have hdensityMeasure :
      volume.withDensity (fun x ↦ ENNReal.ofReal
          ((stablePDFReal α β₁ s₁ m₁ ⋆[mul ℝ ℝ]
            stablePDFReal α β₂ s₂ m₂) x)) =
        volume.withDensity (fun x ↦ ENNReal.ofReal (stablePDFReal α β s m x)) := by
    rw [← hmeasure]
    simp only [← stablePDF_eq_ofReal]
    rw [← stableMeasure_eq_withDensity α β₁ hs₁ m₁,
      ← stableMeasure_eq_withDensity α β₂ hs₂ m₂,
      stableMeasure_conv_stableMeasure_of_eq hα hβ₁ hβ₂ hβ hs hskew hm,
      stableMeasure_eq_withDensity α β hs0 m]
  apply continuous_eq_of_withDensity_ofReal_eq hconvcont (continuous_stablePDFReal α β s m)
      (fun x ↦ ?_) (fun x ↦ stablePDFReal_nonneg α β s m x) hdensityMeasure
  rw [convolution_def]
  exact integral_nonneg fun y ↦ mul_nonneg (hf0 y) (hg0 (x - y))

end TauCeti.Probability
