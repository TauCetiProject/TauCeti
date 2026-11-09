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

* `TauCeti.Probability.convolutionExists_stablePDFReal` and
  `TauCeti.Probability.continuous_convolution_stablePDFReal`: the convolution of an integrable
  function with a stable density exists and is continuous.
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

/-- A stable density either has valid shape `α ∈ (0, 2]`, skewness in `[-1, 1]` and positive
scale, or it vanishes. -/
private lemma valid_or_stablePDFReal_eq_zero (α β : ℝ) (s : ℝ≥0) (m : ℝ) :
    (α ∈ Ioc 0 2 ∧ |β| ≤ 1 ∧ 0 < s) ∨ stablePDFReal α β s m = 0 := by
  by_cases hα : α ∈ Ioc 0 2
  · by_cases hβ : |β| ≤ 1
    · rcases eq_zero_or_pos s with rfl | hs
      · exact Or.inr (funext (stablePDFReal_zero_scale α β m))
      · exact Or.inl ⟨hα, hβ, hs⟩
    · exact Or.inr (funext (stablePDFReal_of_invalid (Or.inr (Or.inr (not_le.1 hβ))) s m))
  · refine Or.inr (funext (stablePDFReal_of_invalid ?_ s m))
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hα
    exact hα.imp id Or.inl

/-- The convolution of an integrable function with a stable density exists. -/
lemma convolutionExists_stablePDFReal {f : ℝ → ℝ} (hf : Integrable f) (α β : ℝ) (s : ℝ≥0)
    (m : ℝ) : ConvolutionExists f (stablePDFReal α β s m) (mul ℝ ℝ) volume := by
  rcases valid_or_stablePDFReal_eq_zero α β s m with ⟨hα, hβ, hs⟩ | h
  · exact convolutionExists_of_integrable_of_ae_norm_le (mul ℝ ℝ) hf
      (continuous_stablePDFReal α β s m).aestronglyMeasurable
      (.of_forall (norm_stablePDFReal_le hα hβ hs m))
  · intro x
    simp [h, ConvolutionExistsAt]

/-- The convolution of an integrable function with a stable density is continuous. -/
lemma continuous_convolution_stablePDFReal {f : ℝ → ℝ} (hf : Integrable f) (α β : ℝ) (s : ℝ≥0)
    (m : ℝ) : Continuous (f ⋆[mul ℝ ℝ] stablePDFReal α β s m) := by
  rcases valid_or_stablePDFReal_eq_zero α β s m with ⟨hα, hβ, hs⟩ | h
  · exact BddAbove.continuous_convolution_right_of_integrable (mul ℝ ℝ)
      ⟨Real.Gamma α⁻¹ / (Real.pi * α * s), forall_mem_range.2 (norm_stablePDFReal_le hα hβ hs m)⟩
      hf (continuous_stablePDFReal α β s m)
  · rw [h, convolution_zero]
    exact continuous_const

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
    by_contra hsn
    rw [not_lt, nonpos_iff_eq_zero] at hsn
    have h₁ : 0 < (s₁ : ℝ) ^ α := Real.rpow_pos_of_pos (NNReal.coe_pos.2 hs₁) α
    have h₂ : 0 ≤ (s₂ : ℝ) ^ α := Real.rpow_nonneg (NNReal.coe_nonneg _) α
    rw [hsn, NNReal.coe_zero, Real.zero_rpow hα.1.ne'] at hs
    linarith
  have hf0 : 0 ≤ stablePDFReal α β₁ s₁ m₁ :=
    fun x ↦ stablePDFReal_nonneg α β₁ s₁ m₁ x
  have hg0 : 0 ≤ stablePDFReal α β₂ s₂ m₂ :=
    fun x ↦ stablePDFReal_nonneg α β₂ s₂ m₂ x
  have hconv := convolutionExists_stablePDFReal (integrable_stablePDFReal α β₁ s₁ m₁) α β₂ s₂ m₂
  have hconvcont := continuous_convolution_stablePDFReal
    (integrable_stablePDFReal α β₁ s₁ m₁) α β₂ s₂ m₂
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
