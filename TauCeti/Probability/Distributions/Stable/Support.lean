/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.DensityConvolution
import TauCeti.Analysis.Convolution.Positivity
import TauCeti.Probability.Distributions.Stable.Approximation.Support
import TauCeti.Probability.Distributions.Stable.Decomposition

/-!
# Support and density positivity of two-sided stable laws

A positive-scale stable law with `|β| < 1` has topological support all of `ℝ`, including at
shape one. Its large-jump compound-Poisson factor already has full support, and convolution
with the small-jump probability factor preserves this property. Affine transport gives every
scale and location; shape two follows from the Gaussian law.

The continuous density is strictly positive everywhere. To see this, split the law into two
identically distributed stable factors with half the scale power and half the `S₁` location.
Their continuous densities have full topological support, so the convolution positivity theorem
applies even before either density is known to be positive at every point.

## Main results

* `TauCeti.Probability.support_stableMeasure_of_abs_lt_one` gives full topological support.
* `TauCeti.Probability.stablePDFReal_pos_of_abs_lt_one` gives pointwise strict density positivity.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1 and section 3.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set ContinuousLinearMap
open scoped Convolution ENNReal NNReal Pointwise

namespace TauCeti.Probability

variable {α β : ℝ} {s : ℝ≥0}

private theorem support_standardStableMeasure_of_abs_lt_one (hα : α ∈ Ioo 0 2)
    (hβ : |β| < 1) : (stableMeasure α β 1 0).support = univ := by
  obtain ⟨μ, hμ, -⟩ := existsUnique_conv_stableCompensatedPoissonMeasure_eq hα hβ.le
    (by norm_num : (0 : ℝ) < 1)
  let _ := isProbabilityMeasure_stableCompensatedPoissonMeasure hα hβ.le zero_lt_one
  obtain ⟨a, ha⟩ := Measure.nonempty_support (IsProbabilityMeasure.ne_zero (μ : Measure ℝ))
  apply eq_univ_of_forall
  intro x
  rw [← hμ]
  have hy : x - a ∈ (stableCompensatedPoissonMeasure α β 1).support := by
    simp [support_stableCompensatedPoissonMeasure_of_abs_lt_one hα hβ zero_lt_one]
  convert Measure.add_mem_support_conv ha hy using 1
  ring

/-- A stable law of valid shape, positive scale and strict interior skewness has full
topological support. This includes shape one and the Gaussian shape two. -/
@[simp]
theorem support_stableMeasure_of_abs_lt_one (hα : α ∈ Ioc 0 2) (hβ : |β| < 1)
    (hs : 0 < s) (m : ℝ) : (stableMeasure α β s m).support = univ := by
  rcases hα.2.eq_or_lt with htwo | htwo
  · subst α
    rw [stableMeasure_two hβ.le]
    apply eq_univ_of_univ_subset
    simpa only [Measure.support_eq_univ] using
      (gaussianReal_absolutelyContinuous' m (by positivity : 2 * s ^ 2 ≠ 0)).support_mono
  · rw [← stableMeasure_one_zero_map_affine hs, support_map_affine (NNReal.coe_pos.2 hs).ne',
      support_standardStableMeasure_of_abs_lt_one ⟨hα.1, htwo⟩ hβ, image_univ]
    exact range_eq_univ.mpr fun y ↦ ⟨(y - m) / s, by
      field_simp [(NNReal.coe_pos.2 hs).ne']
      ring⟩

private theorem exists_stableDensity_convolution_self (hα : α ∈ Ioc 0 2) (hβ : |β| ≤ 1)
    (hs : 0 < s) (m : ℝ) :
    ∃ (r : ℝ≥0) (c : ℝ), 0 < r ∧
      stablePDFReal α β r c ⋆[mul ℝ ℝ] stablePDFReal α β r c = stablePDFReal α β s m := by
  let r : ℝ≥0 := (s ^ α / 2) ^ α⁻¹
  let c := stableS1Location α β s m / 2 - stableS1Location α β r 0
  have hr : 0 < r := NNReal.rpow_pos (div_pos (NNReal.rpow_pos hs) (by norm_num))
  have hpow : (r : ℝ) ^ α = (s : ℝ) ^ α / 2 := by
    simp [r, ← NNReal.coe_rpow, NNReal.rpow_inv_rpow hα.1.ne']
  refine ⟨r, c, hr, stablePDFReal_convolution_stablePDFReal_of_eq hα hβ hβ hβ hr hr
    (by rw [hpow]; ring) (by rw [hpow]; ring) ?_⟩
  rw [stableS1Location_eq_add α β r c]
  dsimp only [c]
  ring

/-- The continuous density of a positive-scale stable law with strict interior skewness is
strictly positive at every real point, including at shapes one and two. -/
theorem stablePDFReal_pos_of_abs_lt_one (hα : α ∈ Ioc 0 2) (hβ : |β| < 1)
    (hs : 0 < s) (m x : ℝ) : 0 < stablePDFReal α β s m x := by
  obtain ⟨r, c, hr, hconv⟩ := exists_stableDensity_convolution_self hα hβ.le hs m
  have hf := continuous_stablePDFReal α β r c
  have hf0 := stablePDFReal_nonneg α β r c
  have hsupp : tsupport (stablePDFReal α β r c) = univ := by
    rw [← Measure.support_withDensity_ofReal (μ := volume) hf hf0,
      ← funext (stablePDF_eq_ofReal α β r c),
      ← stableMeasure_eq_withDensity α β hr c, support_stableMeasure_of_abs_lt_one hα hβ hr c]
  have hfinite : ConvolutionExists (stablePDFReal α β r c) (stablePDFReal α β r c)
      (mul ℝ ℝ) volume :=
    convolutionExists_of_integrable_of_ae_norm_le (mul ℝ ℝ)
      (integrable_stablePDFReal α β r c) hf.aestronglyMeasurable
      (.of_forall fun y ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 y)]
        exact stablePDFReal_le hα hβ.le hr c y)
  rw [← congrFun hconv x]
  apply (convolution_pos_iff_mem_interior_add_tsupport hf hf hf0 hf0
    (by rw [hsupp]; exact convex_univ) (by rw [hsupp]; exact convex_univ) (hfinite x)).2
  simp [hsupp]

end TauCeti.Probability
