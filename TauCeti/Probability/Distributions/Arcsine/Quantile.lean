/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Arcsine.Cdf
public import TauCeti.Probability.Quantile

/-!
# Arcsine quantiles

At an interior probability level `u`, the arcsine quantile is `sin (π * u / 2) ^ 2`.
This formula gives continuity in the level and one-sided limits at the support endpoints.
The endpoint limits are stated in `EReal`, without assigning endpoint quantile values.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley, 1995, Chapter 25.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

/-- The arcsine quantile is `sin (π * u / 2) ^ 2` at every interior probability level. -/
theorem quantile_arcsineMeasure {u : ℝ} (hu : u ∈ Ioo 0 1) :
    arcsineMeasure.quantile u = sin (π * u / 2) ^ 2 := by
  have ht0 : 0 ≤ π * u / 2 := div_nonneg (mul_nonneg pi_pos.le hu.1.le) (by norm_num)
  have ht1 : π * u / 2 ≤ π / 2 := by
    nlinarith [mul_lt_mul_of_pos_left hu.2 pi_pos]
  have hs : 0 ≤ sin (π * u / 2) := sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [pi_pos])
  refine eq_of_forall_ge_iff fun x ↦ ?_
  rw [Measure.quantile_le_iff _ hu.1 hu.2]
  rcases lt_or_ge x 0 with hx | hx
  · rw [cdf_arcsineMeasure_of_nonpos hx.le]
    exact iff_of_false (not_le.mpr hu.1) (not_le.mpr (hx.trans_le (sq_nonneg _)))
  rcases le_or_gt 1 x with hx₁ | hx₁
  · rw [cdf_arcsineMeasure_of_one_le hx₁]
    exact iff_of_true hu.2.le ((sin_sq_le_one _).trans hx₁)
  rw [cdf_arcsineMeasure_eq]
  have hscale : u ≤ 2 / π * arcsin (√x) ↔ π * u / 2 ≤ arcsin (√x) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ pi_pos, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    ring_nf
  rw [hscale, le_arcsin_iff_sin_le ⟨by linarith [pi_pos], ht1⟩
    ⟨by linarith [sqrt_nonneg x], sqrt_le_one.mpr hx₁.le⟩, le_sqrt hs hx]

/-- Arcsine quantiles depend continuously on interior probability levels. -/
theorem continuousOn_quantile_arcsineMeasure : ContinuousOn arcsineMeasure.quantile (Ioo 0 1) := by
  have hc : Continuous (fun u : ℝ ↦ sin (π * u / 2) ^ 2) := by fun_prop
  exact hc.continuousOn.congr (fun _ hu ↦ quantile_arcsineMeasure hu)

/-- The lower one-sided limit of the arcsine quantile is the lower support endpoint zero. -/
theorem tendsto_quantile_arcsineMeasure_nhdsGT_zero :
    Tendsto (fun u ↦ (arcsineMeasure.quantile u : EReal)) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous (fun u : ℝ ↦ sin (π * u / 2) ^ 2) := by fun_prop
  have hlim := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simp only [mul_zero, zero_div, sin_zero, zero_pow two_ne_zero] at hlim
  apply (EReal.tendsto_coe.mpr hlim).congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  exact congrArg (fun x : ℝ ↦ (x : EReal)) (quantile_arcsineMeasure hu).symm

/-- The upper one-sided limit of the arcsine quantile is the upper support endpoint one. -/
theorem tendsto_quantile_arcsineMeasure_nhdsLT_one :
    Tendsto (fun u ↦ (arcsineMeasure.quantile u : EReal)) (𝓝[<] 1) (𝓝 1) := by
  have hc : Continuous (fun u : ℝ ↦ sin (π * u / 2) ^ 2) := by fun_prop
  have hlim := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio 1))
  simp only [mul_one, sin_pi_div_two, one_pow] at hlim
  apply (EReal.tendsto_coe.mpr hlim).congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact congrArg (fun x : ℝ ↦ (x : EReal)) (quantile_arcsineMeasure hu).symm

end TauCeti.Probability
