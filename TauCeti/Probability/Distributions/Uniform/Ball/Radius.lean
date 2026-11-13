/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Uniform.Ball.Basic
public import TauCeti.Probability.Distributions.Affine
import TauCeti.Probability.Distributions.Beta.Quantile
import TauCeti.Probability.Quantile.Map

/-!
# Cdfs and quantiles of uniform-ball radii

In positive dimension `d`, the distance from the center of a uniform point of a ball of radius
`r ≥ 0` has interior quantile `r * u ^ d⁻¹`. Its cdf is zero below zero, `(x / r) ^ d` between
zero and `r`, and one at and above `r`. The quantiles tend to zero and `r` at the respective
endpoints of the probability interval. These formulas include the radius-zero Dirac law.

The normalized radius at positive `r` has cdf `x ^ d` on `[0, 1]` and quantile `u ^ d⁻¹`.
The results specialize `map_norm_sub_div_uniformBallMeasure` and the power-function Beta API;
no new change-of-variables argument is needed. Positive dimension is essential: in dimension
zero the distance is constantly zero even when the ball parameter is positive.

## References

* K.-T. Fang, S. Kotz, K. W. Ng, *Symmetric Multivariate and Related Distributions*,
  Chapman and Hall, 1990, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Module
open scoped Topology

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  {r u : ℝ}

/-- The distance from the center of a uniform ball point is a scaled `Beta(d, 1)` variable,
including the radius-zero Dirac law. -/
theorem map_norm_sub_uniformBallMeasure (c : E) (hr : 0 ≤ r) :
    (uniformBallMeasure c r).map (fun x ↦ ‖x - c‖) =
      (betaMeasure (finrank ℝ E) 1).map (fun x ↦ r * x) := by
  have := isProbabilityMeasureBeta (Nat.cast_pos.2 (finrank_pos (R := ℝ) (M := E))) one_pos
  rcases hr.eq_or_lt with rfl | hr
  · simp [Measure.map_const]
  rw [← map_norm_sub_div_uniformBallMeasure c hr, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext x
  exact (mul_div_cancel₀ _ hr.ne').symm

/-- The normalized radius cdf is the power `x ^ d` on `[0, 1]`, with its zero and one
extensions outside that interval. -/
theorem cdf_map_norm_sub_div_uniformBallMeasure (c : E) (hr : 0 < r) (x : ℝ) :
    cdf ((uniformBallMeasure c r).map (fun y ↦ ‖y - c‖ / r)) x =
      if x < 0 then 0 else if 1 ≤ x then 1 else x ^ finrank ℝ E := by
  have hd : (0 : ℝ) < finrank ℝ E := Nat.cast_pos.2 finrank_pos
  rw [map_norm_sub_div_uniformBallMeasure c hr]
  split_ifs with hx hx₁
  · rw [cdf_betaMeasure_eq hd one_pos,
      regularizedIncompleteBeta_eq_zero_of_nonpos hd.ne' 1 hx.le]
  · rw [cdf_betaMeasure_eq hd one_pos,
      regularizedIncompleteBeta_eq_one_of_one_le hd.le one_pos hx₁]
  · rw [cdf_betaMeasure_one_right hd ⟨le_of_not_gt hx, le_of_not_ge hx₁⟩,
      Real.rpow_natCast]

/-- The distance cdf is the proportion of the ball occupied by the concentric ball of radius
`x`, with explicit support guards. At radius zero it is the cdf of `δ₀`. -/
theorem cdf_map_norm_sub_uniformBallMeasure (c : E) (hr : 0 ≤ r) (x : ℝ) :
    cdf ((uniformBallMeasure c r).map (fun y ↦ ‖y - c‖)) x =
      if x < 0 then 0 else if r ≤ x then 1 else (x / r) ^ finrank ℝ E := by
  rcases hr.eq_or_lt with rfl | hr
  · simp only [uniformBallMeasure_zero_right, Measure.map_dirac, sub_self,
      norm_zero, cdf_dirac]
    split_ifs <;> first | rfl | linarith
  have hmap : (uniformBallMeasure c r).map (fun y ↦ ‖y - c‖) =
      ((uniformBallMeasure c r).map (fun y ↦ ‖y - c‖ / r)).map (fun y ↦ 0 + r * y) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    ext y
    simp only [Function.comp_apply, zero_add]
    exact (mul_div_cancel₀ _ hr.ne').symm
  have := isProbabilityMeasure_uniformBallMeasure (c := c) hr.le
  rw [hmap, cdf_map_affine_of_pos hr, sub_zero,
    cdf_map_norm_sub_div_uniformBallMeasure c hr]
  simp [div_neg_iff, hr.not_gt, hr, le_div_iff₀ hr]

/-- The normalized radius has the power-function quantile `u ^ d⁻¹` at every interior level. -/
theorem quantile_map_norm_sub_div_uniformBallMeasure (c : E) (hr : 0 < r)
    (hu : u ∈ Ioo 0 1) :
    ((uniformBallMeasure c r).map (fun x ↦ ‖x - c‖ / r)).quantile u =
      u ^ (finrank ℝ E : ℝ)⁻¹ := by
  rw [map_norm_sub_div_uniformBallMeasure c hr,
    quantile_betaMeasure_one_right (Nat.cast_pos.2 finrank_pos) hu]

/-- The distance from the center has quantile `r * u ^ d⁻¹`, also when `r = 0`. -/
theorem quantile_map_norm_sub_uniformBallMeasure (c : E) (hr : 0 ≤ r)
    (hu : u ∈ Ioo 0 1) :
    ((uniformBallMeasure c r).map (fun x ↦ ‖x - c‖)).quantile u =
      r * u ^ (finrank ℝ E : ℝ)⁻¹ := by
  have := isProbabilityMeasureBeta (Nat.cast_pos.2 (finrank_pos (R := ℝ) (M := E))) one_pos
  rw [map_norm_sub_uniformBallMeasure c hr, Measure.quantile_map_const_mul hr hu.1 hu.2,
    quantile_betaMeasure_one_right (Nat.cast_pos.2 finrank_pos) hu]

/-- Radius quantiles tend to zero as the probability level tends to zero from above. -/
theorem tendsto_quantile_map_norm_sub_uniformBallMeasure_nhdsGT_zero (c : E) (hr : 0 ≤ r) :
    Tendsto ((uniformBallMeasure c r).map (fun x ↦ ‖x - c‖)).quantile
      (𝓝[>] 0) (𝓝 0) := by
  have := isProbabilityMeasureBeta (Nat.cast_pos.2 (finrank_pos (R := ℝ) (M := E))) one_pos
  rw [map_norm_sub_uniformBallMeasure c hr]
  have h := (tendsto_quantile_betaMeasure_nhdsGT_zero
    (Nat.cast_pos.2 (finrank_pos (R := ℝ) (M := E))) one_pos).const_mul r
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  exact (Measure.quantile_map_const_mul hr hu.1 hu.2).symm

/-- Radius quantiles tend to the ball radius as the probability level tends to one from below. -/
theorem tendsto_quantile_map_norm_sub_uniformBallMeasure_nhdsLT_one (c : E) (hr : 0 ≤ r) :
    Tendsto ((uniformBallMeasure c r).map (fun x ↦ ‖x - c‖)).quantile
      (𝓝[<] 1) (𝓝 r) := by
  have := isProbabilityMeasureBeta (Nat.cast_pos.2 (finrank_pos (R := ℝ) (M := E))) one_pos
  rw [map_norm_sub_uniformBallMeasure c hr]
  have h := (tendsto_quantile_betaMeasure_nhdsLT_one
    (Nat.cast_pos.2 (finrank_pos (R := ℝ) (M := E))) one_pos).const_mul r
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact (Measure.quantile_map_const_mul hr hu.1 hu.2).symm

end TauCeti.Probability
