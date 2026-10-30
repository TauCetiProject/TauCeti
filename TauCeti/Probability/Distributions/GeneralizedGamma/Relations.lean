/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.GeneralizedGamma.Cdf
public import TauCeti.Probability.Distributions.GeneralizedExtremeValue.Basic
public import TauCeti.Probability.Distributions.InverseGamma.Basic
public import TauCeti.Probability.Distributions.Nakagami.Basic
public import TauCeti.Probability.Distributions.Weibull.Basic

/-!
# Specializations of generalized gamma laws

Generalized gamma laws include Weibull, inverse-gamma, chi, and Nakagami laws.
At shape one their negative power parameters give Fréchet laws, and reflection of
their positive-power counterparts gives reversed Weibull laws. The latter two are
identified with the maximum-convention generalized extreme-value family, including
the location and scale changes.

These measure equalities let the density, quantile, and sharp real-power moment APIs
for the individual families be used interchangeably with the generalized gamma API.
Chi degree zero remains its separate Dirac boundary: its generalized gamma shape
would be zero, which is outside that family's probability domain.

The identifications reuse `gammaMeasure_map_const_mul`, the defining Gamma
pushforwards, and the existing cumulative distribution functions.

## References

* E. W. Stacy, *A Generalization of the Gamma Distribution*, Annals of Mathematical
  Statistics 33 (1962), 1187–1192. We also allow negative power parameters.
* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer
  (2001), Chapter 3, for the maximum-convention extreme-value parameterization.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {a c s k m Ω ξ : ℝ}

/-- Shape-one generalized gamma laws with positive power parameter are Weibull laws
with that shape and the same scale, including the zero laws at nonpositive scale. -/
theorem generalizedGammaMeasure_one_shape_eq_weibullMeasure (hc : 0 < c) :
    generalizedGammaMeasure 1 c s = weibullMeasure c s := by
  by_cases hs : 0 < s
  swap
  · rw [generalizedGammaMeasure_of_not_valid (by tauto), weibullMeasure_of_not_pos (by tauto)]
  let _ := isProbabilityMeasure_generalizedGammaMeasure zero_lt_one hc.ne' hs
  let _ := isProbabilityMeasure_weibullMeasure hc hs
  apply Measure.eq_of_cdf
  ext x
  rw [cdf_generalizedGammaMeasure_eq zero_lt_one hc.ne' hs,
    cdf_weibullMeasure_eq hc hs, ite_eq_left hc]
  split_ifs with hx
  · rfl
  · rw [regularizedGamma_one (rpow_nonneg (div_nonneg (not_le.mp hx).le hs.le) _)]

/-- Power parameter `-1` recovers the inverse-gamma law, with generalized gamma
scale equal to the rate of the Gamma variable before inversion, including invalid parameters. -/
theorem generalizedGammaMeasure_neg_one_eq_inverseGammaMeasure (a s : ℝ) :
    generalizedGammaMeasure a (-1) s = inverseGammaMeasure a s := by
  by_cases h : 0 < a ∧ 0 < s
  swap
  · rw [generalizedGammaMeasure_of_not_valid (by tauto), inverseGammaMeasure_of_not_pos h]
  obtain ⟨ha, hs⟩ := h
  have hscale : (gammaMeasure a 1).map (s⁻¹ * ·) = gammaMeasure a s := by
    simpa using gammaMeasure_map_const_mul ha zero_lt_one (inv_pos.mpr hs)
  rw [generalizedGammaMeasure_of_valid ha (by norm_num) hs,
    inverseGammaMeasure_of_pos ha hs, ← hscale,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp [Real.rpow_neg_one, mul_inv_rev, mul_comm]

/-- A chi law of positive degree `k` and scale `s` is generalized gamma with
shape `k / 2`, power parameter `2`, and scale `√2 * s`, including nonpositive scale. -/
theorem chiMeasure_eq_generalizedGammaMeasure (hk : 0 < k) :
    chiMeasure k s = generalizedGammaMeasure (k / 2) 2 (√2 * s) := by
  by_cases hs : 0 < s
  swap
  · rw [chiMeasure_of_scale_nonpos (not_lt.mp hs),
      generalizedGammaMeasure_of_not_valid (by
        have : √2 * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sqrt_nonneg _) (not_lt.mp hs)
        grind)]
  have hscale : (gammaMeasure (k / 2) 1).map (2 * ·) =
      gammaMeasure (k / 2) (1 / 2) :=
    gammaMeasure_map_const_mul (half_pos hk) zero_lt_one (by norm_num)
  rw [chiMeasure_eq_map_gammaMeasure hk hs, ← hscale,
    Measure.map_map (by fun_prop) (by fun_prop),
    generalizedGammaMeasure_of_valid (half_pos hk) (by norm_num) (by positivity)]
  congr 1
  funext x
  rw [Function.comp_apply, sqrt_mul (by norm_num)]
  simp only [sqrt_eq_rpow, one_div]
  ring

/-- A Nakagami law is generalized gamma with power parameter `2` and scale
`√(Ω / m)`. This holds for every positive shape, including shapes below one half,
and for the zero laws at invalid parameters. -/
theorem nakagamiMeasure_eq_generalizedGammaMeasure (m Ω : ℝ) :
    nakagamiMeasure m Ω = generalizedGammaMeasure m 2 (√(Ω / m)) := by
  by_cases hm : 0 < m
  swap
  · rw [nakagamiMeasure_of_not_pos (by tauto),
      generalizedGammaMeasure_of_not_valid (by tauto)]
  by_cases hΩ : 0 < Ω
  swap
  · have hs : √(Ω / m) = 0 :=
      sqrt_eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (not_lt.mp hΩ) hm.le)
    simp [nakagamiMeasure_of_not_pos (by tauto : ¬ (0 < m ∧ 0 < Ω)), hs]
  rw [nakagamiMeasure_eq_chiMeasure hm hΩ,
    chiMeasure_eq_generalizedGammaMeasure (by positivity)]
  congr 1
  · ring
  · rw [← sqrt_mul (by norm_num)]
    congr 1
    field_simp

/-- At nonzero shape, a generalized extreme-value law is the affine image of a
shape-one generalized gamma law with power parameter `(-ξ)⁻¹` and unit scale. -/
theorem generalizedExtremeValueMeasure_eq_map_generalizedGammaMeasure
    (hs : 0 < s) (hξ : ξ ≠ 0) (m : ℝ) :
    generalizedExtremeValueMeasure m s ξ =
      (generalizedGammaMeasure 1 (-ξ)⁻¹ 1).map
        (fun x ↦ (m - s / ξ) + (s / ξ) * x) := by
  rw [generalizedGammaMeasure_of_valid zero_lt_one
      (inv_ne_zero (neg_ne_zero.mpr hξ)) zero_lt_one,
    Measure.map_map (by fun_prop) (by fun_prop),
    generalizedExtremeValueMeasure_of_shape_ne_zero hs hξ, expMeasure]
  congr 1
  funext x
  simp only [Function.comp_apply, inv_inv, one_mul]
  ring

/-- The Fréchet law of shape `c` and scale `s` is both generalized gamma with
parameters `(1, -c, s)` and GEV with location `s`, scale `s / c`, and shape `c⁻¹`.
The equality includes the zero laws at nonpositive scale. -/
theorem generalizedGammaMeasure_one_shape_neg_eq_generalizedExtremeValueMeasure
    (hc : 0 < c) :
    generalizedGammaMeasure 1 (-c) s =
      generalizedExtremeValueMeasure s (s / c) c⁻¹ := by
  by_cases hs : 0 < s
  swap
  · rw [generalizedGammaMeasure_of_not_valid (by tauto),
      generalizedExtremeValueMeasure_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (not_lt.mp hs) hc.le)]
  rw [generalizedGammaMeasure_of_valid zero_lt_one (neg_ne_zero.mpr hc.ne') hs,
    generalizedExtremeValueMeasure_of_pos (div_pos hs hc), expMeasure]
  apply Measure.map_congr
  filter_upwards [ae_pos_gammaMeasure 1 1] with x hx
  rw [generalizedExtremeValueMap_eq_rpow hx, ite_eq_right (inv_ne_zero hc.ne')]
  simp only [inv_neg]
  field_simp
  ring

/-- The maximum-convention GEV specialization representing Fréchet has cdf
`exp (-(x / s) ^ (-c))` on the positive half-line and zero below it. -/
theorem cdf_generalizedExtremeValueMeasure_frechet (hc : 0 < c) (hs : 0 < s) (x : ℝ) :
    cdf (generalizedExtremeValueMeasure s (s / c) c⁻¹) x =
      if x ≤ 0 then 0 else exp (-(x / s) ^ (-c)) := by
  rw [← generalizedGammaMeasure_one_shape_neg_eq_generalizedExtremeValueMeasure hc,
    cdf_generalizedGammaMeasure_eq zero_lt_one (neg_ne_zero.mpr hc.ne') hs,
    ite_eq_right (by linarith : ¬ 0 < -c)]
  split_ifs with hx
  · rfl
  · rw [regularizedGamma_one (rpow_nonneg (div_nonneg (not_le.mp hx).le hs.le) _)]
    ring

/-- Reflecting a Weibull law gives a reversed Weibull law: GEV location `-s`,
scale `s / c`, and shape `-c⁻¹`, including the zero laws at nonpositive scale. -/
@[simp]
theorem weibullMeasure_map_neg (hc : 0 < c) :
    (weibullMeasure c s).map Neg.neg =
      generalizedExtremeValueMeasure (-s) (s / c) (-c⁻¹) := by
  rw [← generalizedGammaMeasure_one_shape_eq_weibullMeasure hc]
  by_cases hs : 0 < s
  swap
  · rw [generalizedGammaMeasure_of_not_valid (by tauto), Measure.map_zero,
      generalizedExtremeValueMeasure_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg (not_lt.mp hs) hc.le)]
  rw [generalizedGammaMeasure_of_valid zero_lt_one hc.ne' hs,
    Measure.map_map (by fun_prop) (by fun_prop),
    generalizedExtremeValueMeasure_of_pos (div_pos hs hc), expMeasure]
  apply Measure.map_congr
  filter_upwards [ae_pos_gammaMeasure 1 1] with x hx
  rw [generalizedExtremeValueMap_eq_rpow hx,
    ite_eq_right (neg_ne_zero.mpr (inv_ne_zero hc.ne'))]
  simp only [Function.comp_apply, neg_neg]
  field_simp
  ring

end TauCeti.Probability
