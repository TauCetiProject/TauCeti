/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.GeneralizedPareto.Cdf
public import TauCeti.Probability.Distributions.GeneralizedPareto.PDF
public import TauCeti.Probability.Hazard

/-!
# Generalized Pareto survival and hazard

At positive scale `s`, the generalized Pareto survival at a nonnegative `x` is positive
exactly when `s + ξ * x > 0`. On this region the hazard at positive `x` is
`1 / (s + ξ * x)`, and the cumulative hazard is `log (1 + ξ * x / s) / ξ`,
with the exponential branch `x / s` at shape zero.

The cumulative hazard includes the value zero at the lower endpoint. The chosen density
vanishes at that endpoint, so the pointwise hazard and derivative formulas assume `x > 0`.
The hazard is integrable on every compact interval where survival remains positive. Its
integral from zero equals the displayed cumulative hazard. At negative shape these statements
exclude the finite upper endpoint.

## References

* S. Coles, *An Introduction to Statistical Modeling of Extreme Values*, Springer (2001),
  Chapter 4.
-/

public section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

variable {s ξ x : ℝ}

/-- The generalized Pareto hazard at positive points of positive survival. -/
theorem generalizedParetoPDFReal_div_one_sub_cdf (hs : 0 < s) (hx : 0 < x)
    (hb : 0 < s + ξ * x) :
    generalizedParetoPDFReal s ξ x / (1 - cdf (generalizedParetoMeasure s ξ) x) =
      1 / (s + ξ * x) := by
  have hw : 0 < 1 + ξ * x / s := by
    have := div_pos hb hs
    simpa [add_div, hs.ne'] using this
  by_cases hξ : ξ = 0
  · subst ξ
    simp [generalizedParetoPDFReal_zero hs, hx, cdf_generalizedParetoMeasure_eq hs,
      hx.not_ge]
    field_simp
  rw [generalizedParetoPDFReal_of_shape_ne_zero hs hξ hx hw,
    cdf_generalizedParetoMeasure_of_shape_ne_zero hs hξ hx.le hw,
    sub_sub_cancel, Real.rpow_sub_one hw.ne']
  have hp : (1 + ξ * x / s) ^ (-ξ⁻¹) ≠ 0 := (Real.rpow_pos_of_pos hw _).ne'
  simp only [neg_div, one_div]
  field_simp

/-- The cumulative generalized Pareto hazard, including its value zero at the lower endpoint.
Shape zero uses the exponential formula. -/
theorem neg_log_one_sub_cdf_generalizedParetoMeasure (hs : 0 < s) (hx : 0 ≤ x)
    (hb : 0 < s + ξ * x) :
    -Real.log (1 - cdf (generalizedParetoMeasure s ξ) x) =
      if ξ = 0 then x / s else Real.log (1 + ξ * x / s) / ξ := by
  by_cases hξ : ξ = 0
  · subst ξ
    rw [generalizedParetoMeasure_zero hs, cdf_expMeasure_eq (inv_pos.mpr hs),
      ite_eq_left hx]
    simp [Real.log_exp, div_eq_mul_inv, mul_comm]
  have hw : 0 < 1 + ξ * x / s := by
    have := div_pos hb hs
    simpa [add_div, hs.ne'] using this
  rw [ite_eq_right hξ, cdf_generalizedParetoMeasure_of_shape_ne_zero hs hξ hx hw,
    sub_sub_cancel, Real.log_rpow hw]
  ring

/-- The cumulative generalized Pareto hazard has derivative equal to its hazard at every
positive point of positive survival. -/
theorem hasDerivAt_neg_log_one_sub_cdf_generalizedParetoMeasure
    (hs : 0 < s) (hx : 0 < x) (hb : 0 < s + ξ * x) :
    HasDerivAt (fun t => -Real.log (1 - cdf (generalizedParetoMeasure s ξ) t))
      (1 / (s + ξ * x)) x := by
  have heq : (fun t => -Real.log (1 - cdf (generalizedParetoMeasure s ξ) t)) =ᶠ[𝓝 x]
      fun t => if ξ = 0 then t / s else Real.log (1 + ξ * t / s) / ξ := by
    filter_upwards [eventually_gt_nhds hx,
      (by fun_prop : Continuous fun t : ℝ => s + ξ * t).continuousAt
        (eventually_gt_nhds hb)]
      with t ht hbt
    exact neg_log_one_sub_cdf_generalizedParetoMeasure hs ht.le hbt
  apply HasDerivAt.congr_of_eventuallyEq _ heq
  by_cases hξ : ξ = 0
  · subst ξ
    simpa using (hasDerivAt_id x).div_const s
  simp only [hξ, ↓reduceIte]
  have hw : 0 < 1 + ξ * x / s := by
    have := div_pos hb hs
    simpa [add_div, hs.ne'] using this
  convert (((((hasDerivAt_id x).const_mul ξ).div_const s).const_add 1).log hw.ne').div_const ξ
    using 1 <;> simp only [id_eq]
  field_simp

/-- The generalized Pareto hazard is integrable on every compact interval where survival
remains positive, as determined by its value at the larger endpoint. -/
theorem intervalIntegrable_generalizedParetoPDFReal_div_one_sub_cdf
    (hs : 0 < s) (a b : ℝ) (hS : cdf (generalizedParetoMeasure s ξ) (max a b) < 1) :
    IntervalIntegrable (fun t => generalizedParetoPDFReal s ξ t /
      (1 - cdf (generalizedParetoMeasure s ξ) t)) volume a b := by
  let _ := isProbabilityMeasure_generalizedParetoMeasure hs ξ
  apply intervalIntegrable_div_one_sub_cdf_of_eq_withDensity
    (by rw [generalizedParetoMeasure_eq_withDensity,
      funext (generalizedParetoPDF_eq_ofReal s ξ)])
    (measurable_generalizedParetoPDFReal s ξ).aemeasurable
    (ae_of_all _ (generalizedParetoPDFReal_nonneg s ξ))
  intro t ht
  exact (monotone_cdf _ ht.2).trans_lt hS

/-- Integrating the generalized Pareto hazard from zero gives its logarithmic cumulative
hazard, with the exponential branch at zero shape. -/
@[simp]
theorem integral_generalizedParetoPDFReal_div_one_sub_cdf
    (hs : 0 < s) (hx : 0 ≤ x) (hb : 0 < s + ξ * x) :
    ∫ t in (0 : ℝ)..x, generalizedParetoPDFReal s ξ t /
      (1 - cdf (generalizedParetoMeasure s ξ) t) =
        if ξ = 0 then x / s else Real.log (1 + ξ * x / s) / ξ := by
  let _ := isProbabilityMeasure_generalizedParetoMeasure hs ξ
  rw [integral_div_one_sub_cdf_of_eq_withDensity
    (by rw [generalizedParetoMeasure_eq_withDensity,
      funext (generalizedParetoPDF_eq_ofReal s ξ)])
    (measurable_generalizedParetoPDFReal s ξ).aemeasurable
    (ae_of_all _ (generalizedParetoPDFReal_nonneg s ξ))
    (measure_mono_null Iio_subset_Iic_self (by
      simpa only [ae_iff, not_lt, ← Iic_def] using
        (ae_pos_and_one_add_mul_div_pos_generalizedParetoMeasure s ξ).mono fun _ ht => ht.1))
    ((cdf_generalizedParetoMeasure_lt_one_iff hs hx).2 hb),
    neg_log_one_sub_cdf_generalizedParetoMeasure hs hx hb]

end TauCeti.Probability
