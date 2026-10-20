/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gamma.Cdf
public import TauCeti.Probability.Hazard

/-!
# The Gamma hazard

For positive shape and rate, the Gamma survival is `1 - regularizedGamma a (r * x)`.
It is positive at every finite point. Dividing the density by this survival gives a hazard
integrable on every compact interval, including at zero when the shape is below one.
Its integral from zero is the negative logarithm of survival.

## References

* NIST Digital Library of Mathematical Functions, §8.2 (incomplete Gamma functions).
-/

public section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

variable {a r x : ℝ}

/-- The cumulative Gamma hazard has derivative equal to the density divided by survival at
every positive point. No differentiability at zero is asserted for shapes below one. -/
theorem hasDerivAt_neg_log_one_sub_cdf_gammaMeasure
    (ha : 0 < a) (hr : 0 < r) (hx : 0 < x) :
    HasDerivAt (fun t => -Real.log (1 - cdf (gammaMeasure a r) t))
      (gammaPDFReal a r x / (1 - cdf (gammaMeasure a r) x)) x := by
  let _ := isProbabilityMeasure_gammaMeasure ha hr
  apply hasDerivAt_neg_log_one_sub_cdf ?_ (cdf_gammaMeasure_lt_one ha hr x)
  apply hasDerivAt_cdf_of_eq_withDensity (gammaMeasure_eq_withDensity_ofReal a r)
    (measurable_gammaPDFReal a r).aemeasurable (ae_of_all _ (gammaPDFReal_nonneg ha hr))
  have hc : ContinuousAt (fun t => r ^ a / Real.Gamma a * t ^ (a - 1) *
      Real.exp (-(r * t))) x :=
    (continuousAt_const.mul (Real.continuousAt_rpow_const x (a - 1) (.inl hx.ne'))).mul
      (by fun_prop)
  exact hc.congr_of_eventuallyEq
    ((eventually_gt_nhds hx).mono fun t ht => gammaPDFReal_of_nonneg ht.le)

/-- The Gamma hazard is integrable on every compact interval, including across zero. -/
theorem intervalIntegrable_gammaPDFReal_div_one_sub_cdf
    (ha : 0 < a) (hr : 0 < r) (l u : ℝ) :
    IntervalIntegrable (fun t => gammaPDFReal a r t / (1 - cdf (gammaMeasure a r) t))
      volume l u := by
  let _ := isProbabilityMeasure_gammaMeasure ha hr
  exact intervalIntegrable_div_one_sub_cdf_of_eq_withDensity
    (gammaMeasure_eq_withDensity_ofReal a r) (measurable_gammaPDFReal a r).aemeasurable
    (ae_of_all _ (gammaPDFReal_nonneg ha hr)) l u
    (fun t _ => cdf_gammaMeasure_lt_one ha hr t)

/-- The integrated Gamma hazard is the negative logarithm of its regularized-Gamma tail.
The formula holds also at nonpositive `x`, where both sides vanish. -/
theorem integral_gammaPDFReal_div_one_sub_cdf (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    ∫ t in (0 : ℝ)..x, gammaPDFReal a r t / (1 - cdf (gammaMeasure a r) t) =
      -Real.log (1 - regularizedGamma a (r * x)) := by
  let _ := isProbabilityMeasure_gammaMeasure ha hr
  rw [integral_div_one_sub_cdf_of_eq_withDensity
    (gammaMeasure_eq_withDensity_ofReal a r) (measurable_gammaPDFReal a r).aemeasurable
    (ae_of_all _ (gammaPDFReal_nonneg ha hr))
    (measure_mono_null Iio_subset_Iic_self (by
      simpa only [ae_iff, not_lt, ← Iic_def] using ae_pos_gammaMeasure a r))
    (cdf_gammaMeasure_lt_one ha hr x), cdf_gammaMeasure_eq ha hr]

end TauCeti.Probability
