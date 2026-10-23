/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Weibull.Basic
public import TauCeti.Probability.Hazard

/-!
# The Weibull hazard

A Weibull law of shape `k` and scale `s` has hazard `(k / s) * (x / s) ^ (k - 1)`
at positive `x` and integrated hazard `(x / s) ^ k` on the nonnegative half-line.
The hazard is locally integrable even when `k < 1`, where its right limit at zero is infinite.
Pointwise hazard formulas therefore exclude zero, while the integrated formula includes it.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, Vol. 1,
  2nd ed., Wiley, 1994.
-/

public section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

variable {k s x : ℝ}

/-- The Weibull hazard on the positive half-line. -/
theorem weibullPDFReal_div_one_sub_cdf (hk : 0 < k) (hs : 0 < s) (hx : 0 < x) :
    weibullPDFReal k s x / (1 - cdf (weibullMeasure k s) x) =
      k / s * (x / s) ^ (k - 1) := by
  simp [weibullPDFReal_of_pos hk hs hx, cdf_weibullMeasure_eq hk hs, hx.not_ge,
    Real.exp_ne_zero]

/-- The cumulative Weibull hazard has derivative `(k / s) * (x / s) ^ (k - 1)` at every
positive point. -/
theorem hasDerivAt_neg_log_one_sub_cdf_weibullMeasure
    (hk : 0 < k) (hs : 0 < s) (hx : 0 < x) :
    HasDerivAt (fun t => -Real.log (1 - cdf (weibullMeasure k s) t))
      (k / s * (x / s) ^ (k - 1)) x := by
  have hd := ((hasDerivAt_id x).div_const s).rpow_const (p := k)
    (Or.inl (div_pos hx hs).ne')
  have heq : (fun t => -Real.log (1 - cdf (weibullMeasure k s) t)) =ᶠ[𝓝 x]
      fun t => (t / s) ^ k := by
    filter_upwards [eventually_gt_nhds hx] with t ht
    simp [cdf_weibullMeasure_eq hk hs, ht.not_ge, Real.log_exp]
  convert hd.congr_of_eventuallyEq heq using 1
  simp only [id_eq]
  ring

/-- The Weibull hazard is integrable on every compact interval, including across zero. -/
theorem intervalIntegrable_weibullPDFReal_div_one_sub_cdf
    (hk : 0 < k) (hs : 0 < s) (a b : ℝ) :
    IntervalIntegrable (fun t => weibullPDFReal k s t / (1 - cdf (weibullMeasure k s) t))
      volume a b := by
  let _ := isProbabilityMeasure_weibullMeasure hk hs
  exact intervalIntegrable_div_one_sub_cdf_of_eq_withDensity
    (by rw [weibullMeasure_def, funext (weibullPDF_eq_ofReal k s)])
    (measurable_weibullPDFReal k s).aemeasurable
    (ae_of_all _ (weibullPDFReal_nonneg k s)) a b
    (fun t _ => cdf_weibullMeasure_lt_one hk hs t)

/-- The integrated Weibull hazard on `[0, x]`, including the endpoint zero. -/
@[simp]
theorem integral_weibullPDFReal_div_one_sub_cdf
    (hk : 0 < k) (hs : 0 < s) (hx : 0 ≤ x) :
    ∫ t in (0 : ℝ)..x, weibullPDFReal k s t / (1 - cdf (weibullMeasure k s) t) =
      (x / s) ^ k := by
  let _ := isProbabilityMeasure_weibullMeasure hk hs
  rw [integral_div_one_sub_cdf_of_eq_withDensity
    (by rw [weibullMeasure_def, funext (weibullPDF_eq_ofReal k s)])
    (measurable_weibullPDFReal k s).aemeasurable
    (ae_of_all _ (weibullPDFReal_nonneg k s))
    (measure_mono_null Iio_subset_Iic_self (weibullMeasure_Iic_zero k s))
    (cdf_weibullMeasure_lt_one hk hs x), cdf_weibullMeasure_eq hk hs]
  rcases hx.eq_or_lt with rfl | hx
  · simp [hk.ne']
  · simp [hx.not_ge, Real.log_exp]

end TauCeti.Probability
