/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Exponential.Basic
public import TauCeti.Probability.Hazard

/-!
# The exponential hazard

The exponential law has constant hazard equal to its rate on the nonnegative half-line.
Its integrated hazard is `r * x`. The survival is positive at every finite point, so the
density-based hazard is integrable on every compact interval.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, Vol. 1,
  2nd ed., Wiley, 1994.
-/

public section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

namespace TauCeti.Probability

variable {r x : ℝ}

/-- The hazard rate of an exponential law is its rate, including at zero. -/
@[simp]
theorem exponentialPDFReal_div_one_sub_cdf (hr : 0 < r) (hx : 0 ≤ x) :
    exponentialPDFReal r x / (1 - cdf (expMeasure r) x) = r := by
  simp [exponentialPDFReal, gammaPDFReal, hx, cdf_expMeasure_eq hr,
    Real.exp_ne_zero]

/-- The cumulative exponential hazard has constant derivative equal to the rate at every
positive point. -/
theorem hasDerivAt_neg_log_one_sub_cdf_expMeasure (hr : 0 < r) (hx : 0 < x) :
    HasDerivAt (fun t => -Real.log (1 - cdf (expMeasure r) t)) r x := by
  have hd : HasDerivAt (fun t : ℝ => r * t) r x := by
    simpa using (hasDerivAt_id x).const_mul r
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hx] with t ht
  simp [cdf_expMeasure_eq hr, ht.le, Real.log_exp]

/-- The exponential hazard is integrable on every compact interval. -/
theorem intervalIntegrable_exponentialPDFReal_div_one_sub_cdf (hr : 0 < r) (a b : ℝ) :
    IntervalIntegrable (fun t => exponentialPDFReal r t / (1 - cdf (expMeasure r) t))
      volume a b := by
  let _ := isProbabilityMeasure_expMeasure hr
  exact intervalIntegrable_div_one_sub_cdf_of_eq_withDensity
    (by rw [expMeasure_eq_withDensity]; rfl)
    (measurable_exponentialPDFReal r).aemeasurable
    (ae_of_all _ (exponentialPDFReal_nonneg hr)) a b
    (fun t _ => cdf_expMeasure_lt_one hr t)

/-- The integrated exponential hazard on `[0, x]` is `r * x`. -/
@[simp]
theorem integral_exponentialPDFReal_div_one_sub_cdf (hr : 0 < r) (hx : 0 ≤ x) :
    ∫ t in (0 : ℝ)..x, exponentialPDFReal r t / (1 - cdf (expMeasure r) t) = r * x := by
  rw [intervalIntegral.integral_congr fun t ht =>
    exponentialPDFReal_div_one_sub_cdf hr ((uIcc_of_le hx ▸ ht).1)]
  simp [mul_comm]

end TauCeti.Probability
