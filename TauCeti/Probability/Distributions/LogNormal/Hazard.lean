/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.LogNormal.Basic
public import TauCeti.Probability.Hazard

/-!
# The log-normal hazard

At positive log-variance the log-normal survival is strictly positive at every finite point.
The density divided by survival is integrable on every compact interval and its integral
from zero is the negative logarithm of the Gaussian tail at the logarithmic argument.
The zero-variance Dirac law is excluded from these density statements.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, Vol. 1,
  2nd ed., Wiley, 1994, Chapter 14.
-/

public section

open Filter MeasureTheory ProbabilityTheory Real Set Topology

open scoped NNReal

namespace TauCeti.Probability

variable {m x : ℝ} {v : ℝ≥0}

/-- The cumulative log-normal hazard has derivative equal to the density divided by survival
at every positive point. -/
theorem hasDerivAt_neg_log_one_sub_cdf_logNormalMeasure
    (m : ℝ) (hv : v ≠ 0) (hx : 0 < x) :
    HasDerivAt (fun t => -Real.log (1 - cdf (logNormalMeasure m v) t))
      (logNormalPDFReal m v x / (1 - cdf (logNormalMeasure m v) x)) x := by
  apply hasDerivAt_neg_log_one_sub_cdf ?_ (cdf_logNormalMeasure_lt_one m hv x)
  apply hasDerivAt_cdf_of_eq_withDensity
    (by rw [logNormalMeasure_eq_withDensity m hv, funext (logNormalPDF_eq_ofReal m v)])
    (measurable_logNormalPDFReal m v).aemeasurable (ae_of_all _ (logNormalPDFReal_nonneg m v))
  have hc : ContinuousAt (fun t => (t * √(2 * π * v))⁻¹ *
      Real.exp (-(Real.log t - m) ^ 2 / (2 * v))) x := by
    fun_prop (disch := positivity)
  exact hc.congr_of_eventuallyEq
    ((eventually_gt_nhds hx).mono fun t ht => logNormalPDFReal_of_pos ht m v)

/-- The log-normal hazard is integrable on every compact interval. -/
theorem intervalIntegrable_logNormalPDFReal_div_one_sub_cdf
    (m : ℝ) (hv : v ≠ 0) (a b : ℝ) :
    IntervalIntegrable (fun t => logNormalPDFReal m v t / (1 - cdf (logNormalMeasure m v) t))
      volume a b := by
  exact intervalIntegrable_div_one_sub_cdf_of_eq_withDensity
    (by rw [logNormalMeasure_eq_withDensity m hv, funext (logNormalPDF_eq_ofReal m v)])
    (measurable_logNormalPDFReal m v).aemeasurable
    (ae_of_all _ (logNormalPDFReal_nonneg m v)) a b
    (fun t _ => cdf_logNormalMeasure_lt_one m hv t)

/-- The integrated log-normal hazard on the positive half-line, expressed through the error
function. At zero the integral is zero. -/
theorem integral_logNormalPDFReal_div_one_sub_cdf
    (m : ℝ) (hv : v ≠ 0) (hx : 0 < x) :
    ∫ t in (0 : ℝ)..x, logNormalPDFReal m v t / (1 - cdf (logNormalMeasure m v) t) =
      -Real.log ((1 - Real.erf ((Real.log x - m) / √(2 * (v : ℝ)))) / 2) := by
  rw [integral_div_one_sub_cdf_of_eq_withDensity
    (by rw [logNormalMeasure_eq_withDensity m hv, funext (logNormalPDF_eq_ofReal m v)])
    (measurable_logNormalPDFReal m v).aemeasurable
    (ae_of_all _ (logNormalPDFReal_nonneg m v))
    (measure_mono_null Iio_subset_Iic_self (logNormalMeasure_Iic_zero m v))
    (cdf_logNormalMeasure_lt_one m hv x), cdf_logNormalMeasure_eq m hv,
    ite_eq_right hx.not_ge]
  congr 2
  ring

end TauCeti.Probability
