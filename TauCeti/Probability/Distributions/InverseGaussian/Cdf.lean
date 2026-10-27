/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.InverseGaussian.Basic
import TauCeti.Probability.Cdf

/-!
# Strict increase of inverse Gaussian cdfs

At positive mean and shape, the inverse Gaussian cdf increases strictly on `[0, ∞)`,
is positive exactly on `(0, ∞)`, and stays below one at every finite cutoff.
These properties identify interior quantiles as unique positive roots of the explicit cdf.

The support argument follows the hyperexponential cdf API in
`TauCeti.Probability.Distributions.Hyperexponential.Cdf`.

## References

* R. S. Chhikara, J. L. Folks, *The Inverse Gaussian Distribution: Theory, Methodology, and
  Applications*, Marcel Dekker (1989).
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {μ lam x : ℝ}

/-- The inverse Gaussian cdf increases strictly on its nonnegative support. -/
theorem strictMonoOn_cdf_inverseGaussianMeasure (hμ : 0 < μ) (hlam : 0 < lam) :
    StrictMonoOn (cdf (inverseGaussianMeasure μ lam)) (Ici 0) := by
  let _ := isProbabilityMeasure_inverseGaussianMeasure hμ hlam
  exact Measure.strictMonoOn_cdf_of_subset_support _ ordConnected_Ici
    (by rw [support_inverseGaussianMeasure hμ hlam])

/-- The inverse Gaussian cdf is positive exactly at positive cutoffs. -/
@[simp]
theorem cdf_inverseGaussianMeasure_pos_iff (hμ : 0 < μ) (hlam : 0 < lam) :
    0 < cdf (inverseGaussianMeasure μ lam) x ↔ 0 < x := by
  constructor
  · intro hx
    by_contra h
    rw [cdf_inverseGaussianMeasure_of_nonpos hμ hlam (le_of_not_gt h)] at hx
    exact lt_irrefl _ hx
  · intro hx
    exact (cdf_nonneg _ 0).trans_lt
      (strictMonoOn_cdf_inverseGaussianMeasure hμ hlam (by simp) hx.le hx)

/-- Every finite cutoff leaves positive upper-tail mass under a valid inverse Gaussian law. -/
theorem cdf_inverseGaussianMeasure_lt_one (hμ : 0 < μ) (hlam : 0 < lam) (x : ℝ) :
    cdf (inverseGaussianMeasure μ lam) x < 1 :=
  Measure.cdf_lt_one_of_strictMonoOn_Ici _ (strictMonoOn_cdf_inverseGaussianMeasure hμ hlam) x

end TauCeti.Probability
