/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Hyperexponential.Basic
import TauCeti.Probability.Cdf

/-!
# Strict increase of hyperexponential cdfs

A valid hyperexponential cdf is strictly increasing on the nonnegative half-line,
positive exactly at positive cutoffs, and strictly below one at every finite cutoff.
These properties make interior quantiles unique positive roots of the finite survival sum.
Only positive-weight components need positive rates.

## References

* S. Asmussen, *Applied Probability and Queues*, 2nd ed., Springer (2003), Chapter III, §4.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] {p : Convexity.StdSimplex ℝ≥0 ι} {r : ι → ℝ} {x : ℝ}

/-- The cdf increases strictly throughout the nonnegative half-line, including from zero. -/
theorem strictMonoOn_cdf_hyperexponentialMeasure
    (hr : ∀ i, 0 < p.weights i → 0 < r i) :
    StrictMonoOn (cdf (hyperexponentialMeasure p r)) (Ici 0) := by
  let _ := isProbabilityMeasure_hyperexponentialMeasure hr
  exact Measure.strictMonoOn_cdf_of_subset_support _ ordConnected_Ici
    (by rw [support_hyperexponentialMeasure hr])

/-- The cdf is positive exactly at positive cutoffs. -/
@[simp]
theorem cdf_hyperexponentialMeasure_pos_iff
    (hr : ∀ i, 0 < p.weights i → 0 < r i) :
    0 < cdf (hyperexponentialMeasure p r) x ↔ 0 < x := by
  constructor
  · intro hx
    by_contra h
    simp [cdf_hyperexponentialMeasure_eq hr x, le_of_not_gt h] at hx
  · intro hx
    exact (cdf_nonneg _ 0).trans_lt
      (strictMonoOn_cdf_hyperexponentialMeasure hr (by simp) hx.le hx)

/-- Every finite cutoff leaves positive upper-tail probability. -/
theorem cdf_hyperexponentialMeasure_lt_one
    (hr : ∀ i, 0 < p.weights i → 0 < r i) (x : ℝ) :
    cdf (hyperexponentialMeasure p r) x < 1 :=
  Measure.cdf_lt_one_of_strictMonoOn_Ici _ (strictMonoOn_cdf_hyperexponentialMeasure hr) x

end TauCeti.Probability
