/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.MeasureTheory.Measure.Support
public import TauCeti.Probability.Distributions.Weibull.Basic
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Support of Weibull distributions

This file identifies the function support of the Weibull density and the topological support of
the corresponding measure. At positive shape and scale, the law is almost surely strictly
positive, but zero belongs to its topological support because the density is positive at every
positive point. Invalid parameters give the zero measure and hence empty support.

## Main results

* `TauCeti.Probability.support_weibullPDF` — the density is nonzero exactly on `(0, ∞)`;
* `TauCeti.Probability.support_weibullMeasure` — the law has support `[0, ∞)` exactly when both
  parameters are positive, and empty support otherwise.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  second edition, Wiley, 1994, chapter 21.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Probability

/-- For positive shape and scale, the function support of the Weibull density is the positive
half-line. -/
@[simp]
theorem support_weibullPDF {k lam : ℝ} (hk : 0 < k) (hlam : 0 < lam) :
    Function.support (weibullPDF k lam) = Ioi 0 := by
  ext x
  rw [Function.mem_support]
  simp only [mem_Ioi]
  constructor
  · intro hx
    by_contra h
    exact hx (weibullPDF_of_nonpos (le_of_not_gt h) k lam)
  · intro hx
    rw [weibullPDF_eq_ofReal, ENNReal.ofReal_ne_zero_iff]
    exact (weibullPDFReal_pos_iff hk hlam).2 hx

/-- The topological support of a Weibull law is the closed nonnegative half-line at positive
shape and scale, and empty when either parameter is invalid. -/
@[simp]
theorem support_weibullMeasure (k lam : ℝ) :
    (weibullMeasure k lam).support = if 0 < k ∧ 0 < lam then Ici 0 else ∅ := by
  by_cases hvalid : 0 < k ∧ 0 < lam
  · rw [ite_eq_left hvalid, weibullMeasure_def,
      Measure.support_withDensity_eq_closure (measurable_weibullPDF k lam) isOpen_Ioi
        (support_weibullPDF hvalid.1 hvalid.2), closure_Ioi]
  · rw [ite_eq_right hvalid, weibullMeasure_of_not_pos hvalid, Measure.support_zero]

end TauCeti.Probability
