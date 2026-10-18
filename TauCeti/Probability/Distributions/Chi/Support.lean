/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Chi.Basic
public import TauCeti.MeasureTheory.Measure.Dirac
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Support of chi distributions

This file identifies the topological support of every chi law. At positive degrees and scale the
law is almost surely positive, but zero remains in its support because the density is positive at
every positive point. Degree zero gives a point mass at zero, while invalid degrees or scales give
the zero measure.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  second edition, Wiley, 1994, chapter 18.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Probability

/-- For positive degrees and scale, the function support of the chi density is the positive
half-line. -/
@[simp]
theorem support_chiPDF {k s : ℝ} (hk : 0 < k) (hs : 0 < s) :
    Function.support (chiPDF k s) = Ioi 0 := by
  ext x
  rw [Function.mem_support]
  simp only [mem_Ioi]
  constructor
  · intro hx
    by_contra h
    exact hx (chiPDF_of_nonpos (le_of_not_gt h))
  · intro hx
    rw [chiPDF_eq_ofReal, ENNReal.ofReal_ne_zero_iff]
    exact (chiPDFReal_pos_iff hk hs).2 hx

/-- The topological support of a chi law is the closed nonnegative half-line at positive degrees
and scale, the singleton zero at degree zero and positive scale, and empty in every invalid
parameter regime. -/
@[simp]
theorem support_chiMeasure (k s : ℝ) :
    (chiMeasure k s).support =
      if 0 < s then if k = 0 then {0} else if 0 < k then Ici 0 else ∅ else ∅ := by
  by_cases hs : 0 < s
  · simp only [hs, ite_true]
    rcases lt_trichotomy k 0 with hk | rfl | hk
    · simp [hk.ne, not_lt.mpr hk.le, chiMeasure_of_neg hk]
    · simp [chiMeasure_zero hs, Measure.support_dirac]
    · simp only [hk.ne', hk, ite_false, ite_true]
      rw [chiMeasure_eq_withDensity hk hs,
        Measure.support_withDensity_eq_closure (measurable_chiPDF k s) isOpen_Ioi
          (support_chiPDF hk hs), closure_Ioi]
  · simp [hs, chiMeasure_of_scale_nonpos (le_of_not_gt hs)]

end TauCeti.Probability
