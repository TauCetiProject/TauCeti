/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.Probability.Distributions.Gamma.Support
public import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Support of chi-squared laws

Positive-degree chi-squared laws have topological support `[0, ∞)`. At degree zero the support is
the singleton zero; negative degrees give empty support. This also describes the components used
in Poisson mixtures of chi-squared laws.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- The topological support of a chi-squared law, in every degree regime. -/
@[simp]
theorem support_chiSquaredMeasure (k : ℝ) :
    (chiSquaredMeasure k).support =
      if k = 0 then {0} else if 0 < k then Ici 0 else ∅ := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · simp [chiSquaredMeasure_of_neg hk, hk.ne, not_lt.mpr hk.le]
  · simp [chiSquaredMeasure_zero]
  · simp only [hk.ne', hk, ite_false, ite_true]
    rw [chiSquaredMeasure_eq_gammaMeasure hk,
      support_gammaMeasure (by positivity) (by norm_num)]

end TauCeti.Probability
