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

In particular, every open right half-line `(c, ∞)` has positive measure when the degree is positive.
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

/-- For positive degrees of freedom, every open right half-line `(c, ∞)` has positive
chi-squared measure. -/
theorem measure_Ioi_chiSquaredMeasure_pos {k : ℝ} (hk : 0 < k) (c : ℝ) :
    0 < chiSquaredMeasure k (Ioi c) := by
  have hmem : max c 0 + 1 ∈ (chiSquaredMeasure k).support := by
    simp only [support_chiSquaredMeasure, hk.ne', hk, ite_false, ite_true]
    exact (le_max_right c 0).trans (le_add_of_nonneg_right zero_le_one)
  exact (Measure.mem_support_iff_forall _).1 hmem (Ioi c)
    (isOpen_Ioi.mem_nhds ((le_max_left c 0).trans_lt (lt_add_one _)))

/-- For positive degrees of freedom, every open right half-line `(c, ∞)` has positive real
chi-squared probability. -/
theorem measureReal_Ioi_chiSquaredMeasure_pos {k : ℝ} (hk : 0 < k) (c : ℝ) :
    0 < (chiSquaredMeasure k).real (Ioi c) := by
  have := isProbabilityMeasure_chiSquaredMeasure hk.le
  exact ENNReal.toReal_pos (measure_Ioi_chiSquaredMeasure_pos hk c).ne' (measure_ne_top _ _)

end TauCeti.Probability
