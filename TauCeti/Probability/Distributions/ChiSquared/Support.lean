/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.ChiSquared.Basic
public import TauCeti.MeasureTheory.Measure.Dirac
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# Support of chi-squared laws

Positive-degree chi-squared laws have no atoms, are almost surely positive, and have topological
support `[0, ∞)`. At degree zero the support is the singleton zero; negative degrees give the zero
measure. These statements also describe the components used in Poisson mixtures of chi-squared
laws.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- A chi-squared law of positive degree has no atoms. -/
theorem nullSingletonClass_chiSquaredMeasure {k : ℝ} (hk : 0 < k) :
    NullSingletonClass (chiSquaredMeasure k) := by
  rw [chiSquaredMeasure_eq_gammaMeasure hk]
  infer_instance

/-- A chi-squared variable of positive degree is positive almost surely. -/
theorem ae_pos_chiSquaredMeasure {k : ℝ} (hk : 0 < k) :
    ∀ᵐ x ∂chiSquaredMeasure k, 0 < x := by
  rw [chiSquaredMeasure_eq_gammaMeasure hk]
  exact ae_pos_gammaMeasure _ _

/-- Every chi-squared measure is carried by the nonnegative half-line, including its Dirac
and invalid zero-measure cases. -/
theorem ae_nonneg_chiSquaredMeasure (k : ℝ) :
    ∀ᵐ x ∂chiSquaredMeasure k, 0 ≤ x := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · simp [chiSquaredMeasure_of_neg hk]
  · simp [chiSquaredMeasure_zero]
  · exact (ae_pos_chiSquaredMeasure hk).mono fun _ hx ↦ hx.le

/-- The topological support of a chi-squared law, in every degree regime. -/
@[simp]
theorem support_chiSquaredMeasure (k : ℝ) :
    (chiSquaredMeasure k).support =
      if k = 0 then {0} else if 0 < k then Ici 0 else ∅ := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · simp [chiSquaredMeasure_of_neg hk, hk.ne, not_lt.mpr hk.le]
  · simp [chiSquaredMeasure_zero]
  · simp only [hk.ne', hk, ite_false, ite_true]
    rw [chiSquaredMeasure_eq_gammaMeasure hk, gammaMeasure_eq_withDensity_restrict_Ioi,
      ← withDensity_indicator measurableSet_Ioi]
    apply (Measure.support_withDensity_eq_closure
      ((measurable_gammaPDF (k / 2) (1 / 2)).indicator measurableSet_Ioi)
      isOpen_Ioi ?_).trans (closure_Ioi 0)
    ext x
    by_cases hx : 0 < x
    · simp only [Function.mem_support, mem_Ioi, hx, indicator_of_mem, iff_true, gammaPDF]
      exact ENNReal.ofReal_ne_zero_iff.mpr
        (gammaPDFReal_pos (a := k / 2) (r := 1 / 2) (by positivity) (by norm_num) hx)
    · simp [Function.mem_support, hx]

end TauCeti.Probability
