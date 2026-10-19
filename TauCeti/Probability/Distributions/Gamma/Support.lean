/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gamma.Basic
public import Mathlib.MeasureTheory.Measure.Support
import TauCeti.MeasureTheory.Measure.WithDensity
import TauCeti.Probability.Distributions.Gamma.PDF

/-!
# Support of gamma laws

A gamma law with positive shape and rate has topological support `[0, ∞)`, although it is
almost surely strictly positive. This support formula also applies to chi-squared laws through
their gamma representation.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- A gamma law with positive shape and rate has topological support `[0, ∞)`. -/
@[simp]
theorem support_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    (gammaMeasure a r).support = Ici 0 := by
  rw [gammaMeasure_eq_withDensity_restrict_Ioi, ← withDensity_indicator measurableSet_Ioi]
  apply (Measure.support_withDensity_eq_closure
    ((measurable_gammaPDF a r).indicator measurableSet_Ioi)
    isOpen_Ioi ?_).trans (closure_Ioi 0)
  ext x
  by_cases hx : 0 < x
  · simp only [Function.mem_support, mem_Ioi, hx, indicator_of_mem, iff_true, gammaPDF]
    exact ENNReal.ofReal_ne_zero_iff.mpr (gammaPDFReal_pos ha hr hx)
  · simp [Function.mem_support, hx]

end TauCeti.Probability
