/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.Basic

/-!
# Basic facts about moment-generating functions

This file supplements Mathlib's basic moment-generating-function API.

## Main results

* `TauCeti.isProbabilityMeasure_of_mgf_zero_eq_one`: a measure is a probability measure if the
  moment-generating function of any real-valued statistic equals `1` at zero.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ}

/-- A measure is a probability measure if the moment-generating function of any real-valued
statistic equals `1` at zero. -/
theorem isProbabilityMeasure_of_mgf_zero_eq_one (hmgf : mgf X μ 0 = 1) :
    IsProbabilityMeasure μ := by
  rw [mgf_zero'] at hmgf
  exact ⟨(ENNReal.toReal_eq_one_iff _).1 hmgf⟩

end TauCeti
