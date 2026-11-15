/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gamma.Support
public import TauCeti.Probability.Distributions.Exponential.Basic

/-!
# Topological support of the exponential distribution

This file records that a positive-rate exponential law reaches arbitrarily close to zero and has
positive density at every positive point.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

/-- An exponential law with positive rate has topological support `[0, ∞)`. -/
@[simp]
theorem support_expMeasure {r : ℝ} (hr : 0 < r) : (expMeasure r).support = Ici 0 := by
  simpa only [expMeasure] using support_gammaMeasure zero_lt_one hr

end TauCeti.Probability
