/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
/-! # Parameter measurability for the Bernoulli distribution -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
namespace TauCeti.Probability
/-- **The Bernoulli family is measurable in its success probability.** -/
@[fun_prop] theorem measurable_bernoulliMeasure {X : Type*} [MeasurableSpace X] (x y : X) :
    Measurable fun p : unitInterval => bernoulliMeasure x y p := by
  simp only [bernoulliMeasure]
  fun_prop
end TauCeti.Probability
