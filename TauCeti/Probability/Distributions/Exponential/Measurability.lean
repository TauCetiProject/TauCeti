/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.Gamma.Measurability
public import Mathlib.Probability.Distributions.Exponential
/-! # Parameter measurability for the exponential distribution -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
namespace TauCeti.Probability
/-- **The exponential family is measurable in its rate.**

`expMeasure r` is `gammaMeasure 1 r`, so this is `measurable_gammaMeasure` along the line `a = 1`.
-/
@[fun_prop] theorem measurable_expMeasure : Measurable fun r : ℝ => expMeasure r := by
  have h : (fun r : ℝ => expMeasure r) =
      (fun p : ℝ × ℝ => gammaMeasure p.1 p.2) ∘ fun r : ℝ => ((1 : ℝ), r) := rfl
  rw [h]
  exact measurable_gammaMeasure.comp (by fun_prop)
end TauCeti.Probability
