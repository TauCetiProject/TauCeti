/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.MeasureTheory.Measure.Measurability
public import Mathlib.Probability.Distributions.Geometric
/-!
# Parameter measurability for the geometric distribution

Measurability in the success probability lets measurable parameter maps produce measurable
measure-valued geometric families, in particular kernels, including the zero-parameter boundary.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
namespace TauCeti.Probability
/-- **The geometric family is measurable in its success probability.**

At `p = 0` the law is `Measure.dirac 0`; the result covers this boundary as well as nonzero success
probabilities. -/
@[fun_prop] theorem measurable_geometricMeasure :
    Measurable fun p : unitInterval => geometricMeasure p := by
  simp only [geometricMeasure]
  refine Measurable.ite ?_ (TauCeti.MeasureTheory.measurable_sum_smul_dirac fun n => by fun_prop)
    measurable_const
  exact (measurableSet_singleton (0 : unitInterval)).compl
end TauCeti.Probability
