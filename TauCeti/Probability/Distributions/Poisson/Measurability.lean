/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Distributions.Poisson.Basic

import TauCeti.MeasureTheory.Measure.Measurability
/-!
# Parameter measurability for the Poisson distribution

Measurability in the rate lets measurable rate maps produce measurable measure-valued Poisson
families and permits packaging such families as kernels.
-/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace TauCeti.Probability
/-- **The Poisson family is measurable in its rate.**

This permits composition with measurable rate maps and packages the resulting measure-valued
family as a kernel. -/
@[fun_prop] theorem measurable_poissonMeasure : Measurable fun r : ℝ≥0 => poissonMeasure r := by
  simp only [poissonMeasure]
  exact TauCeti.MeasureTheory.measurable_sum_smul_dirac fun n => by fun_prop
end TauCeti.Probability
