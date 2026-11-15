/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Probability.Distributions.Bernoulli

/-!
# Parameter measurability for the Bernoulli distribution

The Bernoulli measure `Ber(x, y, p)` depends measurably on its two atoms and its success
probability jointly, so measurable parameter maps produce measurable measure-valued Bernoulli
families, in particular kernels.
-/

public section

open MeasureTheory ProbabilityTheory

/-- **The Bernoulli family is measurable in its parameters**: if the atoms `x`, `y` and the
success probability `p` depend measurably on `a`, then so does `Ber(x a, y a, p a)`. -/
@[fun_prop]
theorem Measurable.bernoulliMeasure {α X : Type*} [MeasurableSpace α] [MeasurableSpace X]
    {x y : α → X} {p : α → unitInterval} (hx : Measurable x) (hy : Measurable y)
    (hp : Measurable p) : Measurable fun a => Ber(x a, y a, p a) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [bernoulliMeasure_def, add_apply, smul_apply, Measure.dirac_apply' _ hs]
  fun_prop (disch := exact hs)
