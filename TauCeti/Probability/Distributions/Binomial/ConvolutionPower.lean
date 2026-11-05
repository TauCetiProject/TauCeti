/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Binomial.Basic
public import TauCeti.MeasureTheory.Group.Convolution.Power

/-!
# Convolution powers of Bernoulli laws

The convolution power of the natural-valued Bernoulli law is binomial. Transport along
`multiplesHom` gives the convolution powers of a law supported on zero and a fixed element
of a measurable additive monoid, as needed for scaled binomial renewal arrival laws.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- The convolution powers of the Bernoulli law are the binomial laws, including the empty
sum at exponent zero. -/
@[simp]
theorem bernoulliMeasure_convolutionPower (p : unitInterval) (n : ℕ) :
    (bernoulliMeasure (1 : ℕ) 0 p).convolutionPower n = binomial n p := by
  induction n with
  | zero => simp [binomial_zero]
  | succ n ih =>
    rw [Measure.convolutionPower_succ, ih, ← binomial_one_eq_bernoulliMeasure,
      binomial_conv_binomial]

/-- Convolution powers of the law supported on `a` and zero are binomial laws transported
along the map `j ↦ j • a`, including the empty sum at exponent zero. -/
theorem bernoulliMeasure_convolutionPower_multiples {β : Type*} [MeasurableSpace β]
    [AddMonoid β] [MeasurableAdd₂ β]
    (a : β) (p : unitInterval) (n : ℕ) :
    (bernoulliMeasure a 0 p).convolutionPower n = (binomial n p).map (multiplesHom β a) := by
  have hmap : (bernoulliMeasure (1 : ℕ) 0 p).map (multiplesHom β a) =
      bernoulliMeasure a 0 p := by
    simpa using map_bernoulliMeasure' 1 0 (f := multiplesHom β a) Measurable.of_discrete p
  simpa only [bernoulliMeasure_convolutionPower, hmap] using
    (Measure.map_convolutionPower (bernoulliMeasure (1 : ℕ) 0 p)
      (multiplesHom β a) Measurable.of_discrete n).symm

end TauCeti.Probability
