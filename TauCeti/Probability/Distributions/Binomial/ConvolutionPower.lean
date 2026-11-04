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

The convolution power of the natural-valued Bernoulli law is binomial. This connects the
independent-sum description of binomial laws to measure convolution and transport by additive
homomorphisms, including the scaled binomial laws of two-point renewal arrivals.
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

end TauCeti.Probability
