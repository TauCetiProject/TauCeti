/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.CDF

/-!
# The Bernoulli cumulative distribution function

A real Bernoulli law `Ber(a, b, p)` assigns mass `p` to `a` and mass `1 - p` to `b`, so its cdf
at `x` is the total mass of the atoms lying at or below `x`. The formula assumes no order between
the atoms and includes `a = b` and the Dirac laws at success probabilities zero and one. For the
standard law `Ber(1, 0, p)` it is zero below zero, `1 - p` between zero and one, and one from one
onwards: the cumulative crossing used to compute Bernoulli quantiles.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

namespace TauCeti.Probability

/-- The cdf of a real Bernoulli law with atoms `a` (mass `p`) and `b` (mass `1 - p`): each atom
contributes its mass from its own position onwards. No order between `a` and `b` is assumed, and
the formula includes `a = b` and success probabilities zero and one. -/
@[simp]
theorem cdf_bernoulliMeasure (a b : ℝ) (p : unitInterval) (x : ℝ) :
    cdf Ber(a, b, p) x =
      (if a ≤ x then (p : ℝ) else 0) + if b ≤ x then 1 - (p : ℝ) else 0 := by
  rw [cdf_eq_real, bernoulliMeasure_real_apply p measurableSet_Iic]
  simp only [mem_Iic, unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
  split_ifs <;> ring

end TauCeti.Probability
