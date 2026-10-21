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

The real Bernoulli law assigns mass `1 - p` to zero and mass `p` to one. Its cdf is therefore
zero below zero, `1 - p` between zero and one, and one from one onwards. The formula includes
the Dirac laws at success probabilities zero and one, and supplies the cumulative crossing
used to compute Bernoulli quantiles.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

namespace TauCeti.Probability

/-- The cdf of a real Bernoulli law, including success probabilities zero and one. -/
@[simp]
theorem cdf_bernoulliMeasure (p : unitInterval) (x : ℝ) :
    cdf Ber((1 : ℝ), 0, p) x =
      if x < 0 then 0 else if x < 1 then 1 - (p : ℝ) else 1 := by
  rw [cdf_eq_real, bernoulliMeasure_real_apply p measurableSet_Iic]
  simp only [mem_Iic, unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
  split_ifs <;> grind

end TauCeti.Probability
