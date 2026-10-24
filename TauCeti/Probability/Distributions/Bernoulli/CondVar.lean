/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Distributions.TwoValued

/-!
# Conditional variance of a Bernoulli random variable

For a random variable with Bernoulli law on `0` and `1`, conditional variance is
the product of the two conditional expectations.
-/

public section

open MeasureTheory

open scoped ProbabilityTheory unitInterval

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} {X : Ω → ℝ}

/-- **Conditional variance of a Bernoulli random variable**.

The conditional variance of a random variable with law `Ber(1, 0, p)` is the product of the
conditional probabilities that it's equal to `1` and that it's equal to `0`. -/
lemma condVar_of_hasLaw_bernoulliMeasure {m₀ : MeasurableSpace Ω} (hm : m ≤ m₀)
    {P : Measure[m₀] Ω} {p : I} (hX : HasLaw X Ber(1, 0, p) P) :
    Var[X; P | m] =ᵐ[P] P[X | m] * P[1 - X | m] := by
  have := hX.isProbabilityMeasure
  have hp : Measurable fun x : ℝ ↦ x = 0 ∨ x = 1 := by fun_prop
  refine condVar_of_ae_eq_zero_or_one hm hX.aemeasurable ?_
  rw [hX.ae_iff hp, ae_iff]
  exact bernoulliMeasure_apply_of_notMem_of_notMem p hp.not.setOf (by simp) (by simp)

end ProbabilityTheory
