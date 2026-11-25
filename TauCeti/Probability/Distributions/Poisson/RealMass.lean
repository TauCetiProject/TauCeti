/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan Braams, Claude
-/
module

public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# The Poisson mass at a real parameter

The Poisson mass `e^{-θ} θˣ / x!` is defined here for every real `θ`, so that it can be
integrated against a prior on all of `ℝ`, as in empirical Bayes. For `θ ≥ 0` it is the mass of
Mathlib's `poissonMeasure` at `x`. For every real `θ` the masses sum to `1`, being the
exponential series of `θ` times `e^{-θ}`; for `θ < 0` some masses are negative.

## Main definitions

* `Real.poissonMass θ x`: the Poisson mass `e^{-θ} θˣ / x!`.

## Main results

* `Real.poissonMass_eq_poissonMeasure_real_singleton`: for `θ ≥ 0` it is the mass of
  `poissonMeasure θ` at `x`.
* `Real.hasSum_poissonMass`: the masses sum to `1` for every real `θ`.

The definition is adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>),
file `CKSD/Bayes/Basic.lean`.

## References

* G. Casella and R. L. Berger, *Statistical Inference*, 2nd ed., Duxbury (2002), §3.2.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal Nat

namespace Real

/-- The **Poisson mass** `e^{-θ} θˣ / x!`, for an arbitrary real parameter `θ`. For `θ ≥ 0` it
is the mass of `poissonMeasure θ` at `x`. -/
noncomputable def poissonMass (θ : ℝ) (x : ℕ) : ℝ :=
  exp (-θ) * θ ^ x / x !

theorem poissonMass_def (θ : ℝ) (x : ℕ) : poissonMass θ x = exp (-θ) * θ ^ x / x ! := (rfl)

/-- For `θ ≥ 0`, the Poisson mass is the mass of Mathlib's Poisson law at a point. -/
theorem poissonMass_eq_poissonMeasure_real_singleton {θ : ℝ} (hθ : 0 ≤ θ) (x : ℕ) :
    poissonMass θ x = (poissonMeasure θ.toNNReal).real {x} := by
  rw [poissonMeasure_real_singleton, Real.coe_toNNReal θ hθ, poissonMass_def]

/-- The Poisson masses sum to `1` for every real `θ`, including negative `θ`. -/
theorem hasSum_poissonMass (θ : ℝ) : HasSum (poissonMass θ) 1 := by
  convert (NormedSpace.expSeries_div_hasSum_exp θ).mul_left (exp (-θ)) using 1
  · ext x
    simp_rw [poissonMass_def, mul_div_assoc]
  · simp [← exp_eq_exp_ℝ, ← exp_add]

/-- The Poisson masses sum to `1` for every real `θ`. -/
theorem tsum_poissonMass (θ : ℝ) : ∑' x, poissonMass θ x = 1 :=
  (hasSum_poissonMass θ).tsum_eq

end Real
