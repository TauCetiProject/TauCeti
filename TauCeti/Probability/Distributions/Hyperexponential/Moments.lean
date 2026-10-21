/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Hyperexponential.Basic

/-!
# Moments of hyperexponential distributions

All natural moments of a hyperexponential law are finite. Its moment of order `n` is
`n! * ∑ i, pᵢ / rᵢⁿ`, its mean is `∑ i, pᵢ / rᵢ`, and its variance is
`2 * ∑ i, pᵢ / rᵢ² - (∑ i, pᵢ / rᵢ)²`.
Only positive-weight components require positive rates; the formulas allow arbitrary
inactive rates and coincident active rates. The zeroth-moment formula is included.

The calculations use the exponential moment formulas and finite-mixture integration from
`Hyperexponential.Basic`.

## References

* S. Asmussen, *Applied Probability and Queues*, 2nd ed., Springer (2003), Chapter III, §4.
-/

public section

noncomputable section

open Convexity MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] {p : StdSimplex ℝ≥0 ι} {r : ι → ℝ}

/-- Every natural power is integrable, including for invalid parameters whose law is zero. -/
@[simp]
theorem integrable_pow_hyperexponentialMeasure (p : StdSimplex ℝ≥0 ι) (r : ι → ℝ) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (hyperexponentialMeasure p r) := by
  by_cases hr : ∀ i, 0 < p.weights i → 0 < r i
  · exact (integrable_hyperexponentialMeasure_iff hr).mpr fun i hi ↦
      integrable_pow_expMeasure (hr i hi) n
  · simp [hyperexponentialMeasure_of_not_pos hr]

/-- The natural moments of a valid hyperexponential law, including order zero. -/
@[simp]
theorem integral_pow_hyperexponentialMeasure
    (hr : ∀ i, 0 < p.weights i → 0 < r i) (n : ℕ) :
    ∫ x, x ^ n ∂hyperexponentialMeasure p r =
      (Nat.factorial n : ℝ) * ∑ i, (p.weights i : ℝ) / r i ^ n := by
  rw [integral_hyperexponentialMeasure hr (integrable_pow_hyperexponentialMeasure p r n),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hwi : p.weights i = 0
  · simp [hwi]
  · rw [integral_pow_expMeasure (hr i (pos_iff_ne_zero.mpr hwi))]
    simp only [smul_eq_mul]
    ring

/-- The mean of a valid hyperexponential law. -/
@[simp]
theorem integral_id_hyperexponentialMeasure
    (hr : ∀ i, 0 < p.weights i → 0 < r i) :
    ∫ x, x ∂hyperexponentialMeasure p r = ∑ i, (p.weights i : ℝ) / r i := by
  simpa using integral_pow_hyperexponentialMeasure hr 1

/-- The variance of a valid hyperexponential law. -/
@[simp]
theorem variance_id_hyperexponentialMeasure
    (hr : ∀ i, 0 < p.weights i → 0 < r i) :
    Var[id; hyperexponentialMeasure p r] =
      2 * ∑ i, (p.weights i : ℝ) / r i ^ 2 - (∑ i, (p.weights i : ℝ) / r i) ^ 2 := by
  let _ := isProbabilityMeasure_hyperexponentialMeasure hr
  have hmem : MemLp id 2 (hyperexponentialMeasure p r) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).mpr
      (integrable_pow_hyperexponentialMeasure p r 2)
  rw [variance_eq_sub hmem]
  simp [integral_pow_hyperexponentialMeasure hr, integral_id_hyperexponentialMeasure hr]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- The mean of a random variable with a valid hyperexponential law. -/
theorem integral_of_hasLaw_hyperexponentialMeasure
    (hr : ∀ i, 0 < p.weights i → 0 < r i)
    (hX : HasLaw X (hyperexponentialMeasure p r) P) :
    ∫ ω, X ω ∂P = ∑ i, (p.weights i : ℝ) / r i := by
  rw [hX.integral_eq, integral_id_hyperexponentialMeasure hr]

/-- The variance of a random variable with a valid hyperexponential law. -/
theorem variance_of_hasLaw_hyperexponentialMeasure
    (hr : ∀ i, 0 < p.weights i → 0 < r i)
    (hX : HasLaw X (hyperexponentialMeasure p r) P) :
    Var[X; P] =
      2 * ∑ i, (p.weights i : ℝ) / r i ^ 2 - (∑ i, (p.weights i : ℝ) / r i) ^ 2 := by
  rw [hX.variance_eq, variance_id_hyperexponentialMeasure hr]

end TauCeti.Probability
