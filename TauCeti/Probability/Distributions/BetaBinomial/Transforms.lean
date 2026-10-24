/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.BetaBinomial.Basic
public import TauCeti.Probability.GeneratingFunction
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Transforms of beta-binomial laws

The beta-binomial law has finite support, so its probability-generating function is a polynomial
on all of `ℝ`, and its real cast has every exponential moment. Its moment-generating and
characteristic functions are finite sums of the Beta-function masses. These formulas include
zero trials; exponential integrability also includes invalid shapes, whose law is zero.

The finite sums use `integral_betaBinomialMeasure`, while the passage from the generating
function to the real-cast moment-generating function uses `mgf_id_map_natCast`.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- The beta-binomial probability-generating function is a finite polynomial for every real
argument, without a unit-interval restriction. -/
theorem pgf_betaBinomialMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (n : ℕ) (z : ℝ) :
    pgf id (betaBinomialMeasure n a b) z =
      ∑ k ∈ Finset.Iic n,
        (n.choose k * beta (a + k) (b + (n - k)) / beta a b) * z ^ k := by
  rw [pgf_def, integral_betaBinomialMeasure _ ha hb]
  simp only [id_eq, smul_eq_mul]

/-- The real cast of a beta-binomial law has exponential-integrability domain all of `ℝ`.
This also holds for invalid shapes, where the law is zero. -/
@[simp]
theorem integrableExpSet_id_map_cast_betaBinomialMeasure (n : ℕ) (a b : ℝ) :
    integrableExpSet id ((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ)) = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_univ, iff_true]
  exact integrable_map_cast_betaBinomialMeasure _ n a b

/-- The beta-binomial moment-generating function is the finite exponential sum of its masses. -/
theorem mgf_id_map_cast_betaBinomialMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (n : ℕ) (t : ℝ) :
    mgf id ((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ)) t =
      ∑ k ∈ Finset.Iic n,
        (n.choose k * beta (a + k) (b + (n - k)) / beta a b) * Real.exp (t * k) := by
  rw [mgf_id_map_natCast, pgf_betaBinomialMeasure ha hb]
  simp only [← Real.exp_nat_mul, mul_comm t]

/-- The beta-binomial cumulant-generating function is the logarithm of its finite exponential
sum, on its full domain `ℝ`. -/
theorem cgf_id_map_cast_betaBinomialMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (n : ℕ) (t : ℝ) :
    cgf id ((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ)) t =
      Real.log (∑ k ∈ Finset.Iic n,
        (n.choose k * beta (a + k) (b + (n - k)) / beta a b) * Real.exp (t * k)) := by
  rw [cgf, mgf_id_map_cast_betaBinomialMeasure ha hb]

/-- The characteristic function of the real cast beta-binomial law is its finite Fourier sum. -/
theorem charFun_map_cast_betaBinomialMeasure {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (n : ℕ) (t : ℝ) :
    charFun ((betaBinomialMeasure n a b).map (Nat.cast : ℕ → ℝ)) t =
      ∑ k ∈ Finset.Iic n,
        (n.choose k * beta (a + k) (b + (n - k)) / beta a b : ℝ) •
          Complex.exp ((t : ℂ) * k * Complex.I) := by
  rw [charFun_apply_real, (MeasurableEmbedding.natCast (α := ℝ)).integral_map,
    integral_betaBinomialMeasure _ ha hb]
  simp

end TauCeti.Probability
