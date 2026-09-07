/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# The multinomial distribution

For a natural number `n` and a probability vector `p`, the multinomial distribution assigns to
a count vector `k` of total size `n` the mass

```text
  multinomial(univ, k) * ∏ i, p.weights i ^ k i.
```

This file defines the distribution as a finite weighted sum of Dirac measures and establishes its
normalization, exact singleton masses and support, and finite-sum integration formula.  The
parameter space is Mathlib's `Convexity.StdSimplex ℝ≥0 ι`; its weights are nonnegative real
numbers summing to one.

## Main definitions and results

* `TauCeti.Probability.multinomialWeightReal`: the real-valued multinomial weight.
* `TauCeti.Probability.multinomialWeight`: the extended nonnegative multinomial weight.
* `TauCeti.Probability.multinomialMeasure`: the multinomial measure on count vectors.
* `TauCeti.Probability.isProbabilityMeasure_multinomialMeasure`: normalization.
* `TauCeti.Probability.multinomialMeasure_singleton`: the exact singleton mass.
* `TauCeti.Probability.multinomialMeasure_singleton_ne_zero_iff`: the exact support.
* `TauCeti.Probability.integral_multinomialMeasure`: integration as a finite weighted sum.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 35.
-/

public section

noncomputable section

open Convexity MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {ι : Type*} [Fintype ι]

/-- The real-valued mass function of the multinomial distribution.

It is indexed by a probability vector `p` and a count vector `k`.  The sample size does not occur
in the definition: it selects the level set `∑ i, k i = n` when the measure is formed. -/
def multinomialWeightReal (p : StdSimplex NNReal ι) (k : ι → ℕ) : ℝ :=
  (Nat.multinomial Finset.univ k : ℝ) * ∏ i, (p.weights i : ℝ) ^ k i

/-- Every multinomial mass is nonnegative. -/
theorem multinomialWeightReal_nonneg (p : StdSimplex NNReal ι) (k : ι → ℕ) :
    0 ≤ multinomialWeightReal p k := by
  exact mul_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg fun i _ ↦ pow_nonneg (p.weights i).coe_nonneg _)

/-- The `ℝ≥0∞`-valued multinomial weight used to scale Dirac measures. -/
def multinomialWeight (p : StdSimplex NNReal ι) (k : ι → ℕ) : ℝ≥0∞ :=
  (Nat.multinomial Finset.univ k : ℝ≥0∞) * ∏ i, (p.weights i : ℝ≥0∞) ^ k i

/-- The extended nonnegative multinomial weight has the expected real value. -/
@[simp]
theorem multinomialWeight_toReal (p : StdSimplex NNReal ι) (k : ι → ℕ) :
    (multinomialWeight p k).toReal = multinomialWeightReal p k := by
  simp [multinomialWeight, multinomialWeightReal, ENNReal.toReal_mul]

open Classical in
/-- The multinomial distribution with sample size `n` and cell probabilities `p`.

The finite antidiagonal consists precisely of the count vectors whose coordinates sum to `n`. -/
def multinomialMeasure (n : ℕ) (p : StdSimplex NNReal ι) : Measure (ι → ℕ) :=
  ∑ k ∈ Finset.piAntidiag Finset.univ n, multinomialWeight p k • Measure.dirac k

open Classical in
/-- The real multinomial masses on a fixed antidiagonal sum to one. -/
theorem sum_multinomialWeightReal (n : ℕ) (p : StdSimplex NNReal ι) :
    ∑ k ∈ Finset.piAntidiag Finset.univ n, multinomialWeightReal p k = 1 := by
  calc
    _ = (∑ i ∈ Finset.univ, (p.weights i : ℝ)) ^ n := by
      symm
      simpa [multinomialWeightReal] using
        (Finset.sum_pow_eq_sum_piAntidiag Finset.univ (fun i ↦ (p.weights i : ℝ)) n)
    _ = 1 := by norm_cast; simp

open Classical in
/-- The `ℝ≥0∞`-valued multinomial weights on a fixed antidiagonal sum to one. -/
theorem sum_multinomialWeight (n : ℕ) (p : StdSimplex NNReal ι) :
    ∑ k ∈ Finset.piAntidiag Finset.univ n, multinomialWeight p k = 1 := by
  calc
    _ = (∑ i ∈ Finset.univ, (p.weights i : ℝ≥0∞)) ^ n := by
      symm
      simpa [multinomialWeight] using
        (Finset.sum_pow_eq_sum_piAntidiag Finset.univ
          (fun i ↦ (p.weights i : ℝ≥0∞)) n)
    _ = 1 := by norm_cast; simp

/-- The multinomial law is a probability measure. -/
theorem isProbabilityMeasure_multinomialMeasure (n : ℕ) (p : StdSimplex NNReal ι) :
    IsProbabilityMeasure (multinomialMeasure n p) := by
  classical
  rw [isProbabilityMeasure_iff, multinomialMeasure, Measure.finsetSum_apply]
  simpa using sum_multinomialWeight n p

/-- With no trials, the multinomial law is concentrated at the zero count vector. -/
@[simp]
theorem multinomialMeasure_zero (p : StdSimplex NNReal ι) :
    multinomialMeasure 0 p = Measure.dirac 0 := by
  classical
  simp [multinomialMeasure, multinomialWeight, Nat.multinomial]

/-- The singleton mass of a multinomial law is its defining weight on the count antidiagonal and
zero elsewhere. -/
@[simp]
theorem multinomialMeasure_singleton (n : ℕ) (p : StdSimplex NNReal ι) (k : ι → ℕ) :
    multinomialMeasure n p {k} =
      if ∑ i, k i = n then multinomialWeight p k else 0 := by
  classical
  rw [multinomialMeasure, Measure.finsetSum_apply]
  split_ifs with hk
  · rw [Finset.sum_eq_single k]
    · simp
    · intro b hb hbk
      simp [hbk]
    · intro hmem
      exact (hmem (by simp [Finset.mem_piAntidiag, hk])).elim
  · rw [Finset.sum_eq_zero]
    intro b hb
    have hbk : b ≠ k := by
      intro h
      subst b
      exact hk (Finset.mem_piAntidiag.mp hb).1
    simp [hbk]

/-- The real singleton mass of a multinomial law, in the usual factorial form. -/
theorem multinomialMeasure_real_singleton (n : ℕ) (p : StdSimplex NNReal ι) (k : ι → ℕ) :
    (multinomialMeasure n p).real {k} =
      if ∑ i, k i = n then
        ((n.factorial : ℝ) / (∏ i, ((k i).factorial : ℝ))) *
          (∏ i, (p.weights i : ℝ) ^ k i)
      else 0 := by
  rw [measureReal_def, multinomialMeasure_singleton]
  split_ifs with hk
  · simp only [multinomialWeight_toReal, multinomialWeightReal]
    have hprod : (∏ i, ((k i).factorial : ℝ)) ≠ 0 := by positivity
    have hcoeff : (Nat.multinomial Finset.univ k : ℝ) =
        ((∑ i, k i).factorial : ℝ) / ∏ i, ((k i).factorial : ℝ) := by
      apply (eq_div_iff hprod).2
      rw [mul_comm]
      exact_mod_cast Nat.multinomial_spec Finset.univ k
    rw [hcoeff, hk]
  · simp

/-- A multinomial weight is nonzero exactly when every cell receiving a positive count has
positive parameter weight. -/
@[simp]
theorem multinomialWeight_ne_zero_iff (p : StdSimplex NNReal ι) (k : ι → ℕ) :
    multinomialWeight p k ≠ 0 ↔ ∀ i, k i ≠ 0 → p.weights i ≠ 0 := by
  rw [multinomialWeight, mul_ne_zero_iff,
    and_iff_right (by exact_mod_cast Nat.ne_of_gt (Nat.multinomial_pos Finset.univ k)),
    Finset.prod_ne_zero_iff]
  simp only [Finset.mem_univ, forall_const]
  constructor
  · intro h i hki hpi
    simpa [hpi, hki] using h i
  · intro h i
    by_cases hki : k i = 0
    · simp [hki]
    · apply pow_ne_zero
      exact_mod_cast h i hki

/-- The singleton mass is nonzero precisely for count vectors of total size `n` which do not use
a zero-weight cell. -/
theorem multinomialMeasure_singleton_ne_zero_iff (n : ℕ) (p : StdSimplex NNReal ι)
    (k : ι → ℕ) :
    multinomialMeasure n p {k} ≠ 0 ↔
      (∑ i, k i = n) ∧ ∀ i, k i ≠ 0 → p.weights i ≠ 0 := by
  rw [multinomialMeasure_singleton]
  split_ifs with hk
  · simp [hk]
  · simp [hk]

/-- Every multinomial weight is finite. -/
@[simp]
theorem multinomialWeight_ne_top (p : StdSimplex NNReal ι) (k : ι → ℕ) :
    multinomialWeight p k ≠ ∞ := by
  rw [multinomialWeight]
  apply ENNReal.mul_ne_top
  · exact ne_of_lt (ENNReal.natCast_lt_top _)
  · exact ENNReal.prod_ne_top fun _ _ ↦ by simp

/-- A multinomial law is concentrated on count vectors whose coordinates sum to the sample
size. -/
@[simp]
theorem multinomialMeasure_sum_eq (n : ℕ) (p : StdSimplex NNReal ι) :
    multinomialMeasure n p {k | ∑ i, k i = n} = 1 := by
  classical
  rw [multinomialMeasure, Measure.finsetSum_apply]
  calc
    _ = ∑ k ∈ Finset.piAntidiag Finset.univ n, multinomialWeight p k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hsum : ∑ i, k i = n := (Finset.mem_piAntidiag.mp hk).1
      simp [hsum]
    _ = 1 := sum_multinomialWeight n p

/-- Every function is integrable against a multinomial law because the law has finite support. -/
theorem integrable_multinomialMeasure {E : Type*} [NormedAddCommGroup E]
    (f : (ι → ℕ) → E) (n : ℕ) (p : StdSimplex NNReal ι) :
    Integrable f (multinomialMeasure n p) := by
  classical
  rw [multinomialMeasure]
  exact integrable_finsetSum_measure.mpr fun k _ ↦
    (integrable_dirac (by simp)).smul_measure (multinomialWeight_ne_top p k)

open Classical in
/-- Integration against a multinomial law is the corresponding finite weighted sum. -/
theorem integral_multinomialMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : (ι → ℕ) → E) (n : ℕ) (p : StdSimplex NNReal ι) :
    ∫ k, f k ∂multinomialMeasure n p =
      ∑ k ∈ Finset.piAntidiag Finset.univ n, multinomialWeightReal p k • f k := by
  rw [multinomialMeasure, integral_finsetSum_measure]
  · simp
  · exact fun k _ ↦
      (integrable_dirac (by simp)).smul_measure (multinomialWeight_ne_top p k)

end Probability

end TauCeti
