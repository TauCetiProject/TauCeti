/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NegativeMultinomial.Basic
import TauCeti.Probability.Distributions.Poisson.FactorialMoments
import TauCeti.Analysis.SpecialFunctions.Gamma
import TauCeti.MeasureTheory.Integral.Bind
import Mathlib.Combinatorics.Enumerative.Stirling

/-!
# Mixed factorial moments of negative-multinomial counts

The mixed falling-factorial moment of orders `n i`, with total order `N`, is
`r (r + 1) ⋯ (r + N - 1) * ∏ i, (p i / p₀) ^ n i`.
The formula includes shape zero, zero category weights, empty category types, and order zero.
Every mixed factorial moment is integrable. Ordinary mixed natural moments are obtained
by the finite Stirling expansion, with integrability proved before evaluating the integral.

The calculation uses the defining Gamma mixture of independent Poisson counts. Conditional
factorial moments are powers of the rates, so finite-product integration reduces the mixed
moment to the existing natural Gamma moment formula. The nonnegative integrand lets the same
calculation establish integrability before using the real integral.

## References

* F. Ouimet, *Moments of the negative multinomial distribution*, 2022.
* The Poisson factorial-moment series and its mixture integration are provided by
  `hasSum_descFactorial_poissonMeasure` and `integral_descFactorial_mixedPoissonMeasure`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- Every mixed falling-factorial moment is finite, including the invalid zero-measure branches. -/
theorem integrable_prod_descFactorial_negativeMultinomialMeasure (r p₀ : ℝ)
    (p : ι → ℝ≥0) (n : ι → ℕ) :
    Integrable (fun k : ι → ℕ => ∏ i, ((k i).descFactorial (n i) : ℝ))
      (negativeMultinomialMeasure r p₀ p) := by
  by_cases h : 0 ≤ r ∧ 0 < p₀ ∧ p₀ + ∑ i, (p i : ℝ) = 1
  swap
  · rw [negativeMultinomialMeasure_eq_zero_of_invalid h]
    exact integrable_zero_measure
  obtain ⟨hr, hp₀, hp⟩ := h
  rcases hr.eq_or_lt with rfl | hr
  · rw [negativeMultinomialMeasure_zero hp₀ hp]
    exact integrable_dirac (by simp)
  rw [negativeMultinomialMeasure_of_pos hr hp₀ hp]
  refine (Measure.integrable_bind_iff (measurable_pi_poissonMeasure_mul_toNNReal p)
    (.of_discrete)).2 ⟨?_, ?_⟩
  · exact Filter.Eventually.of_forall fun x =>
      integrable_prod_descFactorial_pi_poissonMeasure (fun i => p i * x.toNNReal) n
  · simp_rw [Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _),
      integral_prod_descFactorial_pi_poissonMeasure]
    simp_rw [NNReal.coe_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    refine ((integrable_pow_gammaMeasure hr hp₀ (∑ i, n i)).const_mul
      (∏ i, (p i : ℝ) ^ n i)).congr ?_
    filter_upwards [ae_pos_gammaMeasure r p₀] with x hx
    simp only [Real.coe_toNNReal _ hx.le]

/-- The mixed factorial moment of total order `N` is the rising factorial of `r` of order `N`
times the product of the category-to-success weight ratios to their respective orders. -/
@[simp]
theorem integral_prod_descFactorial_negativeMultinomialMeasure {r p₀ : ℝ}
    (hr : 0 ≤ r) (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) (n : ι → ℕ) :
    ∫ k : ι → ℕ, ∏ i, ((k i).descFactorial (n i) : ℝ)
      ∂negativeMultinomialMeasure r p₀ p =
      (∏ j ∈ Finset.range (∑ i, n i), (r + j)) * ∏ i, ((p i : ℝ) / p₀) ^ n i := by
  classical
  rcases hr.eq_or_lt with rfl | hr
  · rw [negativeMultinomialMeasure_zero hp₀ hp, integral_dirac]
    by_cases hn : n = 0
    · simp [hn]
    · obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := Function.ne_iff.mp hn
      have hsum : 0 < ∑ j, n j :=
        lt_of_lt_of_le (Nat.pos_of_ne_zero hi) (Finset.single_le_sum (by simp) (by simp))
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Nat.pos_of_ne_zero hi]),
        Finset.prod_eq_zero (Finset.mem_range.mpr hsum) (by simp)]
      simp
  have hint := integrable_prod_descFactorial_negativeMultinomialMeasure r p₀ p n
  rw [negativeMultinomialMeasure_of_pos hr hp₀ hp] at hint ⊢
  rw [Measure.integral_bind (measurable_pi_poissonMeasure_mul_toNNReal p).aemeasurable hint]
  simp_rw [integral_prod_descFactorial_pi_poissonMeasure, NNReal.coe_mul, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hpow : (fun x : ℝ => (x.toNNReal : ℝ) ^ (∑ i, n i)) =ᵐ[gammaMeasure r p₀]
      fun x => x ^ (∑ i, n i) := by
    filter_upwards [ae_pos_gammaMeasure r p₀] with x hx
    simp only [Real.coe_toNNReal _ hx.le]
  rw [integral_const_mul, integral_congr_ae hpow, integral_pow_gammaMeasure hr hp₀]
  rw [← Real.prod_range_add_mul_Gamma hr (∑ i, n i)]
  simp_rw [div_pow]
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  field_simp [(Real.Gamma_pos_of_pos hr).ne', hp₀.ne']

open scoped Classical in
private theorem prod_pow_moments (r p₀ : ℝ)
    (p : ι → ℝ≥0) (n : ι → ℕ) :
    Integrable (fun k : ι → ℕ => ∏ i, (k i : ℝ) ^ n i)
      (negativeMultinomialMeasure r p₀ p) ∧
      ∫ k : ι → ℕ, ∏ i, (k i : ℝ) ^ n i ∂negativeMultinomialMeasure r p₀ p =
        ∑ j : (∀ i, Fin (n i + 1)), (∏ i, (Nat.stirlingSecond (n i) (j i) : ℝ)) *
          ∫ k : ι → ℕ, ∏ i, ((k i).descFactorial (j i) : ℝ)
            ∂negativeMultinomialMeasure r p₀ p := by
  classical
  have hexpand (k : ι → ℕ) :
      ∏ i, (k i : ℝ) ^ n i = ∑ j : (∀ i, Fin (n i + 1)),
        (∏ i, (Nat.stirlingSecond (n i) (j i) : ℝ)) *
          ∏ i, ((k i).descFactorial (j i) : ℝ) := by
    simp_rw [← Nat.cast_pow, Nat.pow_eq_sum_stirlingSecond_mul_descFactorial,
      Nat.cast_sum, Nat.cast_mul, ← Fin.sum_univ_eq_sum_range]
    rw [Fintype.prod_sum]
    simp only [Finset.prod_mul_distrib]
  simp_rw [hexpand]
  have hint (j : ∀ i, Fin (n i + 1)) :=
    (integrable_prod_descFactorial_negativeMultinomialMeasure r p₀ p
      (fun i => j i)).const_mul (∏ i, (Nat.stirlingSecond (n i) (j i) : ℝ))
  refine ⟨integrable_finsetSum _ (fun j _ => hint j), ?_⟩
  rw [integral_finsetSum _ (fun j _ => hint j)]
  simp_rw [integral_const_mul]

/-- Every ordinary mixed natural moment is finite, including the invalid zero-measure branches. -/
theorem integrable_prod_pow_negativeMultinomialMeasure (r p₀ : ℝ)
    (p : ι → ℝ≥0) (n : ι → ℕ) :
    Integrable (fun k : ι → ℕ => ∏ i, (k i : ℝ) ^ n i)
      (negativeMultinomialMeasure r p₀ p) :=
  (prod_pow_moments r p₀ p n).1

open scoped Classical in
/-- Ordinary mixed moments are finite Stirling sums of the explicit mixed factorial moments.
The sum ranges over coordinate orders bounded by the requested natural multi-index. -/
theorem integral_prod_pow_negativeMultinomialMeasure {r p₀ : ℝ}
    (hr : 0 ≤ r) (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) (n : ι → ℕ) :
    ∫ k : ι → ℕ, ∏ i, (k i : ℝ) ^ n i ∂negativeMultinomialMeasure r p₀ p =
      ∑ j : (∀ i, Fin (n i + 1)), (∏ i, (Nat.stirlingSecond (n i) (j i) : ℝ)) *
        ((∏ l ∈ Finset.range (∑ i, (j i : ℕ)), (r + l)) *
          ∏ i, ((p i : ℝ) / p₀) ^ (j i : ℕ)) := by
  rw [(prod_pow_moments r p₀ p n).2]
  simp_rw [integral_prod_descFactorial_negativeMultinomialMeasure hr hp₀ hp]

end TauCeti.Probability
