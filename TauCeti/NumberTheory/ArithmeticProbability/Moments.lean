/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticFunction.PrimeDivisibilitySum
public import TauCeti.NumberTheory.ArithmeticProbability.Divisibility

/-!
# First and second moments of weighted prime divisibility sums

Let `P` be a finite set of natural numbers, `a : ℕ → ℝ` a weight, and
`S = ArithmeticFunction.primeDivisibilitySum P a`, so that `S n = ∑ p ∈ P with p ∣ n, a p` for
`n > 0`. Under the uniform probability measure `μ_N = empiricalMeasure (· + 1) m` on
`{1, …, N}`, `N = m + 1`, this file computes the first two moments of `S` against the independent
model, in which the divisibility events `p ∣ n` for primes `p` become independent events of
probability `1 / p`.

Write `A = ∑ p ∈ P, a p / p` for the model mean, `L = ∑ p ∈ P, |a p|`, and, for `P` a set of
primes, `V = ∑ p ∈ P, a p ^ 2 (1 / p - 1 / p ^ 2)` for the model variance.

* The mean of `S` is exactly `∑ p ∈ P, a p ⌊N / p⌋ / N`, and it lies within `L / N` of `A`.
* For primes, the second moment of `S` about the model center `A` lies within `2 L ^ 2 / N` of
  `V`.
* Over a complete period, when every `p ∈ P` divides `N`, both comparisons are exact: the mean is
  `A` and the second moment about `A`, hence the variance, is `V`.

The center `A` is the model mean, not the empirical mean, and no independence is used: the
second moment is expanded over all ordered pairs of primes, including the diagonal, and each pair
is compared with the model through the counting of
`TauCeti.NumberTheory.ArithmeticProbability.Divisibility`. Only the moment comparisons need `P`
to consist of primes; the formulas for the mean hold for every finite `P`. These estimates are the
quadratic input of Turán–Kubilius type arguments for the normal order of additive functions such
as `ω`; they are useful only when `L ^ 2 / N` is small, so they do not by themselves control
the contribution of large primes.

## References

* T. Tao, *254A, Supplement 4: Probabilistic models and heuristics for the primes*, lecture
  notes (2015), Section 3.
-/

public section

noncomputable section

open MeasureTheory Finset TauCeti.Probability

namespace ArithmeticFunction

variable (P : Finset ℕ) (a : ℕ → ℝ) (m : ℕ)

/-- At a positive input the weighted divisibility sum is a weighted sum of divisibility
indicators. -/
private lemma primeDivisibilitySum_apply_eq_sum_ite {n : ℕ} (hn : n ≠ 0) :
    primeDivisibilitySum P a n = ∑ p ∈ P, a p * (if p ∣ n then 1 else 0) := by
  rw [primeDivisibilitySum_apply _ _ hn, sum_filter]
  simp

/-- The mean of the weighted divisibility sum `S = primeDivisibilitySum P a` under the uniform
probability measure on `{1, …, N}` is `∑ p ∈ P, a p ⌊N / p⌋ / N`. -/
theorem integral_primeDivisibilitySum_empiricalMeasure_add_one :
    ∫ n, primeDivisibilitySum P a n ∂(empiricalMeasure (· + 1) m : Measure ℕ) =
      ∑ p ∈ P, a p * (((m + 1) / p : ℕ) / (m + 1 : ℝ)) := by
  have h (p : ℕ) : ((m + 1) / p : ℕ) / (m + 1 : ℝ) =
      (m + 1 : ℝ)⁻¹ * ∑ k ∈ range (m + 1), (if p ∣ k + 1 then 1 else 0) := by
    rw [sum_boole, Nat.card_multiples, div_eq_inv_mul]
  rw [integral_empiricalMeasure_add_one, smul_eq_mul]
  simp_rw [h, primeDivisibilitySum_apply_eq_sum_ite _ _ (Nat.succ_ne_zero _), mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun p _ => sum_congr rfl fun k _ => by ring

/-- The mean of the weighted divisibility sum under the uniform probability measure on
`{1, …, N}` is within `L / N` of the model mean `A = ∑ p ∈ P, a p / p`, where
`L = ∑ p ∈ P, |a p|`. The weights may have either sign. -/
theorem abs_integral_primeDivisibilitySum_empiricalMeasure_add_one_sub_le :
    |∫ n, primeDivisibilitySum P a n ∂(empiricalMeasure (· + 1) m : Measure ℕ) -
        ∑ p ∈ P, a p / p| ≤ (∑ p ∈ P, |a p|) / (m + 1 : ℝ) := by
  rw [integral_primeDivisibilitySum_empiricalMeasure_add_one, ← sum_sub_distrib, div_eq_mul_inv,
    sum_mul]
  have h (p : ℕ) : a p * (((m + 1) / p : ℕ) / (m + 1 : ℝ)) - a p / p =
      a p * ((empiricalMeasure (· + 1) m : Measure ℕ).real {n | p ∣ n} - (p : ℝ)⁻¹) := by
    rw [empiricalMeasure_add_one_real_dvd]
    ring
  simp_rw [h]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p _ => ?_)
  rw [abs_mul]
  gcongr
  exact abs_empiricalMeasure_add_one_real_dvd_sub_inv_le m p

/-- Over a complete period, when every member of `P` divides `N`, the mean of the weighted
divisibility sum under the uniform probability measure on `{1, …, N}` is exactly the model mean
`∑ p ∈ P, a p / p`. -/
theorem integral_primeDivisibilitySum_empiricalMeasure_add_one_of_dvd {P : Finset ℕ} {m : ℕ}
    (h : ∀ p ∈ P, p ∣ m + 1) (a : ℕ → ℝ) :
    ∫ n, primeDivisibilitySum P a n ∂(empiricalMeasure (· + 1) m : Measure ℕ) =
      ∑ p ∈ P, a p / p := by
  rw [integral_primeDivisibilitySum_empiricalMeasure_add_one]
  refine sum_congr rfl fun p hp => ?_
  rw [← empiricalMeasure_add_one_real_dvd,
    empiricalMeasure_add_one_real_dvd_of_dvd (h p hp), div_eq_mul_inv]

/-- The second moment of the weighted divisibility sum about the model mean, expanded over all
ordered pairs of members of `P` into averages of products of centered divisibility indicators. -/
private lemma integral_primeDivisibilitySum_sub_sq_empiricalMeasure_add_one_eq_sum_sum :
    ∫ n, (primeDivisibilitySum P a n - ∑ p ∈ P, a p / p) ^ 2
        ∂(empiricalMeasure (· + 1) m : Measure ℕ) =
      ∑ p ∈ P, ∑ q ∈ P, a p * a q *
        ∫ n, ((if p ∣ n then 1 else 0) - (p : ℝ)⁻¹) * ((if q ∣ n then 1 else 0) - (q : ℝ)⁻¹)
          ∂(empiricalMeasure (· + 1) m : Measure ℕ) := by
  have h (n : ℕ) (hn : n ≠ 0) : primeDivisibilitySum P a n - ∑ p ∈ P, a p / p =
      ∑ p ∈ P, a p * ((if p ∣ n then 1 else 0) - (p : ℝ)⁻¹) := by
    rw [primeDivisibilitySum_apply_eq_sum_ite _ _ hn, ← sum_sub_distrib]
    exact sum_congr rfl fun p _ => by ring
  simp_rw [integral_empiricalMeasure_add_one, smul_eq_mul, h _ (Nat.succ_ne_zero _), sq,
    sum_mul_sum, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun p _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun q _ => sum_congr rfl fun k _ => by ring

/-- The model variance written as a double sum over ordered pairs, with only the diagonal
contributing. -/
private lemma sum_sq_mul_eq_sum_sum :
    ∑ p ∈ P, a p ^ 2 * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹) =
      ∑ p ∈ P, ∑ q ∈ P, a p * a q * (if p = q then (p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹ else 0) := by
  refine sum_congr rfl fun p hp => ?_
  simp [mul_ite, sum_ite_eq, hp, sq]

/-- For a finite set `P` of primes, the second moment of the weighted divisibility sum
`S = primeDivisibilitySum P a` about the model mean `A = ∑ p ∈ P, a p / p`, under the uniform
probability measure on `{1, …, N}`, is within `2 L ^ 2 / N` of the model variance
`V = ∑ p ∈ P, a p ^ 2 (1 / p - 1 / p ^ 2)`, where `L = ∑ p ∈ P, |a p|`. -/
theorem abs_integral_primeDivisibilitySum_sub_sq_empiricalMeasure_add_one_sub_le
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℝ) (m : ℕ) :
    |∫ n, (primeDivisibilitySum P a n - ∑ p ∈ P, a p / p) ^ 2
        ∂(empiricalMeasure (· + 1) m : Measure ℕ) -
      ∑ p ∈ P, a p ^ 2 * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹)| ≤
        2 * (∑ p ∈ P, |a p|) ^ 2 / (m + 1 : ℝ) := by
  rw [integral_primeDivisibilitySum_sub_sq_empiricalMeasure_add_one_eq_sum_sum,
    sum_sq_mul_eq_sum_sum, ← sum_sub_distrib]
  simp_rw [← sum_sub_distrib, ← mul_sub]
  calc _ ≤ ∑ p ∈ P, ∑ q ∈ P, |a p| * |a q| * (2 / (m + 1 : ℝ)) := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p hp => ?_)
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun q hq => ?_)
        rw [abs_mul, abs_mul]
        gcongr
        exact abs_integral_empiricalMeasure_add_one_centered_dvd_mul_sub_ite_le (hP p hp)
          (hP q hq) m
    _ = 2 * (∑ p ∈ P, |a p|) ^ 2 / (m + 1 : ℝ) := by
      rw [sq, sum_mul_sum, mul_sum, sum_div]
      refine sum_congr rfl fun p _ => ?_
      rw [mul_sum, sum_div]
      exact sum_congr rfl fun q _ => by ring

/-- For a finite set `P` of primes all dividing `N`, the second moment of the weighted divisibility
sum about the model mean `A = ∑ p ∈ P, a p / p`, under the uniform probability measure on
`{1, …, N}`, is exactly the model variance `V = ∑ p ∈ P, a p ^ 2 (1 / p - 1 / p ^ 2)`. Since the
mean is then `A` (`integral_primeDivisibilitySum_empiricalMeasure_add_one_of_dvd`), `V` is the
variance. -/
theorem integral_primeDivisibilitySum_sub_sq_empiricalMeasure_add_one_of_dvd
    {P : Finset ℕ} {m : ℕ} (hP : ∀ p ∈ P, p.Prime) (h : ∀ p ∈ P, p ∣ m + 1) (a : ℕ → ℝ) :
    ∫ n, (primeDivisibilitySum P a n - ∑ p ∈ P, a p / p) ^ 2
        ∂(empiricalMeasure (· + 1) m : Measure ℕ) =
      ∑ p ∈ P, a p ^ 2 * ((p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹) := by
  rw [integral_primeDivisibilitySum_sub_sq_empiricalMeasure_add_one_eq_sum_sum,
    sum_sq_mul_eq_sum_sum]
  refine sum_congr rfl fun p hp => sum_congr rfl fun q hq => ?_
  rw [integral_empiricalMeasure_add_one_centered_dvd_mul_of_prime_of_dvd (hP p hp) (hP q hq)
    (h p hp) (h q hq)]

end ArithmeticFunction
