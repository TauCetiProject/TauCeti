/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.EmpiricalMeasure
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Divisibility probabilities for a uniform positive integer

For `m : ℕ` put `N = m + 1`. The empirical measure `empiricalMeasure (· + 1) m` of the sequence
`k ↦ k + 1` is the uniform probability measure on `{1, …, N}`; it is the arithmetic sample of
probabilistic number theory, where statements such as "a typical integer `n ≤ N` has about
`log log N` prime factors" are statements about this measure.

Counting positive multiples gives the exact probability that a fixed `d` divides the sample:
`⌊N / d⌋ / N` (`empiricalMeasure_add_one_real_dvd`). It differs from the model value `1 / d`
by the signed error `-(N % d) / (N d)`, which lies in `(-1 / N, 0]` and vanishes exactly over a
complete period `d ∣ N`. The joint event that `d` and `e` both divide the sample is the event that
their `lcm` divides it, so its probability is `⌊N / lcm d e⌋ / N`; for two distinct primes this is
`⌊N / (p q)⌋ / N`, for a repeated prime it is `⌊N / p⌋ / N`, and in general it is not the product
of the two marginal probabilities.

For the centered divisibility indicators `1_{p ∣ n} - 1 / p` the same counting gives the exact
average of a product of two of them, and its distance at most `2 / N` from the model value
`1 / lcm p q - 1 / (p q)`. For primes the model value is `1 / p - 1 / p ^ 2` on the diagonal and
`0` off it. These are the inputs to second-moment (Turán–Kubilius type) comparisons of sums of
divisibility indicators with independent Bernoulli models.

All statements hold for every natural `d`, `p` and `q`, including `0`: the sample avoids `0`, so
the event `0 ∣ n` has probability `0`, matching `⌊N / 0⌋ = 0` and `1 / 0 = 0` in `ℝ`.

## References

* T. Tao, *254A, Supplement 4: Probabilistic models and heuristics for the primes*, lecture
  notes (2015), Section 3.
-/

public section

noncomputable section

open MeasureTheory Finset

namespace TauCeti

namespace Probability

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Integrating against the uniform probability measure on `{1, …, m + 1}` is averaging the values
at `1, …, m + 1`. -/
theorem integral_empiricalMeasure_add_one (m : ℕ) (f : ℕ → E) :
    ∫ n, f n ∂(empiricalMeasure (· + 1) m : Measure ℕ) =
      (m + 1 : ℝ)⁻¹ • ∑ k ∈ range (m + 1), f (k + 1) := by
  rw [integral_empiricalMeasure .of_discrete, Nat.cast_add_one]

end Integral

/-- The number of `k < m + 1` with `d ∣ k + 1`, as a real sum of indicators, is `⌊(m + 1) / d⌋`. -/
private lemma sum_range_ite_dvd_add_one (m d : ℕ) :
    ∑ k ∈ range (m + 1), (if d ∣ k + 1 then (1 : ℝ) else 0) = ((m + 1) / d : ℕ) := by
  rw [sum_boole, Nat.card_multiples]

/-- Under the uniform probability measure on `{1, …, N}`, the probability that `d` divides the
sample is `⌊N / d⌋ / N`. -/
theorem empiricalMeasure_add_one_real_dvd (m d : ℕ) :
    (empiricalMeasure (· + 1) m : Measure ℕ).real {n | d ∣ n} =
      ((m + 1) / d : ℕ) / (m + 1 : ℝ) := by
  rw [← integral_indicator_one .of_discrete, integral_empiricalMeasure_add_one, smul_eq_mul,
    inv_mul_eq_div]
  congr 1
  rw [← sum_range_ite_dvd_add_one]
  exact sum_congr rfl fun k _ => by simp [Set.indicator_apply]

/-- The signed error of the divisibility probability against the model value `1 / d` is
`-(N % d) / (N d)`. -/
theorem empiricalMeasure_add_one_real_dvd_sub_inv (m d : ℕ) :
    (empiricalMeasure (· + 1) m : Measure ℕ).real {n | d ∣ n} - (d : ℝ)⁻¹ =
      -(((m + 1) % d : ℕ) : ℝ) / ((m + 1) * d) := by
  rcases eq_or_ne d 0 with rfl | hd
  · rw [empiricalMeasure_add_one_real_dvd]
    simp
  rw [empiricalMeasure_add_one_real_dvd]
  have hdiv := congrArg (Nat.cast : ℕ → ℝ) (Nat.div_add_mod (m + 1) d)
  push_cast at hdiv
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd
  have hm : (m + 1 : ℝ) ≠ 0 := Nat.cast_add_one_ne_zero m
  field_simp
  linear_combination hdiv

/-- The divisibility probability never exceeds the model value `1 / d`. -/
theorem empiricalMeasure_add_one_real_dvd_le_inv (m d : ℕ) :
    (empiricalMeasure (· + 1) m : Measure ℕ).real {n | d ∣ n} ≤ (d : ℝ)⁻¹ := by
  have h := empiricalMeasure_add_one_real_dvd_sub_inv m d
  have : -(((m + 1) % d : ℕ) : ℝ) / ((m + 1) * d) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by simp) (by positivity)
  linarith

/-- The divisibility probability falls short of the model value `1 / d` by less than `1 / N`. -/
theorem neg_inv_lt_empiricalMeasure_add_one_real_dvd_sub_inv (m d : ℕ) :
    -(m + 1 : ℝ)⁻¹ < (empiricalMeasure (· + 1) m : Measure ℕ).real {n | d ∣ n} - (d : ℝ)⁻¹ := by
  rw [empiricalMeasure_add_one_real_dvd_sub_inv]
  rcases eq_or_ne d 0 with rfl | hd
  · simp [Nat.cast_add_one_pos]
  have hmod : (((m + 1) % d : ℕ) : ℝ) < d := Nat.cast_lt.2 (Nat.mod_lt _ (Nat.pos_of_ne_zero hd))
  rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ (by positivity)]
  field_simp
  exact hmod

/-- The divisibility probability is within `1 / N` of the model value `1 / d`. -/
theorem abs_empiricalMeasure_add_one_real_dvd_sub_inv_le (m d : ℕ) :
    |(empiricalMeasure (· + 1) m : Measure ℕ).real {n | d ∣ n} - (d : ℝ)⁻¹| ≤ (m + 1 : ℝ)⁻¹ := by
  rw [abs_le]
  exact ⟨(neg_inv_lt_empiricalMeasure_add_one_real_dvd_sub_inv m d).le,
    (sub_nonpos.2 (empiricalMeasure_add_one_real_dvd_le_inv m d)).trans (by positivity)⟩

/-- Over a complete period, `d ∣ N`, the divisibility probability is exactly `1 / d`. -/
theorem empiricalMeasure_add_one_real_dvd_of_dvd {m d : ℕ} (h : d ∣ m + 1) :
    (empiricalMeasure (· + 1) m : Measure ℕ).real {n | d ∣ n} = (d : ℝ)⁻¹ := by
  have := empiricalMeasure_add_one_real_dvd_sub_inv m d
  rwa [Nat.mod_eq_zero_of_dvd h, Nat.cast_zero, neg_zero, zero_div, sub_eq_zero] at this

/-- The probability that both `d` and `e` divide the sample is `⌊N / lcm d e⌋ / N`. -/
theorem empiricalMeasure_add_one_real_dvd_and_dvd (m d e : ℕ) :
    (empiricalMeasure (· + 1) m : Measure ℕ).real {n | d ∣ n ∧ e ∣ n} =
      ((m + 1) / d.lcm e : ℕ) / (m + 1 : ℝ) := by
  simp_rw [← Nat.lcm_dvd_iff]
  exact empiricalMeasure_add_one_real_dvd m _

/-- For coprime `d` and `e`, in particular for distinct primes, the probability that both divide
the sample is `⌊N / (d e)⌋ / N`. -/
theorem empiricalMeasure_add_one_real_dvd_and_dvd_of_coprime {d e : ℕ} (h : d.Coprime e)
    (m : ℕ) :
    (empiricalMeasure (· + 1) m : Measure ℕ).real {n | d ∣ n ∧ e ∣ n} =
      ((m + 1) / (d * e) : ℕ) / (m + 1 : ℝ) := by
  rw [empiricalMeasure_add_one_real_dvd_and_dvd, h.lcm_eq_mul]

/-! ### Products of two centered divisibility indicators -/

/-- The average over `{1, …, N}` of the product of the centered divisibility indicators
`1_{p ∣ n} - 1 / p` and `1_{q ∣ n} - 1 / q` is
`⌊N / lcm p q⌋ / N - ⌊N / p⌋ / (N q) - ⌊N / q⌋ / (N p) + 1 / (p q)`. -/
theorem integral_empiricalMeasure_add_one_centered_dvd_mul (m p q : ℕ) :
    ∫ n, ((if p ∣ n then 1 else 0) - (p : ℝ)⁻¹) * ((if q ∣ n then 1 else 0) - (q : ℝ)⁻¹)
        ∂(empiricalMeasure (· + 1) m : Measure ℕ) =
      ((m + 1) / p.lcm q : ℕ) / (m + 1 : ℝ) - ((m + 1) / p : ℕ) / ((m + 1) * q) -
        ((m + 1) / q : ℕ) / ((m + 1) * p) + ((p : ℝ) * q)⁻¹ := by
  have key (n : ℕ) :
      ((if p ∣ n then 1 else 0) - (p : ℝ)⁻¹) * ((if q ∣ n then 1 else 0) - (q : ℝ)⁻¹) =
      (if p.lcm q ∣ n then 1 else 0) - (q : ℝ)⁻¹ * (if p ∣ n then 1 else 0) -
        (p : ℝ)⁻¹ * (if q ∣ n then 1 else 0) + (p : ℝ)⁻¹ * (q : ℝ)⁻¹ := by
    by_cases hp : p ∣ n <;> by_cases hq : q ∣ n <;> simp [Nat.lcm_dvd_iff, hp, hq] <;> ring
  simp_rw [key]
  rw [integral_empiricalMeasure_add_one, smul_eq_mul]
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_range_ite_dvd_add_one, sum_const,
    card_range, nsmul_eq_mul]
  have hm : (m + 1 : ℝ) ≠ 0 := Nat.cast_add_one_ne_zero m
  push_cast
  field_simp

/-- The signed divisibility error at `0` and at `1` vanishes. -/
private lemma empiricalMeasure_add_one_real_dvd_sub_inv_eq_zero (m : ℕ) {d : ℕ}
    (hd : d ≤ 1) : (empiricalMeasure (· + 1) m : Measure ℕ).real {n | d ∣ n} - (d : ℝ)⁻¹ = 0 := by
  interval_cases d
  · rw [empiricalMeasure_add_one_real_dvd_sub_inv]
    simp
  · rw [empiricalMeasure_add_one_real_dvd_of_dvd (one_dvd _), sub_self]

/-- The two cross errors in a centered divisibility product weigh at most `1 / N` together. -/
private lemma abs_sub_inv_mul_inv_add_le (m p q : ℕ) :
    |(empiricalMeasure (· + 1) m : Measure ℕ).real {n | p ∣ n} - (p : ℝ)⁻¹| * (q : ℝ)⁻¹ +
      |(empiricalMeasure (· + 1) m : Measure ℕ).real {n | q ∣ n} - (q : ℝ)⁻¹| * (p : ℝ)⁻¹ ≤
        (m + 1 : ℝ)⁻¹ := by
  have hp := abs_empiricalMeasure_add_one_real_dvd_sub_inv_le m p
  have hq := abs_empiricalMeasure_add_one_real_dvd_sub_inv_le m q
  have inv_le_one (d : ℕ) : (d : ℝ)⁻¹ ≤ 1 := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · exact inv_le_one_of_one_le₀ (Nat.one_le_cast.2 hd)
  rcases le_or_gt p 1 with hp1 | hp1
  · rw [empiricalMeasure_add_one_real_dvd_sub_inv_eq_zero m hp1, abs_zero, zero_mul, zero_add]
    exact (mul_le_of_le_one_right (abs_nonneg _) (inv_le_one p)).trans hq
  rcases le_or_gt q 1 with hq1 | hq1
  · rw [empiricalMeasure_add_one_real_dvd_sub_inv_eq_zero m hq1, abs_zero, zero_mul, add_zero]
    exact (mul_le_of_le_one_right (abs_nonneg _) (inv_le_one q)).trans hp
  calc _ ≤ (m + 1 : ℝ)⁻¹ * 2⁻¹ + (m + 1 : ℝ)⁻¹ * 2⁻¹ := by
        gcongr
        · exact_mod_cast (hq1 : 2 ≤ q)
        · exact_mod_cast (hp1 : 2 ≤ p)
    _ = (m + 1 : ℝ)⁻¹ := by ring

/-- The distance of a centered divisibility product average from its model value, written through
the three signed divisibility errors. -/
private lemma integral_empiricalMeasure_add_one_centered_dvd_mul_sub_eq (m p q : ℕ) :
    ∫ n, ((if p ∣ n then 1 else 0) - (p : ℝ)⁻¹) * ((if q ∣ n then 1 else 0) - (q : ℝ)⁻¹)
        ∂(empiricalMeasure (· + 1) m : Measure ℕ) -
      (((p.lcm q : ℕ) : ℝ)⁻¹ - ((p : ℝ) * q)⁻¹) =
    ((empiricalMeasure (· + 1) m : Measure ℕ).real {n | p.lcm q ∣ n} - ((p.lcm q : ℕ) : ℝ)⁻¹) -
      ((empiricalMeasure (· + 1) m : Measure ℕ).real {n | p ∣ n} - (p : ℝ)⁻¹) * (q : ℝ)⁻¹ -
      ((empiricalMeasure (· + 1) m : Measure ℕ).real {n | q ∣ n} - (q : ℝ)⁻¹) * (p : ℝ)⁻¹ := by
  rw [integral_empiricalMeasure_add_one_centered_dvd_mul, div_mul_eq_div_div, div_mul_eq_div_div,
    ← empiricalMeasure_add_one_real_dvd, ← empiricalMeasure_add_one_real_dvd,
    ← empiricalMeasure_add_one_real_dvd, mul_inv]
  ring

/-- The average over `{1, …, N}` of the product of the centered divisibility indicators of `p` and
`q` is within `2 / N` of the model value `1 / lcm p q - 1 / (p q)`. -/
theorem abs_integral_empiricalMeasure_add_one_centered_dvd_mul_sub_le (m p q : ℕ) :
    |∫ n, ((if p ∣ n then 1 else 0) - (p : ℝ)⁻¹) * ((if q ∣ n then 1 else 0) - (q : ℝ)⁻¹)
        ∂(empiricalMeasure (· + 1) m : Measure ℕ) -
      (((p.lcm q : ℕ) : ℝ)⁻¹ - ((p : ℝ) * q)⁻¹)| ≤ 2 / (m + 1 : ℝ) := by
  rw [integral_empiricalMeasure_add_one_centered_dvd_mul_sub_eq]
  have hl := abs_empiricalMeasure_add_one_real_dvd_sub_inv_le m (p.lcm q)
  have hpq := abs_sub_inv_mul_inv_add_le m p q
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_inv, Nat.abs_cast]
  grw [abs_sub, abs_mul, abs_inv, Nat.abs_cast]
  linarith [div_eq_mul_inv (2 : ℝ) (m + 1)]

/-- Over a complete period, `p ∣ N` and `q ∣ N`, the average of the product of the centered
divisibility indicators of `p` and `q` is exactly the model value `1 / lcm p q - 1 / (p q)`. -/
theorem integral_empiricalMeasure_add_one_centered_dvd_mul_of_dvd {m p q : ℕ} (hp : p ∣ m + 1)
    (hq : q ∣ m + 1) :
    ∫ n, ((if p ∣ n then 1 else 0) - (p : ℝ)⁻¹) * ((if q ∣ n then 1 else 0) - (q : ℝ)⁻¹)
        ∂(empiricalMeasure (· + 1) m : Measure ℕ) = ((p.lcm q : ℕ) : ℝ)⁻¹ - ((p : ℝ) * q)⁻¹ := by
  rw [← sub_eq_zero, integral_empiricalMeasure_add_one_centered_dvd_mul_sub_eq,
    empiricalMeasure_add_one_real_dvd_of_dvd hp,
    empiricalMeasure_add_one_real_dvd_of_dvd hq,
    empiricalMeasure_add_one_real_dvd_of_dvd (Nat.lcm_dvd hp hq)]
  simp

/-- For primes `p` and `q` the model value `1 / lcm p q - 1 / (p q)` is `1 / p - 1 / p ^ 2` when
`p = q` and `0` otherwise. -/
private lemma inv_lcm_sub_inv_mul_of_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    ((p.lcm q : ℕ) : ℝ)⁻¹ - ((p : ℝ) * q)⁻¹ =
      if p = q then (p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹ else 0 := by
  split_ifs with h
  · subst h
    rw [Nat.lcm_self, sq]
  · rw [((Nat.coprime_primes hp hq).2 h).lcm_eq_mul, Nat.cast_mul, sub_self]

/-- For primes `p` and `q`, the average over `{1, …, N}` of the product of their centered
divisibility indicators is within `2 / N` of `1 / p - 1 / p ^ 2` when `p = q`, and of `0`
otherwise. Divisibility by distinct primes need not be independent under this measure; the
error term absorbs the dependence. -/
theorem abs_integral_empiricalMeasure_add_one_centered_dvd_mul_sub_ite_le {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (m : ℕ) :
    |∫ n, ((if p ∣ n then 1 else 0) - (p : ℝ)⁻¹) * ((if q ∣ n then 1 else 0) - (q : ℝ)⁻¹)
        ∂(empiricalMeasure (· + 1) m : Measure ℕ) -
      (if p = q then (p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹ else 0)| ≤ 2 / (m + 1 : ℝ) := by
  rw [← inv_lcm_sub_inv_mul_of_prime hp hq]
  exact abs_integral_empiricalMeasure_add_one_centered_dvd_mul_sub_le m p q

/-- For primes `p` and `q` dividing `N`, the average over `{1, …, N}` of the product of their
centered divisibility indicators is exactly `1 / p - 1 / p ^ 2` when `p = q`, and `0` otherwise:
over a complete period, divisibility by distinct primes is independent. -/
theorem integral_empiricalMeasure_add_one_centered_dvd_mul_of_prime_of_dvd {m p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpm : p ∣ m + 1) (hqm : q ∣ m + 1) :
    ∫ n, ((if p ∣ n then 1 else 0) - (p : ℝ)⁻¹) * ((if q ∣ n then 1 else 0) - (q : ℝ)⁻¹)
        ∂(empiricalMeasure (· + 1) m : Measure ℕ) =
      if p = q then (p : ℝ)⁻¹ - ((p : ℝ) ^ 2)⁻¹ else 0 := by
  rw [integral_empiricalMeasure_add_one_centered_dvd_mul_of_dvd hpm hqm,
    inv_lcm_sub_inv_mul_of_prime hp hq]

end Probability

end TauCeti
