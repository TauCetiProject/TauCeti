/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Algebra.BigOperators.Field
import TauCeti.Data.Nat.Interval
import TauCeti.NumberTheory.AlmostPrime

/-!
# Selberg's parity sequences

The two sequences `a_odd(n) = (1 - λ(n)) / 2` and `a_even(n) = (1 + λ(n)) / 2`, for `n > 0` and
with `λ` the Liouville function, are the indicators of an odd and of an even number of prime
factors counted with multiplicity. Their sums over the multiples of `d` up to `N` have the same
main term `⌊N / d⌋ / 2` and differ only through the Liouville partial sum
`λ(d) ∑_{m ≤ N / d} λ(m)`, so a sieve that sees only these sums up to a small error cannot
distinguish them. Yet after sifting by all primes below `z`, the even sequence retains only
`n = 1` when `N < z ^ 2`, and the odd sequence retains exactly the primes in `[z, N]` when
`N < z ^ 3`. This is Selberg's example for the parity problem.

## Main definitions

* `TauCeti.SieveApplications.oddParityWeight`, `TauCeti.SieveApplications.evenParityWeight`: the
  two sequences, as real arithmetic functions vanishing at `0`.

## Main results

* `TauCeti.SieveApplications.oddParityWeight_eq_ite`,
  `TauCeti.SieveApplications.evenParityWeight_eq_ite`: the weights are the indicators of odd and
  even `Ω(n)`.
* `TauCeti.SieveApplications.oddParityWeight_add_evenParityWeight`: they sum to `1` at `n ≠ 0`.
* `TauCeti.SieveApplications.sum_Icc_filter_dvd_oddParityWeight`,
  `TauCeti.SieveApplications.sum_Icc_filter_dvd_evenParityWeight`: the sums over the multiples of
  `d` in `[1, N]` are `(⌊N / d⌋ ∓ λ(d) ∑_{m ≤ N / d} λ(m)) / 2`.
* `TauCeti.SieveApplications.evenParityWeight_eq_one_iff_of_lt_sq`,
  `TauCeti.SieveApplications.oddParityWeight_eq_one_iff_of_lt_cube`: for `n` with every prime
  factor at least `z`, the even weight is `1` only at `n = 1` if `n < z ^ 2`, and the odd weight
  is `1` exactly at the primes if `n < z ^ 3`.
* `TauCeti.SieveApplications.sum_Icc_filter_rough_evenParityWeight`,
  `TauCeti.SieveApplications.sum_Icc_filter_rough_oddParityWeight`: the sifted sums are `1` for
  `1 ≤ N < z ^ 2` and the number of primes in `[z, N]` for `N < z ^ 3`.

## References

* D. R. Heath-Brown, *Lectures on sieves*, arXiv:math/0209360, §4, pp. 24–26: the sequences
  `A⁺` (here the odd one) and `A⁻` (the even one), the count `#A±_d`, and estimate (4.2).
-/

public section

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Omega

namespace TauCeti.SieveApplications

variable {n z N : ℕ}

/-- The odd parity sequence `a_odd(n) = (1 - λ(n)) / 2` for `n ≠ 0`, with `a_odd(0) = 0`: the
indicator of an odd number of prime factors counted with multiplicity. -/
noncomputable def oddParityWeight : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n = 0 then 0 else (1 - (liouville n : ℝ)) / 2, ite_eq_left rfl⟩

/-- The even parity sequence `a_even(n) = (1 + λ(n)) / 2` for `n ≠ 0`, with `a_even(0) = 0`: the
indicator of an even number of prime factors counted with multiplicity. -/
noncomputable def evenParityWeight : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n = 0 then 0 else (1 + (liouville n : ℝ)) / 2, ite_eq_left rfl⟩

/-- The odd parity weight at `n ≠ 0` in terms of the Liouville function. -/
theorem oddParityWeight_apply (hn : n ≠ 0) :
    oddParityWeight n = (1 - (liouville n : ℝ)) / 2 :=
  ite_eq_right hn

/-- The even parity weight at `n ≠ 0` in terms of the Liouville function. -/
theorem evenParityWeight_apply (hn : n ≠ 0) :
    evenParityWeight n = (1 + (liouville n : ℝ)) / 2 :=
  ite_eq_right hn

/-- The odd parity weight at `n ≠ 0` is `(1 - (-1) ^ Ω(n)) / 2`. -/
theorem oddParityWeight_apply_eq_pow (hn : n ≠ 0) :
    oddParityWeight n = (1 - (-1 : ℝ) ^ Ω n) / 2 := by
  rw [oddParityWeight_apply hn, liouville_apply hn]
  push_cast
  rfl

/-- The even parity weight at `n ≠ 0` is `(1 + (-1) ^ Ω(n)) / 2`. -/
theorem evenParityWeight_apply_eq_pow (hn : n ≠ 0) :
    evenParityWeight n = (1 + (-1 : ℝ) ^ Ω n) / 2 := by
  rw [evenParityWeight_apply hn, liouville_apply hn]
  push_cast
  rfl

/-- The odd parity weight at `n ≠ 0` is the indicator of `Ω(n)` being odd. -/
theorem oddParityWeight_eq_ite (hn : n ≠ 0) :
    oddParityWeight n = if Odd (Ω n) then 1 else 0 := by
  rw [oddParityWeight_apply_eq_pow hn]
  split_ifs with h
  · rw [h.neg_one_pow]
    norm_num
  · rw [(Nat.not_odd_iff_even.1 h).neg_one_pow]
    norm_num

/-- The even parity weight at `n ≠ 0` is the indicator of `Ω(n)` being even. -/
theorem evenParityWeight_eq_ite (hn : n ≠ 0) :
    evenParityWeight n = if Even (Ω n) then 1 else 0 := by
  rw [evenParityWeight_apply_eq_pow hn]
  split_ifs with h
  · rw [h.neg_one_pow]
    norm_num
  · rw [(Nat.not_even_iff_odd.1 h).neg_one_pow]
    norm_num

/-- At `n ≠ 0` the two parity weights sum to `1`. -/
theorem oddParityWeight_add_evenParityWeight (hn : n ≠ 0) :
    oddParityWeight n + evenParityWeight n = 1 := by
  rw [oddParityWeight_apply hn, evenParityWeight_apply hn]
  ring

/-- The odd parity weight takes only the values `0` and `1`. -/
theorem oddParityWeight_eq_zero_or_eq_one (n : ℕ) :
    oddParityWeight n = 0 ∨ oddParityWeight n = 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact Or.inl ArithmeticFunction.map_zero
  · rw [oddParityWeight_eq_ite hn]
    exact (ite_eq_or_eq _ _ _).symm

/-- The even parity weight takes only the values `0` and `1`. -/
theorem evenParityWeight_eq_zero_or_eq_one (n : ℕ) :
    evenParityWeight n = 0 ∨ evenParityWeight n = 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact Or.inl ArithmeticFunction.map_zero
  · rw [evenParityWeight_eq_ite hn]
    exact (ite_eq_or_eq _ _ _).symm

/-- **The divisor sums of the odd parity sequence.** The sum of the odd parity weight over the
multiples of `d` in `[1, N]` is `(⌊N / d⌋ - λ(d) ∑_{m ≤ N / d} λ(m)) / 2`. -/
theorem sum_Icc_filter_dvd_oddParityWeight (d N : ℕ) :
    ∑ n ∈ Icc 1 N with d ∣ n, oddParityWeight n =
      (((N / d : ℕ) : ℝ) - (liouville d : ℝ) * ∑ m ∈ Icc 1 (N / d), (liouville m : ℝ)) / 2 := by
  rcases eq_or_ne d 0 with rfl | hd
  · have h0 : ∀ n ∈ (Icc 1 N).filter (0 ∣ ·), oddParityWeight n = 0 := fun n hn ↦ by
      rw [zero_dvd_iff.1 (mem_filter.1 hn).2, ArithmeticFunction.map_zero]
    rw [sum_eq_zero h0]
    simp
  have hterm (m : ℕ) (hm : m ∈ Icc 1 (N / d)) : oddParityWeight (d * m) =
      (1 - (liouville d : ℝ) * (liouville m : ℝ)) / 2 := by
    rw [oddParityWeight_apply (mul_ne_zero hd (by have := (mem_Icc.1 hm).1; omega)),
      liouville_apply_mul, Int.cast_mul]
  rw [Nat.sum_Icc_filter_dvd_eq, sum_congr rfl hterm, ← sum_div, sum_sub_distrib, ← mul_sum]
  simp

/-- **The divisor sums of the even parity sequence.** The sum of the even parity weight over the
multiples of `d` in `[1, N]` is `(⌊N / d⌋ + λ(d) ∑_{m ≤ N / d} λ(m)) / 2`. -/
theorem sum_Icc_filter_dvd_evenParityWeight (d N : ℕ) :
    ∑ n ∈ Icc 1 N with d ∣ n, evenParityWeight n =
      (((N / d : ℕ) : ℝ) + (liouville d : ℝ) * ∑ m ∈ Icc 1 (N / d), (liouville m : ℝ)) / 2 := by
  rcases eq_or_ne d 0 with rfl | hd
  · have h0 : ∀ n ∈ (Icc 1 N).filter (0 ∣ ·), evenParityWeight n = 0 := fun n hn ↦ by
      rw [zero_dvd_iff.1 (mem_filter.1 hn).2, ArithmeticFunction.map_zero]
    rw [sum_eq_zero h0]
    simp
  have hterm (m : ℕ) (hm : m ∈ Icc 1 (N / d)) : evenParityWeight (d * m) =
      (1 + (liouville d : ℝ) * (liouville m : ℝ)) / 2 := by
    rw [evenParityWeight_apply (mul_ne_zero hd (by have := (mem_Icc.1 hm).1; omega)),
      liouville_apply_mul, Int.cast_mul]
  rw [Nat.sum_Icc_filter_dvd_eq, sum_congr rfl hterm, ← sum_div, sum_add_distrib, ← mul_sum]
  simp

/-- A number below `z ^ 2` all of whose prime factors are at least `z` has at most one prime
factor, counted with multiplicity. -/
private theorem cardFactors_le_one_of_lt_sq (hn : n ≠ 0) (h : ∀ p ∈ n.primeFactors, z ≤ p)
    (hlt : n < z ^ 2) : Ω n ≤ 1 :=
  (Nat.isAtMostAlmostPrime_of_lt_pow hn h hlt).2

/-- **The even survivor above the square root.** For `n < z ^ 2` all of whose prime factors are at
least `z`, the even parity weight is `1` exactly at `n = 1`. -/
theorem evenParityWeight_eq_one_iff_of_lt_sq (h : ∀ p ∈ n.primeFactors, z ≤ p)
    (hlt : n < z ^ 2) : evenParityWeight n = 1 ↔ n = 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hΩ := cardFactors_le_one_of_lt_sq hn h hlt
  rw [evenParityWeight_eq_ite hn, ite_eq_left_iff, not_imp_comm]
  simp only [zero_ne_one, not_false_eq_true, forall_const]
  constructor
  · intro heven
    have h0 : Ω n = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hΩ with h0 | h1
      · exact h0
      · rw [h1] at heven
        exact absurd heven (by decide)
    exact (cardFactors_eq_zero_iff_eq_zero_or_one.1 h0).resolve_left hn
  · rintro rfl
    simp

/-- **The odd survivors above the cube root.** For `n < z ^ 3` all of whose prime factors are at
least `z`, the odd parity weight is `1` exactly when `n` is prime: such an `n` has at most two
prime factors. -/
theorem oddParityWeight_eq_one_iff_of_lt_cube (h : ∀ p ∈ n.primeFactors, z ≤ p)
    (hlt : n < z ^ 3) : oddParityWeight n = 1 ↔ n.Prime := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Nat.not_prime_zero]
  have hΩ : Ω n ≤ 2 := (Nat.isAtMostAlmostPrime_of_lt_pow hn h hlt).2
  rw [oddParityWeight_eq_ite hn, ite_eq_left_iff, not_imp_comm, ← cardFactors_eq_one_iff_prime]
  simp only [zero_ne_one, not_false_eq_true, forall_const]
  constructor
  · intro hodd
    have hcases : Ω n = 0 ∨ Ω n = 1 ∨ Ω n = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · rw [h0] at hodd
      exact absurd hodd (by decide)
    · exact h1
    · rw [h2] at hodd
      exact absurd hodd (by decide)
  · intro h1
    rw [h1]
    exact odd_one

/-- **The sifted sum of the even parity sequence above the square root.** If `1 ≤ N < z ^ 2`, the
sum of the even parity weight over the `n ≤ N` with every prime factor at least `z` is `1`: only
`n = 1` survives. -/
theorem sum_Icc_filter_rough_evenParityWeight (hN : 1 ≤ N) (hNz : N < z ^ 2) :
    ∑ n ∈ Icc 1 N with ∀ p ∈ n.primeFactors, z ≤ p, evenParityWeight n = 1 := by
  rw [sum_eq_single 1]
  · rw [evenParityWeight_eq_ite one_ne_zero, cardFactors_one, ite_eq_left Even.zero]
  · intro n hn hn1
    obtain ⟨hn, hrough⟩ := mem_filter.1 hn
    rcases evenParityWeight_eq_zero_or_eq_one n with h0 | h1
    · exact h0
    · exact absurd ((evenParityWeight_eq_one_iff_of_lt_sq hrough
        ((mem_Icc.1 hn).2.trans_lt hNz)).1 h1) hn1
  · intro h1
    exact absurd (mem_filter.2 ⟨mem_Icc.2 ⟨le_rfl, hN⟩, by simp⟩) h1

/-- **The sifted sum of the odd parity sequence above the cube root.** If `N < z ^ 3`, the sum
of the odd parity weight over the `n ≤ N` with every prime factor at least `z` is the number of
primes in `[z, N]`. -/
theorem sum_Icc_filter_rough_oddParityWeight (hNz : N < z ^ 3) :
    ∑ n ∈ Icc 1 N with ∀ p ∈ n.primeFactors, z ≤ p, oddParityWeight n =
      #{p ∈ Icc z N | p.Prime} := by
  have hterm (n : ℕ) (hn : n ∈ (Icc 1 N).filter fun n ↦ ∀ p ∈ n.primeFactors, z ≤ p) :
      oddParityWeight n = if n.Prime then 1 else 0 := by
    obtain ⟨hn, hrough⟩ := mem_filter.1 hn
    have hiff := oddParityWeight_eq_one_iff_of_lt_cube hrough ((mem_Icc.1 hn).2.trans_lt hNz)
    split_ifs with hp
    · exact hiff.2 hp
    · exact (oddParityWeight_eq_zero_or_eq_one n).resolve_right fun h1 ↦ hp (hiff.1 h1)
  rw [sum_congr rfl hterm, sum_boole, filter_filter]
  congr 2
  ext p
  simp only [mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨_, hpN⟩, hrough, hp⟩
    exact ⟨⟨hrough p (hp.mem_primeFactors_self), hpN⟩, hp⟩
  · rintro ⟨⟨hzp, hpN⟩, hp⟩
    refine ⟨⟨hp.one_le, hpN⟩, fun q hq ↦ ?_, hp⟩
    rw [hp.primeFactors, mem_singleton] at hq
    exact hq ▸ hzp

/-! ### Examples -/

/-- `1` has even weight `1` and odd weight `0`. -/
example : evenParityWeight 1 = 1 ∧ oddParityWeight 1 = 0 := by
  simp [evenParityWeight_eq_ite, oddParityWeight_eq_ite]

/-- `4 = 2 ^ 2` has even parity, although it has only one distinct prime factor. -/
example : evenParityWeight 4 = 1 := by
  rw [evenParityWeight_eq_ite (by norm_num), show (4 : ℕ) = 2 ^ 2 by norm_num,
    cardFactors_apply_prime_pow Nat.prime_two, ite_eq_left (by decide)]

/-- `12 = 2 ^ 2 * 3` has odd weight `1`, since `Ω(12) = 3`. -/
example : oddParityWeight 12 = 1 := by
  rw [oddParityWeight_eq_ite (by norm_num), show (12 : ℕ) = 2 ^ 2 * 3 by norm_num,
    cardFactors_mul (by norm_num) (by norm_num), cardFactors_apply_prime_pow Nat.prime_two,
    cardFactors_apply_prime Nat.prime_three, ite_eq_left (by decide)]

/-- Zero has neither weight. -/
example : evenParityWeight 0 = 0 ∧ oddParityWeight 0 = 0 :=
  ⟨ArithmeticFunction.map_zero, ArithmeticFunction.map_zero⟩

end TauCeti.SieveApplications
