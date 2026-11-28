/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.LocalPrimeSum

/-!
# Subtotals of local quadratic prime sums

A finite set of primes need not be an initial segment. For a nonnegative kernel of bounded
support on prime powers, the logarithmically weighted subtotal over any such set is bounded by
the full signed von Mangoldt sum. Applied row by row to positive-part kernels with varying
weights, this bounds the total logarithmic cost of local divisibility by the global prime sums.

The finite-prime subtotal for these kernels is `New.Data.sum_localPrimeSumTotal_mul_log_le`
in `grh/src/New/UpperBound/Size/Estimates.lean` of lsernau/grh-lean (revision `72fead1`).
-/

public section

open ArithmeticFunction Finset

namespace TauCeti.OneSidedBound

/-- A logarithmically weighted subtotal of the local Legendre prime sums is bounded by the
full Legendre-weighted von Mangoldt sum. The kernel only needs to be nonnegative on prime
powers and zero at prime powers greater than `A`; `U` can contain primes above `A`. -/
theorem sum_mul_log_mul_localPrimeSum_le (d : ℕ) [Fact d.Prime] {A : ℕ} {U : Finset ℕ}
    (hU : ∀ p ∈ U, Nat.Prime p) {f : ℕ → ℝ} (h₀ : ∀ n, IsPrimePow n → 0 ≤ f n)
    (hA : ∀ n > A, IsPrimePow n → f n = 0) :
    ∑ p ∈ U, (2 * Real.log p) * localPrimeSum d p f ≤
      ∑ n ∈ Icc 1 A, vonMangoldt n * (1 - (legendreSym d n : ℝ)) * f n := by
  rw [sum_vonMangoldt_mul_one_sub_legendreSym_eq_sum_localPrimeSum d le_rfl hA]
  have hsub : U.filter (· ≤ A) ⊆ Nat.primesLE A := fun p hp ↦
    Nat.mem_primesLE.mpr ⟨(mem_filter.mp hp).2, hU p (mem_filter.mp hp).1⟩
  calc
    _ = ∑ p ∈ U.filter (· ≤ A), (2 * Real.log p) * localPrimeSum d p f := by
      symm
      refine sum_subset (filter_subset _ _) fun p hp hnot ↦ ?_
      have hp' := hU p hp
      have hlt : A < p := lt_of_not_ge fun h ↦ hnot (mem_filter.mpr ⟨hp, h⟩)
      rw [localPrimeSum_eq_zero_of_lt_prime hlt (fun e he h ↦
        hA _ h ((isPrimePow_pow_iff he.ne').mpr hp'.isPrimePow)), mul_zero]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun p hp _ ↦ by
      have hp' := Nat.prime_of_mem_primesLE hp
      exact mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hp'.one_le)))
        (localPrimeSum_nonneg fun e he ↦ h₀ _ ((isPrimePow_pow_iff he.ne').mpr hp'.isPrimePow))

/-- Bound the logarithmically weighted local totals over `U` by the sum of the global
positive-part prime sums over the rows. Here `y i` is the order of row `i`, and `w i n`
is the weight read at the partner of that row for index `n`. If `W ≥ 0` is a common lower
bound on the weights, orders at most `A * W` ensure that no index beyond `A` contributes. -/
theorem sum_mul_log_mul_sum_localPrimeSum_le (d : ℕ) [Fact d.Prime] {ι : Type*} (s : Finset ι)
    {A : ℕ} {U : Finset ℕ} (hU : ∀ p ∈ U, Nat.Prime p) {y : ι → ℝ} {w : ι → ℕ → ℝ}
    {W : ℝ} (hW : 0 ≤ W) (hy : ∀ i ∈ s, y i ≤ A * W)
    (hw : ∀ i ∈ s, ∀ n > A, W ≤ w i n) :
    ∑ p ∈ U, (2 * Real.log p) * (∑ i ∈ s, localPrimeSum d p (fun n ↦ max (y i / n - w i n) 0)) ≤
      ∑ i ∈ s, ∑ n ∈ Icc 1 A,
        vonMangoldt n * (1 - (legendreSym d n : ℝ)) * max (y i / n - w i n) 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_le_sum fun i hi ↦ sum_mul_log_mul_localPrimeSum_le d hU
    (fun n _ ↦ le_max_right _ _) (fun n hn _ ↦ max_eq_right (sub_nonpos.mpr ?_))
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr ((Nat.zero_le A).trans_lt hn)
  have hAn : (A : ℝ) ≤ n := Nat.cast_le.mpr hn.le
  refine ((div_le_iff₀ hn₀).mpr ?_).trans (hw i hi n hn)
  simpa only [mul_comm W] using (hy i hi).trans (mul_le_mul_of_nonneg_right hAn hW)

end TauCeti.OneSidedBound
