/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk, The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.SelbergSieve

import TauCeti.NumberTheory.ArithmeticFunction.Moebius

/-!
# Normalized finite Selberg weights

For a Mathlib bounding sieve and a real cutoff, the normalized upper-divisor sum gives
weights whose quadratic main term is the reciprocal truncated sum of `selbergTerms`.
This identity includes a zero normalizer: totalized weights and the main term are then zero.
Normalization at one and the finite upper bound still require a cutoff containing one.
The weights are supported on divisors of the sieving product within the inclusive cutoff.

The construction is adapted from Arend Mellendijk's Selberg sieve in PNT+.
-/

public noncomputable section

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace BoundingSieve

/-- The Selberg normalizing sum truncated at a real cutoff. -/
def truncatedSelbergSum (s : BoundingSieve) (z : ℝ) : ℝ :=
  ∑ d ∈ s.prodPrimes.divisors, if (d : ℝ) ≤ z then s.selbergTerms d else 0

/-- The defining formula for the truncated Selberg normalizer. -/
theorem truncatedSelbergSum_def (s : BoundingSieve) (z : ℝ) :
    s.truncatedSelbergSum z =
      ∑ d ∈ s.prodPrimes.divisors, if (d : ℝ) ≤ z then s.selbergTerms d else 0 := by
  rfl

/-- Normalized Selberg weights, written as an upper-divisor sum. -/
def selbergWeights (s : BoundingSieve) (z : ℝ) (d : ℕ) : ℝ :=
  if d ∣ s.prodPrimes then
    (s.nu d)⁻¹ * (μ d : ℝ) * (s.truncatedSelbergSum z)⁻¹ *
      ∑ l ∈ s.prodPrimes.divisors,
        if d ∣ l ∧ (l : ℝ) ≤ z then s.selbergTerms l else 0
  else 0

/-- The defining upper-divisor formula for the normalized Selberg weights. -/
theorem selbergWeights_def (s : BoundingSieve) (z : ℝ) (d : ℕ) :
    s.selbergWeights z d =
      if d ∣ s.prodPrimes then
        (s.nu d)⁻¹ * (μ d : ℝ) * (s.truncatedSelbergSum z)⁻¹ *
          ∑ l ∈ s.prodPrimes.divisors,
            if d ∣ l ∧ (l : ℝ) ≤ z then s.selbergTerms l else 0
      else 0 := by
  rfl

/-- The normalizing sum is positive whenever the cutoff contains one. -/
theorem truncatedSelbergSum_pos (s : BoundingSieve) {z : ℝ} (hz : 1 ≤ z) :
    0 < s.truncatedSelbergSum z := by
  rw [truncatedSelbergSum, ← sum_filter]
  apply sum_pos
  · intro d hd
    exact s.selbergTerms_pos (dvd_of_mem_divisors (mem_filter.mp hd).1)
  · exact ⟨1, mem_filter.mpr ⟨one_mem_divisors.mpr s.prodPrimes_ne_zero, by simpa using hz⟩⟩

/-- A Selberg weight vanishes off the divisors of the sieving product. -/
@[simp] theorem selbergWeights_eq_zero_of_not_dvd (s : BoundingSieve) (z : ℝ) {d : ℕ}
    (hd : ¬d ∣ s.prodPrimes) : s.selbergWeights z d = 0 := by
  simp [selbergWeights, hd]

/-- Multiplying a weight by the local density cancels its density denominator. -/
theorem nu_mul_selbergWeights (s : BoundingSieve) (z : ℝ) (d : ℕ) :
    s.nu d * s.selbergWeights z d =
      (μ d : ℝ) * (s.truncatedSelbergSum z)⁻¹ *
        ∑ l ∈ s.prodPrimes.divisors,
          if d ∣ l ∧ (l : ℝ) ≤ z then s.selbergTerms l else 0 := by
  by_cases hd : d ∣ s.prodPrimes
  · rw [selbergWeights, ite_eq_left hd]
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (s.nu_ne_zero hd), one_mul]
  · rw [s.selbergWeights_eq_zero_of_not_dvd z hd, mul_zero]
    have hsum : (∑ l ∈ s.prodPrimes.divisors,
        if d ∣ l ∧ (l : ℝ) ≤ z then s.selbergTerms l else 0) = 0 := by
      apply sum_eq_zero
      intro l hl
      exact ite_eq_right fun h => hd (h.1.trans (dvd_of_mem_divisors hl))
    rw [hsum, mul_zero]

private theorem sum_moebius_upper_in_product (s : BoundingSieve) (l m : ℕ)
    (hm : m ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors,
      if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by
  have h := ArithmeticFunction.sum_moebius_upper l m (s.squarefree_of_dvd_prodPrimes hm)
  have h' : (∑ d ∈ m.divisors, if l ∣ d then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by exact_mod_cast h
  calc
    _ = ∑ d ∈ s.prodPrimes.divisors,
        if d ∣ m then if l ∣ d then (μ d : ℝ) else 0 else 0 := by
      apply sum_congr rfl
      intro d _
      split_ifs <;> simp_all
    _ = ∑ d ∈ m.divisors, if l ∣ d then (μ d : ℝ) else 0 := by
      rw [← sum_filter, Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero hm]
    _ = _ := h'

/-- The upper-divisor transform of the normalized weights is the prescribed diagonal. -/
theorem sum_nu_mul_selbergWeights (s : BoundingSieve) (z : ℝ) (l : ℕ)
    (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * s.selbergWeights z d else 0) =
      if (l : ℝ) ≤ z then
        (μ l : ℝ) * s.selbergTerms l * (s.truncatedSelbergSum z)⁻¹ else 0 := by
  calc
    _ = ∑ d ∈ s.prodPrimes.divisors, ∑ r ∈ s.prodPrimes.divisors,
        if l ∣ d ∧ d ∣ r ∧ (r : ℝ) ≤ z then
          (μ d : ℝ) * (s.truncatedSelbergSum z)⁻¹ * s.selbergTerms r else 0 := by
      apply sum_congr rfl
      intro d _
      rw [s.nu_mul_selbergWeights, mul_sum]
      by_cases hd : l ∣ d <;> simp [hd, mul_ite]
    _ = ∑ r ∈ s.prodPrimes.divisors, if (r : ℝ) ≤ z then
        (∑ d ∈ s.prodPrimes.divisors, if l ∣ d ∧ d ∣ r then (μ d : ℝ) else 0) *
          (s.truncatedSelbergSum z)⁻¹ * s.selbergTerms r else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro r _
      by_cases hr : (r : ℝ) ≤ z
      · simp only [hr, and_true, ite_eq_left, sum_mul, ite_mul, zero_mul]
      · simp [hr]
    _ = ∑ r ∈ s.prodPrimes.divisors, if (r : ℝ) ≤ z then
        (if l = r then (μ l : ℝ) else 0) *
          (s.truncatedSelbergSum z)⁻¹ * s.selbergTerms r else 0 := by
      apply sum_congr rfl
      intro r hr
      rw [sum_moebius_upper_in_product s l r (dvd_of_mem_divisors hr)]
    _ = _ := by
      rw [sum_eq_single l]
      · simp only [ite_true]
        split_ifs <;> ring
      · intro r _ hrl
        simp [Ne.symm hrl]
      · intro h
        exact False.elim (h (mem_divisors.mpr ⟨hl, s.prodPrimes_ne_zero⟩))

/-- The Selberg weight at one is normalized to one. -/
@[simp] theorem selbergWeights_one (s : BoundingSieve) {z : ℝ} (hz : 1 ≤ z) :
    s.selbergWeights z 1 = 1 := by
  simp only [selbergWeights, one_dvd, ite_true, s.nu_mult.map_one, inv_one,
    moebius_apply_one, Int.cast_one, mul_one, one_mul, true_and]
  rw [← truncatedSelbergSum, inv_mul_cancel₀ (s.truncatedSelbergSum_pos hz).ne']

/-- A normalized weight vanishes when its index lies beyond the cutoff. -/
@[simp] theorem selbergWeights_eq_zero_of_lt (s : BoundingSieve) (z : ℝ) (d : ℕ)
    (hd : z < (d : ℝ)) : s.selbergWeights z d = 0 := by
  unfold selbergWeights
  split_ifs
  · have hsum : (∑ l ∈ s.prodPrimes.divisors,
        if d ∣ l ∧ (l : ℝ) ≤ z then s.selbergTerms l else 0) = 0 := by
      apply sum_eq_zero
      intro l hl
      apply ite_eq_right
      intro h
      have hdl : (d : ℝ) ≤ l := by
        exact_mod_cast Nat.le_of_dvd (pos_of_mem_divisors hl) h.1
      exact (not_le_of_gt hd) (hdl.trans h.2)
    rw [hsum, mul_zero]
  · rfl

/-- The quadratic main term is the reciprocal normalizer for every real cutoff, including
the totalized zero-normalizer case. -/
theorem mainSum_lambdaSquared_selbergWeights (s : BoundingSieve) {z : ℝ} :
    s.mainSum (lambdaSquared (s.selbergWeights z)) = (s.truncatedSelbergSum z)⁻¹ := by
  by_cases hG : s.truncatedSelbergSum z = 0
  · have hw : s.selbergWeights z = fun _ ↦ 0 := by
      funext d
      simp [selbergWeights, hG]
    simp [hw, mainSum, lambdaSquared, hG]
  rw [mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  calc
    _ = ∑ l ∈ s.prodPrimes.divisors,
        if (l : ℝ) ≤ z then s.selbergTerms l * (s.truncatedSelbergSum z)⁻¹ ^ 2 else 0 := by
      apply sum_congr rfl
      intro l hl
      rw [s.sum_nu_mul_selbergWeights z l (dvd_of_mem_divisors hl)]
      split_ifs with h
      · have hmu : (μ l : ℝ) ^ 2 = 1 := by
          exact_mod_cast moebius_sq_eq_one_of_squarefree
            (s.squarefree_of_mem_divisors_prodPrimes hl)
        have hg : s.selbergTerms l ≠ 0 := (s.selbergTerms_pos (dvd_of_mem_divisors hl)).ne'
        calc
          _ = (μ l : ℝ) ^ 2 * ((s.selbergTerms l)⁻¹ * s.selbergTerms l) *
              s.selbergTerms l * (s.truncatedSelbergSum z)⁻¹ ^ 2 := by ring
          _ = _ := by rw [hmu, inv_mul_cancel₀ hg, one_mul, one_mul]
      · simp
    _ = s.truncatedSelbergSum z * (s.truncatedSelbergSum z)⁻¹ ^ 2 := by
      rw [truncatedSelbergSum, sum_mul]
      apply sum_congr rfl
      intro l _
      split_ifs <;> simp_all
    _ = _ := by
      rw [sq, ← mul_assoc, mul_inv_cancel₀ hG, one_mul]

/-- The finite Selberg upper bound with its full weighted remainder. -/
theorem siftedSum_le_totalMass_div_truncatedSelbergSum_add_errSum (s : BoundingSieve) {z : ℝ} (hz : 1 ≤ z) :
    s.siftedSum ≤ s.totalMass / s.truncatedSelbergSum z +
      s.errSum (lambdaSquared (s.selbergWeights z)) := by
  simpa only [s.mainSum_lambdaSquared_selbergWeights, div_eq_mul_inv] using
    s.siftedSum_le_mainSum_errSum_of_upperMoebius
      (lambdaSquared (s.selbergWeights z)) (upperMoebius_lambdaSquared _ (s.selbergWeights_one hz))

end BoundingSieve
