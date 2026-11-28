/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import TauCeti.NumberTheory.Chebyshev.LogFactorial

/-!
# Bounds for prime sums with varying cutoffs

A first Riesz weight of the form `(y / n - w n)₊` lets the cutoff depend on the prime power `n`.
If every one of these cutoffs is at most `X`, the increment from `z` to `y` with coefficients
between `0` and `2Λ` is at most `4(y - z) log X`, regardless of the outer summation limit.
Taking `z = 0` bounds the sum itself. This applies in particular when `w n` is read at the
place reached by the Frobenius of `n`.

## References

* `New.Data.primeSum_mem_Icc` in `New/Reduction/PrimeSums.lean` of `lsernau/grh-lean`
  (commit `72fead1`) gives the bound for the prime sums at infinite places.
-/

public section

open Finset ArithmeticFunction
open scoped Nat

namespace TauCeti

/-- For nonnegative coefficients bounded by twice von Mangoldt, increasing the order from
`z` to `y` changes the sum of the ramps by at most `4 (y - z) log X` if all cutoffs are at most
`X` at the larger order. -/
theorem sum_prime_weight_mul_max_sub_mem_Icc {a w : ℕ → ℝ} {N : ℕ} {y z X : ℝ}
    (hzy : z ≤ y) (hX : 1 ≤ X)
    (ha : ∀ n ∈ Ioc 0 N, a n ∈ Set.Icc 0 (2 * Λ n))
    (hw₀ : ∀ n ∈ Ioc 0 N, 0 ≤ w n) (hw : ∀ n ∈ Ioc 0 N, y ≤ X * w n) :
    ((∑ n ∈ Ioc 0 N, a n * max (y / n - w n) 0) -
      ∑ n ∈ Ioc 0 N, a n * max (z / n - w n) 0) ∈ Set.Icc 0 (4 * (y - z) * Real.log X) := by
  rw [← sum_sub_distrib]
  have hinc (n : ℕ) : 0 ≤ max (y / n - w n) 0 - max (z / n - w n) 0 :=
    sub_nonneg.mpr (max_le_max (sub_le_sub_right (div_le_div_of_nonneg_right hzy
      n.cast_nonneg) _) le_rfl)
  simp only [← mul_sub]
  refine ⟨sum_nonneg fun n hn ↦ mul_nonneg (ha n hn).1 (hinc n), ?_⟩
  let S := Ioc 0 N ∩ Ioc 0 ⌊X⌋₊
  have hS₁ : S ⊆ Ioc 0 N := inter_subset_left
  have hS₂ : S ⊆ Ioc 0 ⌊X⌋₊ := inter_subset_right
  rw [← sum_subset hS₁]
  · calc
      _ ≤ ∑ n ∈ S, 2 * (y - z) * (Λ n / n) := by
        refine sum_le_sum fun n hn ↦ ?_
        have hstep : max (y / n - w n) 0 - max (z / n - w n) 0 ≤ (y - z) / n := by
          simpa only [abs_of_nonneg (hinc n), sub_sub_sub_cancel_right, ← sub_div,
            abs_of_nonneg (div_nonneg (sub_nonneg.mpr hzy) n.cast_nonneg)] using
            abs_max_sub_max_le_abs (y / n - w n) (z / n - w n) 0
        calc
          _ ≤ (2 * Λ n) * ((y - z) / n) :=
            mul_le_mul (ha n (hS₁ hn)).2 hstep (hinc n) (by positivity)
          _ = _ := by ring
      _ ≤ ∑ n ∈ Ioc 0 ⌊X⌋₊, 2 * (y - z) * (Λ n / n) :=
        sum_le_sum_of_subset_of_nonneg hS₂ fun _ _ _ ↦ by positivity
      _ = 2 * (y - z) * ∑ n ∈ Ioc 0 ⌊X⌋₊, Λ n / n := by rw [mul_sum]
      _ ≤ 2 * (y - z) * (2 * Real.log X) :=
        mul_le_mul_of_nonneg_left (Chebyshev.sum_vonMangoldt_div_le_two_mul_log hX) (by positivity)
      _ = _ := by ring
  · intro n hn hnS
    have hXn : X ≤ n := le_of_not_ge fun h ↦ hnS <| mem_inter.mpr
      ⟨hn, mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1, (Nat.le_floor_iff (by positivity)).mpr h⟩⟩
    have hn₀ : (0 : ℝ) < n := zero_lt_one.trans_le (hX.trans hXn)
    have hdiv : y / n ≤ w n := (div_le_iff₀ hn₀).2 <| calc
      y ≤ X * w n := hw n hn
      _ ≤ n * w n := mul_le_mul_of_nonneg_right hXn (hw₀ n hn)
      _ = w n * n := mul_comm ..
    have hzero : max (y / n - w n) 0 = 0 := max_eq_right (sub_nonpos.mpr hdiv)
    have hzdiv := (div_le_div_of_nonneg_right hzy n.cast_nonneg).trans hdiv
    rw [hzero, max_eq_right (sub_nonpos.mpr hzdiv), sub_self, mul_zero]

/-- Nonnegative prime weights bounded by twice von Mangoldt give a capped sum in
`[0, 4y log X]` when `X * w n ≥ y` at each summation index. -/
theorem sum_prime_weight_mul_max_mem_Icc {a w : ℕ → ℝ} {N : ℕ} {y X : ℝ}
    (hy : 0 ≤ y) (hX : 1 ≤ X)
    (ha : ∀ n ∈ Ioc 0 N, a n ∈ Set.Icc 0 (2 * Λ n))
    (hw : ∀ n ∈ Ioc 0 N, y ≤ X * w n) :
    (∑ n ∈ Ioc 0 N, a n * max (y / n - w n) 0) ∈ Set.Icc 0 (4 * y * Real.log X) := by
  have hw₀ n hn := nonneg_of_mul_nonneg_right (hy.trans (hw n hn)) (zero_lt_one.trans_le hX)
  have hzero : (∑ n ∈ Ioc 0 N, a n * max (0 / n - w n) 0) = 0 := by
    exact sum_eq_zero fun n hn ↦ by simp [max_eq_right (neg_nonpos.mpr (hw₀ n hn))]
  simpa only [hzero, sub_zero, mul_sub, mul_zero] using
    sum_prime_weight_mul_max_sub_mem_Icc hy hX ha hw₀ hw

end TauCeti
