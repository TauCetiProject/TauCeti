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
If every one of these cutoffs is at most `X`, the whole sum with coefficients between `0` and
`2Λ` is at most `4y log X`, regardless of the outer summation limit. This applies in
particular when `w n` is read at the place reached by the Frobenius of `n`.

## References

* `New.Data.primeSum_mem_Icc` in `New/Reduction/PrimeSums.lean` of `lsernau/grh-lean`
  (commit `72fead1`) gives the bound for the prime sums at infinite places.
-/

public section

open Finset ArithmeticFunction
open scoped Nat

namespace TauCeti

/-- Nonnegative prime weights bounded by twice von Mangoldt give a capped sum in
`[0, 4y log X]` when `X * w n ≥ y` at each summation index. -/
theorem sum_prime_weight_mul_max_mem_Icc {a w : ℕ → ℝ} {N : ℕ} {y X : ℝ}
    (hy : 0 ≤ y) (hX : 1 ≤ X)
    (ha : ∀ n ∈ Ioc 0 N, a n ∈ Set.Icc 0 (2 * Λ n))
    (hw : ∀ n ∈ Ioc 0 N, y ≤ X * w n) :
    (∑ n ∈ Ioc 0 N, a n * max (y / n - w n) 0) ∈ Set.Icc 0 (4 * y * Real.log X) := by
  refine ⟨sum_nonneg fun n hn ↦ mul_nonneg (ha n hn).1 (le_max_right ..), ?_⟩
  have hX₀ : 0 < X := zero_lt_one.trans_le hX
  let S := Ioc 0 N ∩ Ioc 0 ⌊X⌋₊
  have hS₁ : S ⊆ Ioc 0 N := inter_subset_left
  have hS₂ : S ⊆ Ioc 0 ⌊X⌋₊ := inter_subset_right
  have hw₀ (n : ℕ) (hn : n ∈ Ioc 0 N) : 0 ≤ w n :=
    nonneg_of_mul_nonneg_right (hy.trans (hw n hn)) hX₀
  have hsupport (n : ℕ) (hn : n ∈ Ioc 0 N) (hnS : n ∉ S) :
      a n * max (y / n - w n) 0 = 0 := by
    have hXn : X ≤ n := le_of_not_ge fun h ↦ hnS <| mem_inter.mpr
      ⟨hn, mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1, (Nat.le_floor_iff hX₀.le).mpr h⟩⟩
    have hn₀ : (0 : ℝ) < n := hX₀.trans_le hXn
    have hdiv : y / n ≤ w n := (div_le_iff₀ hn₀).2 <| calc
      y ≤ X * w n := hw n hn
      _ ≤ n * w n := mul_le_mul_of_nonneg_right hXn (hw₀ n hn)
      _ = w n * n := mul_comm ..
    rw [max_eq_right (sub_nonpos.mpr hdiv), mul_zero]
  rw [← sum_subset hS₁ hsupport]
  calc
    _ ≤ ∑ n ∈ S, 2 * y * (Λ n / n) := by
      refine sum_le_sum fun n hn ↦ ?_
      have hnN := hS₁ hn
      have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      calc
        _ ≤ (2 * Λ n) * (y / n) := by
          apply mul_le_mul (ha n hnN).2
          · exact max_le (sub_le_self _ (hw₀ n hnN)) (div_nonneg hy hn₀)
          · exact le_max_right ..
          · positivity
        _ = _ := by ring
    _ ≤ ∑ n ∈ Ioc 0 ⌊X⌋₊, 2 * y * (Λ n / n) :=
      sum_le_sum_of_subset_of_nonneg hS₂ fun _ _ _ ↦ by positivity
    _ = 2 * y * ∑ n ∈ Ioc 0 ⌊X⌋₊, Λ n / n := by rw [mul_sum]
    _ ≤ 4 * y * Real.log X := by
      calc
        _ ≤ 2 * y * (2 * Real.log X) :=
          mul_le_mul_of_nonneg_left (Chebyshev.sum_vonMangoldt_div_le_two_mul_log hX)
            (by positivity)
        _ = _ := by ring

end TauCeti
