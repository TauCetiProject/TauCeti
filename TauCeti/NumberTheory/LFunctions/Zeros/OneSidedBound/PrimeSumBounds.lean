/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Bounds

/-!
# Bounds for prime sums with two place weights

Read the weight of each prime power at its destination place. With weights `b` and `xb / x₁`,
every destination admits the same upper cutoff `x₁` for orders through `xb`. This controls both
the value of the prime sum and its increment when the order increases.

The bound at a single order follows `New.Data.primeSum_mem_Icc` in
`New/Reduction/PrimeSums.lean` of [lsernau/grh-lean](https://github.com/lsernau/grh-lean)
(revision `72fead1`).
-/

public section

open Finset

namespace TauCeti.OneSidedBound

/-- With weight `b` on `t` and `xb / x₁` off `t`, the increment of the smoothed quadratic
prime sum from `z` to `y` is at most `4 (y - z) log x₁` at orders up to `xb`. The estimate is
uniform in the place `i` and the choice of destination `next n i` for each prime power `n`. -/
theorem sum_primeWeight_mul_max_sub_mem_Icc_of_two_cutoffs {ι : Type*} [DecidableEq ι]
    (d : ℕ) [Fact d.Prime] (t : Finset ι) (next : ℕ → ι → ι) (i : ι)
    {x x₁ b : ℕ} {z y : ℝ} (hx : x ≤ x₁) (hdiv : x₁ ∣ x * b)
    (hzy : z ≤ y) (hy : y ≤ ((x * b : ℕ) : ℝ)) :
    let κ (j : ι) := if j ∈ t then b else x * b / x₁
    let S (v : ℝ) := ∑ n ∈ Ioc 0 (x * b), primeWeight d 1 n * (max (v / n - κ (next n i)) 0)
    S y - S z ∈ Set.Icc 0 (4 * (y - z) * Real.log x₁) := by
  intro κ S
  rcases Nat.eq_zero_or_pos x₁ with rfl | hX
  · have hx₀ : x = 0 := Nat.le_zero.mp hx
    simp [S, hx₀]
  have hsmall : x * b / x₁ ≤ b := Nat.div_le_of_le_mul (Nat.mul_le_mul_right b hx)
  have hκ (j : ι) : x * b / x₁ ≤ κ j := by
    by_cases hj : j ∈ t <;> simp [κ, hj, hsmall]
  -- The order is bounded by `x₁` times even the smaller of the two weights.
  simpa only [S] using sum_prime_weight_mul_max_sub_mem_Icc (w := fun n ↦ (κ (next n i) : ℝ))
    hzy (by exact_mod_cast hX)
    (fun n _ ↦ ⟨primeWeight_nonneg d 1 n, primeWeight_le_two_mul_vonMangoldt d 1 n⟩)
    (fun _ _ ↦ Nat.cast_nonneg _) (fun n _ ↦ hy.trans (by
      exact_mod_cast (calc
        x * b = x₁ * (x * b / x₁) := (Nat.mul_div_cancel' hdiv).symm
        _ ≤ x₁ * κ (next n i) := Nat.mul_le_mul_left _ (hκ _))))

/-- At a nonnegative order at most `xb`, the two-cutoff prime sum lies between zero and
`4 y log x₁`. -/
theorem sum_primeWeight_mul_max_mem_Icc_of_two_cutoffs {ι : Type*} [DecidableEq ι]
    (d : ℕ) [Fact d.Prime] (t : Finset ι) (next : ℕ → ι → ι) (i : ι)
    {x x₁ b : ℕ} {y : ℝ} (hx : x ≤ x₁) (hdiv : x₁ ∣ x * b)
    (hy₀ : 0 ≤ y) (hy : y ≤ ((x * b : ℕ) : ℝ)) :
    let κ (j : ι) := if j ∈ t then b else x * b / x₁
    (∑ n ∈ Ioc 0 (x * b), primeWeight d 1 n * max (y / n - κ (next n i)) 0) ∈
      Set.Icc 0 (4 * y * Real.log x₁) := by
  have h (n : ℕ) : max (-(↑(if next n i ∈ t then b else x * b / x₁) : ℝ)) 0 = 0 :=
    max_eq_right (neg_nonpos.mpr (Nat.cast_nonneg _))
  simpa only [zero_div, zero_sub, h, mul_zero, sum_const_zero, sub_zero] using
    sum_primeWeight_mul_max_sub_mem_Icc_of_two_cutoffs d t next i hx hdiv hy₀ hy

end TauCeti.OneSidedBound
