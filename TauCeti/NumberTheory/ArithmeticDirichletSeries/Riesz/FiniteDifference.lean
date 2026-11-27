/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Finite differences of first Riesz sums

A forward difference recovers the sum of `a(n)/n` up to the original cutoff, with an error
supported only on the integers between the two cutoffs. This separates the removal of Riesz
smoothing from the analytic estimate for the smoothed sum.
-/

public section

open Finset

namespace TauCeti

/-- In the forward difference of a first Riesz sum, the old terms have slopes `a(n)/n`,
while the new terms retain the ramp at the upper cutoff. -/
theorem rieszSum_sub_eq_mul_sum_div_add_sum_Ioc (a : ℕ → ℂ) {z y : ℝ} (hzy : z ≤ y) :
    rieszSum a y - rieszSum a z =
      ((y - z : ℝ) : ℂ) * (∑ n ∈ Icc 1 ⌊z⌋₊, a n / n) +
        ∑ n ∈ Ioc ⌊z⌋₊ ⌊y⌋₊, a n * ((y : ℂ) / n - 1) := by
  have hI (k : ℕ) : Icc 1 k = Ioc 0 k := by
    rw [← Icc_add_one_left_eq_Ioc, zero_add]
  simp only [rieszSum_def, hI]
  rw [← sum_Ioc_consecutive _ (Nat.zero_le ⌊z⌋₊) (Nat.floor_le_floor hzy),
    add_sub_right_comm, ← sum_sub_distrib, mul_sum]
  congr 1
  refine sum_congr rfl fun n _ ↦ ?_
  push_cast
  ring

/-- The error in approximating the first Riesz increment by the old slopes times the cutoff
increment is bounded by the increment times the mass of `‖a(n)‖/n` in the new interval. -/
theorem norm_rieszSum_sub_sub_mul_sum_div_le (a : ℕ → ℂ) {z y : ℝ} (hzy : z ≤ y) :
    ‖rieszSum a y - rieszSum a z - ((y - z : ℝ) : ℂ) * (∑ n ∈ Icc 1 ⌊z⌋₊, a n / n)‖ ≤
      (y - z) * ∑ n ∈ Ioc ⌊z⌋₊ ⌊y⌋₊, ‖a n‖ / n := by
  rw [rieszSum_sub_eq_mul_sum_div_add_sum_Ioc a hzy, add_sub_cancel_left, mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun n hn ↦ ?_)
  obtain ⟨hzn, hny⟩ := mem_Ioc.mp hn
  have hn' : 0 < n := (Nat.zero_le _).trans_lt hzn
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn'
  have h₁ := (Nat.floor_lt' hn'.ne').mp hzn
  have h₂ := (Nat.le_floor_iff' hn'.ne').mp hny
  rw [norm_mul, ← Complex.ofReal_natCast n, ← Complex.ofReal_div, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr ((one_le_div hn₀).mpr h₂))]
  calc
    _ ≤ ‖a n‖ * ((y - z) / n) := by
      gcongr
      rw [sub_div, sub_le_sub_iff_left]
      exact (div_le_one hn₀).mpr h₁.le
    _ = _ := by ring

end TauCeti
