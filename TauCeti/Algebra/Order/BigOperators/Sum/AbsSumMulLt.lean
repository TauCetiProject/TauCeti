/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Abs

/-!
# Weighted sums of bounded numbers

A weighted sum `∑ i, e i * x i` with total absolute weight `∑ i, |e i| ≤ 1`, of numbers `x i` of
absolute value less than `c`, has absolute value less than `c`
(`TauCeti.abs_sum_mul_lt_of_sum_abs_le_one`).
-/

public section

namespace TauCeti

open Finset

variable {ι R : Type*} [Fintype ι] [Ring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A weighted sum with total absolute weight at most one of numbers of absolute value less than
`c` has absolute value less than `c`. -/
theorem abs_sum_mul_lt_of_sum_abs_le_one {c : R} (hc : 0 < c) (e x : ι → R)
    (he : ∑ i, |e i| ≤ 1) (hx : ∀ i, |x i| < c) : |∑ i, e i * x i| < c := by
  by_cases hzero : ∀ i, e i = 0
  · simpa [hzero] using hc
  · push Not at hzero
    obtain ⟨j, hj⟩ := hzero
    calc
      |∑ i, e i * x i| ≤ ∑ i, |e i| * |x i| := by
        simpa [abs_mul] using abs_sum_le_sum_abs (fun i => e i * x i) (univ : Finset ι)
      _ < ∑ i, |e i| * c :=
        sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hx i).le (abs_nonneg _))
          ⟨j, mem_univ j, mul_lt_mul_of_pos_left (hx j) (abs_pos.mpr hj)⟩
      _ ≤ c := by
        rw [← sum_mul]
        exact mul_le_of_le_one_left hc.le he

end TauCeti
