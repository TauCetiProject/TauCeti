/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Bounds on finite sums of squares

`Finset.sum_sq_le_sum_mul` bounds the sum of squares of nonnegative elements by their sum
times a common upper bound, in a partially ordered semiring.
`Finset.sum_range_sq_sub_le` specializes this to successive differences `t (i + 1) - t i`
along a monotone prefix in a partially ordered ring, bounding the sum of their squares by
the endpoint difference `t n - t 0` times a common upper bound.
These bounds convert sums of squared partition increments into mesh bounds by telescoping.
-/

public section

namespace Finset

/-- The sum of squares of nonnegative elements is at most their sum times a common
upper bound. -/
theorem sum_sq_le_sum_mul {ι R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    {s : Finset ι} {f : ι → R} {δ : R}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hδ : ∀ i ∈ s, f i ≤ δ) :
    ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) * δ := by
  rw [sum_mul]
  exact sum_le_sum fun i hi ↦ by
    simpa only [pow_two] using mul_le_mul_of_nonneg_left (hδ i hi) (hf i hi)

/-- Along a monotone prefix, the sum of squared successive differences is at most the
endpoint difference times any common upper bound on the successive differences. -/
theorem sum_range_sq_sub_le {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R]
    (t : ℕ → R) (n : ℕ) (ht : MonotoneOn t (Set.Iic n)) {δ : R}
    (hmesh : ∀ i < n, t (i + 1) - t i ≤ δ) :
    ∑ i ∈ range n, (t (i + 1) - t i) ^ 2 ≤ (t n - t 0) * δ := by
  simpa only [sum_range_sub] using
    sum_sq_le_sum_mul (s := range n) (f := fun i ↦ t (i + 1) - t i)
      (fun i hi ↦ sub_nonneg.mpr
        (ht (by have := mem_range.mp hi; simp only [Set.mem_Iic]; omega)
          (by have := mem_range.mp hi; simp only [Set.mem_Iic]; omega) (Nat.le_succ i)))
      (fun i hi ↦ hmesh i (mem_range.mp hi))

end Finset
