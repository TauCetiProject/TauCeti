/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Bounds on finite sums of squares, multiplicative-growth sums, and signs of finite products

`Finset.sum_sq_le_sum_mul` bounds the sum of squares of nonnegative elements by their sum
times a common upper bound, in a partially ordered semiring.
`Finset.sum_range_sq_sub_le` specializes this to successive differences `t (i + 1) - t i`
along a monotone prefix in a partially ordered ring, bounding the sum of their squares by
the endpoint difference `t n - t 0` times a common upper bound.
These bounds convert sums of squared partition increments into mesh bounds by telescoping.

`Finset.prod_abs_eq_neg_one_pow_card_filter_neg_mul_prod` computes the sign of a finite product in
a linearly ordered commutative ring: the product of the absolute values is the product times `-1`
to the number of negative factors.

`TauCeti.sub_one_mul_sum_Ico_add_le_of_mul_le` derives the finite-horizon telescoping bound
`(c - 1) * ∑ j ∈ Finset.Ico M m, f j + f M ≤ f m` for a sequence `f : ℕ → R` in a preordered,
not necessarily associative ring with monotone addition satisfying `c * f k ≤ f (k + 1)` on
`Finset.Ico M m` (`M ≤ m`).
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

/-- The product of the absolute values of `f` over `s` is the product of `f` over `s` times `-1`
to the number of `i ∈ s` with `f i < 0`. -/
theorem prod_abs_eq_neg_one_pow_card_filter_neg_mul_prod {ι R : Type*} [CommRing R]
    [LinearOrder R] [AddLeftMono R] (s : Finset ι) (f : ι → R) :
    ∏ i ∈ s, |f i| = (-1) ^ #{i ∈ s | f i < 0} * ∏ i ∈ s, f i := by
  have hsign : (-1 : R) ^ #{i ∈ s | f i < 0} = ∏ i ∈ s, if f i < 0 then -1 else 1 := by
    rw [prod_ite, prod_const, prod_const_one, mul_one]
  rw [hsign, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ ↦ ?_
  split_ifs with h
  · rw [abs_of_neg h, neg_one_mul]
  · rw [abs_of_nonneg (not_lt.mp h), one_mul]

end Finset

namespace TauCeti

open Finset

/-- Along a sequence in a preordered, not necessarily associative ring with monotone addition
satisfying `c * f k ≤ f (k + 1)` for `k ∈ Ico M m` (`M ≤ m`),
`(c - 1) * ∑ j ∈ Ico M m, f j + f M ≤ f m`. -/
theorem sub_one_mul_sum_Ico_add_le_of_mul_le {R : Type*} [NonAssocRing R] [Preorder R]
    [IsOrderedAddMonoid R] {f : ℕ → R} {c : R} {M m : ℕ} (hm : M ≤ m)
    (hstep : ∀ k ∈ Ico M m, c * f k ≤ f (k + 1)) :
    (c - 1) * ∑ j ∈ Ico M m, f j + f M ≤ f m := by
  have hle : ∑ k ∈ Ico M m, (c - 1) * f k ≤ ∑ k ∈ Ico M m, (f (k + 1) - f k) :=
    sum_le_sum fun k hk ↦ by
      rw [sub_mul, one_mul]
      exact sub_le_sub_right (hstep k hk) (f k)
  rw [← mul_sum, sum_Ico_sub f hm] at hle
  exact (add_le_add_left hle (f M)).trans_eq (sub_add_cancel (f m) (f M))

end TauCeti
