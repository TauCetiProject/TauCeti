/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Bounds on finite sums of squares, signs of finite products, and sums of simple poles

`Finset.sum_sq_le_sum_mul` bounds the sum of squares of nonnegative elements by their sum
times a common upper bound, in a partially ordered semiring.
`Finset.sum_range_sq_sub_le` specializes this to successive differences `t (i + 1) - t i`
along a monotone prefix in a partially ordered ring, bounding the sum of their squares by
the endpoint difference `t n - t 0` times a common upper bound.
These bounds convert sums of squared partition increments into mesh bounds by telescoping.

`Finset.prod_abs_eq_neg_one_pow_card_filter_neg_mul_prod` computes the sign of a finite product in
a linearly ordered commutative ring: the product of the absolute values is the product times `-1`
to the number of negative factors.

`Finset.sum_div_sub_lt_sum_div_sub` is the strict monotonicity of a sum of simple poles
`∑ i ∈ s, w i / (f i - t)` with nonnegative weights, not all zero, in `t` above every pole.
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

/-- Above every pole, a sum `∑ i ∈ s, w i / (f i - t)` of simple poles with nonnegative weights is
strictly increasing in `t` once some weight is positive. -/
theorem sum_div_sub_lt_sum_div_sub {ι K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {s : Finset ι} {f w : ι → K} (hw : ∀ i ∈ s, 0 ≤ w i) (hw₀ : ∃ i ∈ s, 0 < w i) {a b : K}
    (ha : ∀ i ∈ s, f i < a) (hab : a < b) :
    ∑ i ∈ s, w i / (f i - a) < ∑ i ∈ s, w i / (f i - b) := by
  have key {c : K} (hc : 0 < c) {i : ι} (hi : i ∈ s) : c / (f i - a) < c / (f i - b) := by
    rw [← neg_sub a, ← neg_sub b, div_neg, div_neg, neg_lt_neg_iff]
    exact div_lt_div_of_pos_left hc (sub_pos.2 (ha i hi)) (sub_lt_sub_right hab _)
  obtain ⟨i₀, hi₀, hw₀⟩ := hw₀
  refine sum_lt_sum (fun i hi ↦ ?_) ⟨i₀, hi₀, key hw₀ hi₀⟩
  rcases (hw i hi).lt_or_eq with h | h
  · exact (key h hi).le
  · simp [← h]

end Finset
