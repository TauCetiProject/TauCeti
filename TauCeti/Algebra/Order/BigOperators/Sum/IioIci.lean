/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Order.Interval.Finset.Basic

/-!
# Splitting finite sums below and from an index

Over a finite locally finite linear order, a product (or sum) over all indices splits at any
index `j` into the part over `k < j` and the part over `j ≤ k`
(`Finset.prod_Iio_mul_prod_Ici`, `Finset.sum_Iio_add_sum_Ici`).

For a unit vector `r`, that is `∑ k, r k ^ 2 = 1`, this identifies the residual
`1 - ∑ k < j, r k ^ 2` with the squared length `∑ k ≥ j, r k ^ 2` of the tail of `r`
(`Finset.one_sub_sum_Iio_sq`). The residual therefore bounds `r i ^ 2` for every `j ≤ i`, and
`r j ^ 2 + r i ^ 2` for every `j < i`; it is positive as soon as some `r i` with `j ≤ i` is
nonzero. These residuals are the denominators of partial correlations read off a triangular
factor with unit-length rows.
-/

public section

namespace Finset

variable {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
  [LocallyFiniteOrderTop ι]

/-- A product over all indices splits into the product below `j` and the product from `j` on. -/
@[to_additive /-- A sum over all indices splits into the sum below `j` and the sum from `j` on. -/]
theorem prod_Iio_mul_prod_Ici {M : Type*} [CommMonoid M] (f : ι → M) (j : ι) :
    (∏ k ∈ Iio j, f k) * ∏ k ∈ Ici j, f k = ∏ k, f k := by
  rw [← prod_filter_mul_prod_filter_not univ (· < j) f, filter_gt_eq_Iio]
  congr 2
  ext
  simp

variable {R : Type*} [CommRing R] {r : ι → R}

/-- For a unit vector `r`, the residual `1 - ∑ k < j, r k ^ 2` is the squared length of the
part of `r` from index `j` on. -/
theorem one_sub_sum_Iio_sq (hr : ∑ k, r k ^ 2 = 1) (j : ι) :
    1 - ∑ k ∈ Iio j, r k ^ 2 = ∑ k ∈ Ici j, r k ^ 2 := by
  rw [← hr, ← sum_Iio_add_sum_Ici _ j, add_sub_cancel_left]

variable [LinearOrder R] [IsStrictOrderedRing R]

/-- For a unit vector `r`, each `r i ^ 2` with `j ≤ i` is bounded by the residual
`1 - ∑ k < j, r k ^ 2`. -/
theorem sq_le_one_sub_sum_Iio_sq (hr : ∑ k, r k ^ 2 = 1) {i j : ι} (hji : j ≤ i) :
    r i ^ 2 ≤ 1 - ∑ k ∈ Iio j, r k ^ 2 := by
  rw [one_sub_sum_Iio_sq hr]
  exact single_le_sum (fun k _ ↦ sq_nonneg (r k)) (mem_Ici.2 hji)

/-- For a unit vector `r` and `j < i`, `r j ^ 2 + r i ^ 2` is bounded by the residual
`1 - ∑ k < j, r k ^ 2`. -/
theorem sq_add_sq_le_one_sub_sum_Iio_sq (hr : ∑ k, r k ^ 2 = 1) {i j : ι} (hji : j < i) :
    r j ^ 2 + r i ^ 2 ≤ 1 - ∑ k ∈ Iio j, r k ^ 2 := by
  rw [one_sub_sum_Iio_sq hr, ← sum_pair (f := fun k ↦ r k ^ 2) hji.ne]
  refine sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ ↦ sq_nonneg (r k)
  exact insert_subset_iff.2 ⟨mem_Ici.2 le_rfl, singleton_subset_iff.2 (mem_Ici.2 hji.le)⟩

/-- For a unit vector `r` with `r i ≠ 0`, the residual `1 - ∑ k < j, r k ^ 2` is positive for
every `j ≤ i`. -/
theorem one_sub_sum_Iio_sq_pos (hr : ∑ k, r k ^ 2 = 1) {i j : ι} (hi : r i ≠ 0)
    (hji : j ≤ i) : 0 < 1 - ∑ k ∈ Iio j, r k ^ 2 :=
  (sq_pos_of_ne_zero hi).trans_le (sq_le_one_sub_sum_Iio_sq hr hji)

end Finset
