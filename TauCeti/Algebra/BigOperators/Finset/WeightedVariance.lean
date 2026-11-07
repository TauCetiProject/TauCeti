/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring

/-!
# The weighted variance decomposition

For weights `w i` summing to `1` and the weighted mean `m = ∑ i, w i * b i`, the weighted mean
square deviation of the points `b i` from any `a` is the squared deviation of `a` from `m` plus
the weighted mean square deviation from `m`:

`∑ i, w i * (a - b i) ^ 2 = (a - m) ^ 2 + ∑ i, w i * (m - b i) ^ 2`.

With nonnegative real weights, the first term is the only one that depends on `a`, so the weighted
mean is the unique minimizer of `a ↦ ∑ i, w i * (a - b i) ^ 2`. Applied pointwise to quantile
functions, the identity describes quadratic Wasserstein barycenters on the real line.

The same weights also express the defect of a quadratic form from the weighted average of its
diagonal through second differences: for any matrix `B`,

`∑ i, ∑ j, w i * w j * (B i i - B i j - B j i + B j j)`
`  = 2 * (∑ i, w i * B i i - ∑ i, ∑ j, w i * w j * B i j)`.

For `B i j = b i * b j` it says that `∑ i, ∑ j, w i * w j * (b i - b j) ^ 2` is twice the weighted
variance `∑ i, w i * b i ^ 2 - m ^ 2`.

## Main results

* `Finset.sum_mul_sub_sq_eq`: the weighted variance decomposition.
* `Finset.sum_sum_mul_sub_sub_add_eq`: the second-difference form of the defect of a quadratic
  form from the average of its diagonal.
-/

public section

namespace Finset

/-- **The weighted variance decomposition.** If the weights `w i` sum to `1` over `s`, then for
every `a` the weighted sum `∑ i ∈ s, w i * (a - b i) ^ 2` equals
`(a - m) ^ 2 + ∑ i ∈ s, w i * (m - b i) ^ 2`, where `m = ∑ i ∈ s, w i * b i` is the weighted mean
of the `b i`. -/
theorem sum_mul_sub_sq_eq {ι R : Type*} [CommRing R] (s : Finset ι) {w : ι → R}
    (hw : ∑ i ∈ s, w i = 1) (a : R) (b : ι → R) :
    ∑ i ∈ s, w i * (a - b i) ^ 2 =
      (a - ∑ i ∈ s, w i * b i) ^ 2 + ∑ i ∈ s, w i * (∑ j ∈ s, w j * b j - b i) ^ 2 := by
  -- Expand both weighted sums into the three sums `∑ w i`, `∑ w i * b i` and `∑ w i * b i ^ 2`.
  have hexpand (c : R) : ∑ i ∈ s, w i * (c - b i) ^ 2 =
      c ^ 2 * ∑ i ∈ s, w i - 2 * c * ∑ i ∈ s, w i * b i + ∑ i ∈ s, w i * b i ^ 2 := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun i _ ↦ by ring
  rw [hexpand, hexpand, hw]
  ring

/-- **Second differences of a weighted quadratic form.** If the weights `w i` sum to `1` over `s`,
then for every matrix `B` the weighted sum of the second differences
`B i i - B i j - B j i + B j j` is twice the defect `∑ i, w i * B i i - ∑ i, ∑ j, w i * w j * B i j`
of the quadratic form from the weighted average of its diagonal. -/
theorem sum_sum_mul_sub_sub_add_eq {ι R : Type*} [CommRing R] (s : Finset ι) {w : ι → R}
    (hw : ∑ i ∈ s, w i = 1) (B : ι → ι → R) :
    ∑ i ∈ s, ∑ j ∈ s, w i * w j * (B i i - B i j - B j i + B j j) =
      2 * (∑ i ∈ s, w i * B i i - ∑ i ∈ s, ∑ j ∈ s, w i * w j * B i j) := by
  -- The two diagonal terms are each the weighted average of the diagonal.
  have h₁ : ∑ i ∈ s, ∑ j ∈ s, w i * w j * B i i = ∑ i ∈ s, w i * B i i :=
    sum_congr rfl fun i _ ↦ by rw [← sum_mul, ← mul_sum, hw, mul_one]
  have h₂ : ∑ i ∈ s, ∑ j ∈ s, w i * w j * B j j = ∑ i ∈ s, w i * B i i := by
    rw [sum_comm]
    exact sum_congr rfl fun j _ ↦ by rw [← sum_mul, ← sum_mul, hw, one_mul]
  -- The two off-diagonal terms agree after exchanging the order of summation.
  have h₃ : ∑ i ∈ s, ∑ j ∈ s, w i * w j * B j i = ∑ i ∈ s, ∑ j ∈ s, w i * w j * B i j := by
    rw [sum_comm]
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring
  simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, h₁, h₂, h₃]
  ring

end Finset
