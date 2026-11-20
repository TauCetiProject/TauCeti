/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.MinMax

/-!
# Positive and negative parts of a balanced sum

When a finite sum in a linearly ordered additive commutative group is zero, its total negative
part equals its total positive part, and twice its total positive part equals the sum of the
absolute values. This expresses the balance of supply and demand without requiring multiplication,
an Archimedean property, or order completeness.
-/

public section

namespace Finset

variable {ι K : Type*} [AddCommGroup K] [LinearOrder K] [IsOrderedAddMonoid K]

/-- A balanced finite family has equal total negative and positive parts. -/
theorem sum_max_neg_eq_sum_max (s : Finset ι) (b : ι → K) (hb : ∑ v ∈ s, b v = 0) :
    ∑ v ∈ s, max (-b v) 0 = ∑ v ∈ s, max (b v) 0 := by
  have h : (∑ v ∈ s, max (b v) 0) - ∑ v ∈ s, max (-b v) 0 = 0 := by
    rw [← sum_sub_distrib]
    simpa only [max_zero_sub_max_neg_zero_eq_self] using hb
  exact (sub_eq_zero.1 h).symm

/-- For a balanced finite family, twice the total positive part equals the sum of the absolute
values. -/
theorem two_nsmul_sum_max_eq_sum_abs (s : Finset ι) (b : ι → K) (hb : ∑ v ∈ s, b v = 0) :
    2 • ∑ v ∈ s, max (b v) 0 = ∑ v ∈ s, |b v| := by
  rw [two_nsmul]
  nth_rw 1 [← sum_max_neg_eq_sum_max s b hb]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun v _ ↦ ?_
  rcases le_total 0 (b v) with hv | hv
  · rw [max_eq_right (neg_nonpos.2 hv), max_eq_left hv, zero_add, abs_of_nonneg hv]
  · rw [max_eq_left (neg_nonneg.2 hv), max_eq_right hv, add_zero, abs_of_nonpos hv]

end Finset
