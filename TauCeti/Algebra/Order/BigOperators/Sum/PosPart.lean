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
part equals its total positive part. This expresses the balance of supply and demand without
requiring multiplication, an Archimedean property, or order completeness.
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

end Finset
