/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Chebyshev

/-!
# The square of a sum and its nonzero terms

`sq_sum_le_card_mul_sum_sq` bounds the square of a finite sum by the number of terms times the sum
of the squares. Terms equal to zero contribute to neither sum, so only the nonzero terms need to be
counted: `(∑ i ∈ s, f i) ^ 2 ≤ #{i ∈ s | f i ≠ 0} * ∑ i ∈ s, f i ^ 2`
(`sq_sum_le_card_filter_ne_zero_mul_sum_sq`). This is the form used for sums with bounded overlap,
in which every sum has many terms but at most a fixed number of them are nonzero at each point.
-/

public section

namespace TauCeti

open Finset
open scoped Finset

variable {ι α : Type*} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α]

/-- **Cauchy–Schwarz over the nonzero terms.** The square of a sum is at most the number of its
nonzero terms times the sum of the squares. -/
theorem sq_sum_le_card_filter_ne_zero_mul_sum_sq (s : Finset ι) (f : ι → α) :
    (∑ i ∈ s, f i) ^ 2 ≤ #{i ∈ s | f i ≠ 0} * ∑ i ∈ s, f i ^ 2 := by
  rw [← sum_filter_ne_zero, ← sum_filter_of_ne (p := fun i ↦ f i ≠ 0) (s := s)
    (f := fun i ↦ f i ^ 2) fun i _ hi hf ↦ hi (by rw [hf, zero_pow two_ne_zero])]
  exact sq_sum_le_card_mul_sum_sq

end TauCeti
