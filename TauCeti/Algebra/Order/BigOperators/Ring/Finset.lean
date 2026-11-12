/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Bounds on finite sums of squares

`Finset.sum_sq_le_sum_mul` bounds the sum of squares of nonnegative elements by their sum
times a common upper bound, in a partially ordered semiring.
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

end Finset
