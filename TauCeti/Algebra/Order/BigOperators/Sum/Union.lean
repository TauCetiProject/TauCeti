/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite sums over a union

A finite sum over `s ∪ t` is at most the sum over `s` plus the sum over `t`, provided the summand
is nonnegative on the overlap `s ∩ t`. This is the order consequence of
`Finset.sum_union_inter`, which computes the defect exactly.

## Main results

* `Finset.sum_union_le`: `∑ i ∈ s ∪ t, f i ≤ ∑ i ∈ s, f i + ∑ i ∈ t, f i` when
  `0 ≤ f i` for every `i ∈ s ∩ t`.
-/

public section

namespace Finset

/-- A sum over `s ∪ t` is at most the sum over `s` plus the sum over `t` when the summand is
nonnegative on `s ∩ t`. -/
theorem sum_union_le {ι M : Type*} [DecidableEq ι] [AddCommMonoid M] [Preorder M]
    [IsOrderedAddMonoid M] {s t : Finset ι} {f : ι → M} (h : ∀ i ∈ s ∩ t, 0 ≤ f i) :
    ∑ i ∈ s ∪ t, f i ≤ ∑ i ∈ s, f i + ∑ i ∈ t, f i := by
  rw [← sum_union_inter]
  exact le_add_of_nonneg_right (sum_nonneg h)

end Finset
