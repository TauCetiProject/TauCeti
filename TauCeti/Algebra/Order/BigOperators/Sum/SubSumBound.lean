/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Group.Abs

/-!
# Summing the errors of a sequence of increments

If the increments `G (k + 1) - G k` of a sequence `G` are each within `D` of a prescribed value
`g k` for `k < n`, then `G n - G 0` is within `n • D` of the sum `∑ k < n, g k`. The increments
telescope, and the errors add up by the triangle inequality.

## Main results

* `TauCeti.abs_sub_sub_sum_range_le_of_forall_lt`: the bound on `G n - G 0 - ∑ k < n, g k` from
  the bounds on the increments.
-/

public section

namespace TauCeti

/-- If the increments `G (k + 1) - G k` of a sequence are within `D` of `g k` for `k < n`, then
`G n - G 0` is within `n • D` of `∑ k ∈ range n, g k`. -/
theorem abs_sub_sub_sum_range_le_of_forall_lt {α : Type*} [AddCommGroup α] [LinearOrder α]
    [IsOrderedAddMonoid α] {G g : ℕ → α} {D : α} {n : ℕ}
    (hstep : ∀ k < n, |G (k + 1) - G k - g k| ≤ D) :
    |G n - G 0 - ∑ k ∈ Finset.range n, g k| ≤ n • D := by
  have hbound := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk =>
    hstep k (Finset.mem_range.1 hk))
  rwa [Finset.sum_sub_distrib, Finset.sum_range_sub G, Finset.sum_const, Finset.card_range]
    at hbound

end TauCeti
