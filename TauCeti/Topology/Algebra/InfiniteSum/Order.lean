/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Order lemmas for infinite sums and products

This file supplements `Mathlib.Topology.Algebra.InfiniteSum.Order` with existence of a factor
above `1` (or a positive summand) when an infinite product exceeds `1` (or an infinite sum is
positive).

## Main results

* `HasProd.exists_one_lt`, `HasSum.exists_pos`: in a linearly ordered commutative monoid with a
  closed downward interval topology and left-monotonic multiplication, an infinite product strictly
  greater than `1` (or positive infinite sum) along a nontrivial summation filter has at least one
  factor greater than `1` (or positive summand).
-/

public section

/-- In a linearly ordered commutative monoid with closed downward rays and left-monotone
multiplication, an infinite product strictly greater than `1` along a nontrivial summation filter
has a factor strictly greater than `1`. -/
@[to_additive /-- In a linearly ordered additive commutative monoid with closed downward rays and
left-monotone addition, a positive infinite sum along a nontrivial summation filter has a positive
summand. -/]
theorem HasProd.exists_one_lt {ι α : Type*} {L : SummationFilter ι} [CommMonoid α] [LinearOrder α]
    [MulLeftMono α] [TopologicalSpace α] [ClosedIicTopology α] [L.NeBot]
    {f : ι → α} {a : α} (hprod : HasProd f a L) (ha : 1 < a) : ∃ i, 1 < f i := by
  by_contra! h
  exact (hasProd_le_of_prod_le hprod fun _ ↦ Finset.prod_le_one fun i _ ↦ h i).not_gt ha
