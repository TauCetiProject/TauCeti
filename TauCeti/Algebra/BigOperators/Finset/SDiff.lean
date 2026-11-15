/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Cancelling equal sub-products over set differences

In a commutative monoid with right cancellation, an equation between two products over finsets,
each possibly with an extra factor in front, may be tested after removing from both index sets
subfinsets whose products agree: by `Finset.prod_sdiff`, each product splits as the product over
the set difference times the product over the removed subfinset, and the two removed products
cancel on the right.

## Main results

* `Finset.mul_prod_eq_mul_prod_iff_sdiff`, `Finset.add_sum_eq_add_sum_iff_sdiff`: removing two
  subfinsets with equal products (sums) from both sides of `a * ∏ = b * ∏` (`a + ∑ = b + ∑`).
* `Finset.prod_eq_prod_iff_sdiff`, `Finset.sum_eq_sum_iff_sdiff`: the case without the extra
  factor (summand).
-/

public section

namespace Finset

variable {α β M : Type*} [DecidableEq α] [DecidableEq β] [CommMonoid M] [IsRightCancelMul M]
  {A S : Finset α} {B T : Finset β} {f : α → M} {g : β → M}

/-- Two products, each with a factor in front, are equal exactly when they stay equal after
removing subfinsets with equal products from both of them. -/
@[to_additive /-- Two sums, each with a summand added in front, are equal exactly when they stay
equal after removing subfinsets with equal sums from both of them. -/]
theorem mul_prod_eq_mul_prod_iff_sdiff {a b : M} (hS : S ⊆ A) (hT : T ⊆ B)
    (h : ∏ x ∈ S, f x = ∏ y ∈ T, g y) :
    a * ∏ x ∈ A, f x = b * ∏ y ∈ B, g y ↔ a * ∏ x ∈ A \ S, f x = b * ∏ y ∈ B \ T, g y := by
  rw [← prod_sdiff hS, ← prod_sdiff hT, h, ← mul_assoc, ← mul_assoc]
  exact mul_left_inj _

/-- Two products are equal exactly when they stay equal after removing subfinsets with equal
products from both of them. -/
@[to_additive /-- Two sums are equal exactly when they stay equal after removing subfinsets with
equal sums from both of them. -/]
theorem prod_eq_prod_iff_sdiff (hS : S ⊆ A) (hT : T ⊆ B) (h : ∏ x ∈ S, f x = ∏ y ∈ T, g y) :
    ∏ x ∈ A, f x = ∏ y ∈ B, g y ↔ ∏ x ∈ A \ S, f x = ∏ y ∈ B \ T, g y := by
  simpa only [one_mul] using mul_prod_eq_mul_prod_iff_sdiff (a := 1) (b := 1) hS hT h

end Finset
