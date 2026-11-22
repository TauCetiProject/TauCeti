/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Products and sums over the subtype of a `Finset`

When a function defined on the subtype `s` agrees pointwise with a function on the ambient type,
the product (or sum) over `s` as a subtype equals the product (or sum) over `s`
(`Finset.prod_coe_sort_eq_prod`, `Finset.sum_coe_sort_eq_sum`).
-/

public section

namespace Finset

/-- A product over the subtype `s` equals a product over `s` when the factors agree pointwise. -/
@[to_additive /-- A sum over the subtype `s` equals a sum over `s` when the summands agree
pointwise. -/]
theorem prod_coe_sort_eq_prod {ι M : Type*} [CommMonoid M] (s : Finset ι)
    {f : s → M} (g : ι → M) (h : ∀ (i : ι) (hi : i ∈ s), f ⟨i, hi⟩ = g i) :
    ∏ i : s, f i = ∏ i ∈ s, g i := by
  rw [← prod_coe_sort s g]
  exact prod_congr rfl fun i _ ↦ h i.val i.property

end Finset
