/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SemidirectProduct

/-!
# The semidirect product of a subgroup with a subgroup that normalizes it

Let `H` and `K` be subgroups of a group `G` with `K ≤ Subgroup.normalizer H`. Multiplication then
carries the external semidirect product `H ⋊ K` into `G` (`SemidirectProduct.monoidHomSubgroup`),
and its image is the join `H ⊔ K`. The corresponding elementwise normal form of `H ⊔ K` is
`Subgroup.mem_sup_of_right_le_normalizer_left` in `TauCeti.Algebra.Group.Subgroup.Pointwise`.

## Main results

* `SemidirectProduct.range_monoidHomSubgroup`: the range of the semidirect-product
  multiplication homomorphism is `H ⊔ K`.
-/

public section

variable {G : Type*} [Group G] {H K : Subgroup G}

namespace SemidirectProduct

/-- Multiplication from the semidirect product of a subgroup with a subgroup normalizing it is onto
the join of the two subgroups. -/
@[simp]
theorem range_monoidHomSubgroup (hLE : K ≤ Subgroup.normalizer (H : Set G)) :
    (monoidHomSubgroup hLE).range = H ⊔ K := by
  refine le_antisymm ?_ (sup_le (fun x hx => ⟨inl ⟨x, hx⟩, by simp⟩)
    fun t ht => ⟨inr ⟨t, ht⟩, by simp⟩)
  rintro _ ⟨x, rfl⟩
  rw [monoidHomSubgroup_apply]
  exact Subgroup.mul_mem_sup x.left.2 x.right.2

end SemidirectProduct
