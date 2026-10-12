/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Dedekind's modular law for subgroups

The lattice of subgroups of a group is not modular in general, but the modular identity
`(K ⊓ H) ⊔ N = K ⊓ (H ⊔ N)` does hold for `N ≤ K` as soon as `H` normalizes `N`, because then
the join `H ⊔ N` is the product set `H * N` and the identity is Dedekind's law for products of
subgroups (Mathlib's `Subgroup.inf_mul_assoc`). This is the form in which a kernel is cut out
by a normal subgroup it contains together with a complementary subgroup.

## Main results

* `Subgroup.inf_sup_assoc_of_le`: `(K ⊓ H) ⊔ N = K ⊓ (H ⊔ N)` for `H ≤ normalizer N` and
  `N ≤ K`.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G]

/-- **Dedekind's modular law**: if `H` normalizes `N` and `N ≤ K`, then
`(K ⊓ H) ⊔ N = K ⊓ (H ⊔ N)`. -/
@[to_additive /-- **Dedekind's modular law**: if `H` normalizes `N` and `N ≤ K`, then
`(K ⊓ H) ⊔ N = K ⊓ (H ⊔ N)`. -/]
theorem inf_sup_assoc_of_le {H K N : Subgroup G} (hHN : H ≤ normalizer (N : Set G)) (h : N ≤ K) :
    (K ⊓ H) ⊔ N = K ⊓ (H ⊔ N) := by
  apply SetLike.coe_injective
  rw [coe_mul_of_left_le_normalizer_right _ _ (inf_le_right.trans hHN), inf_mul_assoc K H N h,
    coe_inf, coe_mul_of_left_le_normalizer_right _ _ hHN]

end Subgroup
