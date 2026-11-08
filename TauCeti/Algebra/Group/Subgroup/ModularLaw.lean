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
`(K ⊓ H) ⊔ N = K ⊓ (H ⊔ N)` does hold for `N ≤ K` as soon as the join `H ⊔ N` is the product
set `H * N`: the identity is then Dedekind's law for products of subgroups (Mathlib's
`Subgroup.inf_mul_assoc`). The join is the product set whenever one of `H`, `N` normalizes the
other (`Subgroup.coe_mul_of_left_le_normalizer_right`,
`Subgroup.coe_mul_of_right_le_normalizer_left`), in particular when `N` is normal
(`Subgroup.mul_normal`).

## Main results

* `Subgroup.inf_sup_assoc_of_le`: `(K ⊓ H) ⊔ N = K ⊓ (H ⊔ N)` for `↑(H ⊔ N) = ↑H * ↑N` and
  `N ≤ K`.
-/

public section

open scoped Pointwise

namespace Subgroup

variable {G : Type*} [Group G]

/-- **Dedekind's modular law**: if the join `H ⊔ N` is the product set `H * N` (for example
when `H` normalizes `N`) and `N ≤ K`, then `(K ⊓ H) ⊔ N = K ⊓ (H ⊔ N)`. -/
@[to_additive /-- **Dedekind's modular law**: if the join `H ⊔ N` is the sum set `H + N` (for
example when `H` normalizes `N`) and `N ≤ K`, then `(K ⊓ H) ⊔ N = K ⊓ (H ⊔ N)`. -/]
theorem inf_sup_assoc_of_le {H K N : Subgroup G}
    (hHN : (↑(H ⊔ N) : Set G) = H * N) (h : N ≤ K) : (K ⊓ H) ⊔ N = K ⊓ (H ⊔ N) := by
  refine le_antisymm (sup_le (inf_le_inf_left _ le_sup_left) (le_inf h le_sup_right)) fun x hx ↦ ?_
  rw [← SetLike.mem_coe, coe_inf, hHN, ← inf_mul_assoc K H N h] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  exact mul_mem_sup hy hz

end Subgroup
