/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Simplicity of a quotient from a normal-subgroup dichotomy

Simplicity theorems for groups of Lie type, by Tits's criterion for a BN-pair or Iwasawa's
criterion for a group action, first prove a dichotomy in the group itself: every normal subgroup
either lies in a fixed proper normal subgroup `N` or is the whole group. The quotient `G ⧸ N` is
then simple, since a normal subgroup of `G ⧸ N` is the image of its preimage, which is normal in
`G`. Mathlib's `Group.isSimpleGroup_of_isCoatom` asks instead for `N` to be maximal among all
subgroups, which these criteria do not give.

## Main results

* `QuotientGroup.isSimpleGroup_of_forall_normal`: if every normal subgroup lies in the proper
  normal subgroup `N` or is the whole group, then `G ⧸ N` is simple.
-/

public section

open Subgroup

variable {G : Type*} [Group G]

namespace QuotientGroup

/-- **Simplicity of a quotient from a normal-subgroup dichotomy.** If every normal subgroup of `G`
lies in the proper normal subgroup `N` or is the whole group, then `G ⧸ N` is simple. -/
theorem isSimpleGroup_of_forall_normal {N : Subgroup G} [N.Normal] (hN : N ≠ ⊤)
    (h : ∀ (K : Subgroup G) [K.Normal], K ≤ N ∨ K = ⊤) : IsSimpleGroup (G ⧸ N) := by
  have : Nontrivial (G ⧸ N) := QuotientGroup.nontrivial_iff.mpr hN
  have hπ := mk'_surjective N
  refine ⟨fun L hL ↦ ?_⟩
  -- A normal subgroup of the quotient is the image of its preimage, which is normal in `G`.
  have := hL.comap (mk' N)
  rw [← map_comap_eq_self_of_surjective hπ L]
  rcases h (L.comap (mk' N)) with hle | htop
  · exact Or.inl (eq_bot_iff.mpr ((map_mono hle).trans (map_mk'_self N).le))
  · rw [htop, map_top_of_surjective _ hπ]
    exact Or.inr rfl

end QuotientGroup
