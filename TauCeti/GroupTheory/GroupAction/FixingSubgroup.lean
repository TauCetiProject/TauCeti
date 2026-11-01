/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Pointwise fixing subgroups

This file records small generic additions to Mathlib's `fixingSubgroup` API, together with their
additive `fixingAddSubgroup` counterparts.
-/

public section

namespace TauCeti

/-- For a faithful action, the subgroup fixing the whole space pointwise is trivial. -/
@[to_additive (attr := simp)
  /-- For a faithful additive action, the additive subgroup fixing the whole space pointwise is
  trivial. -/]
theorem fixingSubgroup_univ {G α : Type*} [Group G] [MulAction G α] [FaithfulSMul G α] :
    fixingSubgroup G (Set.univ : Set α) = ⊥ :=
  (Subgroup.eq_bot_iff_forall _).2 fun _ hg ↦ eq_of_smul_eq_smul fun x ↦ by
    rw [(mem_fixingSubgroup_iff G).1 hg x (Set.mem_univ x), one_smul]

end TauCeti
