/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.Algebra.Group.Subgroup.Actions

/-!
# Pointwise fixing subgroups and fixed points

This file records small generic additions to Mathlib's `fixingSubgroup` API, together with their
additive `fixingAddSubgroup` counterparts: for a faithful action the subgroup fixing the whole
space pointwise is trivial, and dually a nontrivial subgroup has a fixed-point set different from
the whole space.
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

/-- For a faithful action, a nontrivial subgroup moves some point: its fixed-point set is not the
whole space. -/
@[to_additive AddAction.fixedPoints_ne_univ_of_ne_bot
  /-- For a faithful additive action, a nontrivial additive subgroup moves some point: its
  fixed-point set is not the whole space. -/]
theorem MulAction.fixedPoints_ne_univ_of_ne_bot {G α : Type*} [Group G] [MulAction G α]
    [FaithfulSMul G α] {N : Subgroup G} (hN : N ≠ ⊥) : MulAction.fixedPoints N α ≠ Set.univ :=
  fun h ↦ hN <| eq_bot_iff.2 fun n hn ↦ fixingSubgroup_univ (G := G) (α := α) ▸
    (mem_fixingSubgroup_iff G).2 fun x _ ↦ (Subgroup.smul_def ⟨n, hn⟩ x).symm.trans
      (MulAction.mem_fixedPoints.1 (Set.eq_univ_iff_forall.1 h x) ⟨n, hn⟩)

end TauCeti
