/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Subgroup

/-!
# The permutation subgroup of a faithful group action

These formulas describe how Mathlib's `Equiv.Perm.subgroupOfMulAction` and its inverse
act on points of the underlying faithful group action.
-/

public section

namespace TauCeti

/-- Restricting `MulAction.toPermHom` to its image leaves its action on points unchanged. -/
@[simp]
theorem subgroupOfMulAction_apply (G H : Type*) [Group G] [MulAction G H]
    [FaithfulSMul G H] (g : G) (x : H) :
    ((Equiv.Perm.subgroupOfMulAction G H g : (MulAction.toPermHom G H).range) :
      Equiv.Perm H) x = g • x := rfl

/-- The inverse of Cayley's equivalence acts by the inverse group element. -/
@[simp]
theorem subgroupOfMulAction_inv_apply (G H : Type*) [Group G] [MulAction G H]
    [FaithfulSMul G H] (g : G) (x : H) :
    (((Equiv.Perm.subgroupOfMulAction G H g : (MulAction.toPermHom G H).range) :
      Equiv.Perm H)⁻¹) x = g⁻¹ • x := by
  simpa only [map_inv, Subgroup.coe_inv] using
    subgroupOfMulAction_apply G H g⁻¹ x

end TauCeti
