/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.Perm.Finite

/-!
# Subgroups of permutation groups

These formulas describe how the permutation associated by Mathlib's
`Equiv.Perm.subgroupOfMulAction`, and its inverse permutation, act on points of a faithful action.

The transpositions `swap (inl ()) x` of `Unit ⊕ κ` form a left transversal of the subgroup
`Perm Unit × Perm κ`, the range of `Equiv.Perm.sumCongrHom`
(`Equiv.Perm.isComplement_image_swap_inl_sumCongrHom_range`).
-/

public section

namespace TauCeti

/-- Restricting `MulAction.toPermHom` to its image leaves its action on points unchanged. -/
@[simp]
theorem subgroupOfMulAction_apply {G H : Type*} [Group G] [MulAction G H]
    [FaithfulSMul G H] (g : G) (x : H) :
    ((Equiv.Perm.subgroupOfMulAction G H g : (MulAction.toPermHom G H).range) :
      Equiv.Perm H) x = g • x := rfl

/-- The inverse permutation associated to `g` acts by `g⁻¹`. -/
@[simp]
theorem subgroupOfMulAction_inv_apply {G H : Type*} [Group G] [MulAction G H]
    [FaithfulSMul G H] (g : G) (x : H) :
    (((Equiv.Perm.subgroupOfMulAction G H g : (MulAction.toPermHom G H).range) :
      Equiv.Perm H)⁻¹) x = g⁻¹ • x := by
  simpa only [map_inv, Subgroup.coe_inv] using subgroupOfMulAction_apply g⁻¹ x

end TauCeti

namespace Equiv.Perm

/-- The transpositions of `inl ()` with the elements of `Unit ⊕ κ` (including the identity) form a
left transversal of `Perm Unit × Perm κ` in `Perm (Unit ⊕ κ)`. -/
theorem isComplement_image_swap_inl_sumCongrHom_range (κ : Type*) [Fintype κ] [DecidableEq κ] :
    Subgroup.IsComplement
      ((Finset.univ.image fun x : Unit ⊕ κ => swap (.inl ()) x : Finset _) :
        Set (Perm (Unit ⊕ κ))) (sumCongrHom Unit κ).range := by
  rw [Subgroup.isComplement_iff_existsUnique_inv_mul_mem]
  intro g
  refine ⟨⟨swap (.inl ()) (g (.inl ())), by simp⟩, ?_, ?_⟩
  · apply mem_sumCongrHom_range_of_perm_mapsTo_inl
    rintro _ ⟨⟨⟩, rfl⟩
    simp
  · rintro ⟨_, hx⟩ ⟨⟨p, q⟩, hpq⟩
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    have h : swap (.inl ()) a (g (.inl ())) = .inl () := by
      simpa using congr($hpq (Sum.inl ())).symm
    simp [(swap_apply_eq_iff.mp h).trans (swap_apply_left _ _)]

end Equiv.Perm
