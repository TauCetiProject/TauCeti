/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Perm.Subgroup

/-!
# Subgroups of permutation groups

These formulas describe how the permutation associated by Mathlib's
`Equiv.Perm.subgroupOfMulAction`, and its inverse permutation, act on points of a faithful action.

When `ι` has a single element, the transpositions `swap (inl default) x` of `ι ⊕ κ` form a left
transversal of the subgroup `Perm ι × Perm κ`, the range of `Equiv.Perm.sumCongrHom`
(`Equiv.Perm.isComplement_range_swap_inl_sumCongrHom_range`).
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

/-- The transpositions of `inl default` with the elements of `ι ⊕ κ` (including the identity) form
a left transversal of `Perm ι × Perm κ` in `Perm (ι ⊕ κ)` when `ι` has a single element. -/
theorem isComplement_range_swap_inl_sumCongrHom_range (ι κ : Type*) [Unique ι] [DecidableEq ι]
    [DecidableEq κ] :
    Subgroup.IsComplement (Set.range fun x : ι ⊕ κ => swap (.inl default) x)
      (sumCongrHom ι κ).range := by
  -- A permutation fixing `inl default` preserves the right summand, and so lies in the range.
  have hmem (τ : Perm (ι ⊕ κ)) (hτ : τ (.inl default) = .inl default) :
      τ ∈ (sumCongrHom ι κ).range := by
    have h (x : ι ⊕ κ) : (τ x).isRight ↔ x.isRight := by
      rcases x with a | b
      · simp [Unique.eq_default a, hτ]
      · rcases hb : τ (.inr b) with a | _
        · rw [Unique.eq_default a, ← hτ] at hb
          simpa using τ.injective hb
        · simp
    refine ⟨(1, sumIsRight.permCongr (τ.subtypePerm h)), ?_⟩
    ext (a | b)
    · simp [Unique.eq_default a, hτ]
    · simp [permCongr_apply, subtypePerm_apply]
  rw [Subgroup.isComplement_iff_existsUnique_inv_mul_mem]
  intro g
  refine ⟨⟨swap (.inl default) (g (.inl default)), Set.mem_range_self _⟩, hmem _ (by simp), ?_⟩
  rintro ⟨_, ⟨a, rfl⟩⟩ ⟨⟨p, q⟩, hpq⟩
  have h : swap (.inl default) a (g (.inl default)) = .inl default := by
    simpa [Unique.eq_default (p default)] using congr($hpq (Sum.inl default)).symm
  simp [(swap_apply_eq_iff.mp h).trans (swap_apply_left _ _)]

end Equiv.Perm
