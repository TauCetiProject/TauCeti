/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Blocks
public import TauCeti.GroupTheory.Perm.WreathProduct

/-!
# Imprimitivity gives a wreath product embedding

Let `G` act transitively on `α`, and let `B` be a nonempty block. The translates `g • B` form the
block system `MulAction.orbit G B`, a partition of `α` on which `G` acts. Choosing, for each
translate `C`, an element of `G` carrying `B` onto `C` identifies `α` with the grid
`orbit G B × B`: a point is sent to the translate containing it, together with its position
inside that translate transported back to `B`.

Under this identification every element of `G` permutes the rows `{C} × B` of the grid, so it acts
through the imprimitive action of the wreath product `Sym(B) ≀ Sym(orbit G B)`. This gives a group
homomorphism `G →* WreathProduct (Equiv.Perm B) (orbit G B)` whose top component is the action of
`G` on the block system. It is injective exactly when `G` acts faithfully on `α`, and the elements
it sends into the base group `orbit G B → Equiv.Perm B` are exactly those acting trivially on the
block system. So the kernel of the action on the block system embeds in the base group.

The identification of `α` with the grid depends on the chosen elements of `G`. The lemmas below
describe it only through properties that hold for every such choice.

## Main definitions

* `MulAction.IsBlock.imprimitivityEquiv`: the identification `α ≃ orbit G B × B`.
* `MulAction.IsBlock.toWreathProduct`: the homomorphism
  `G →* WreathProduct (Equiv.Perm B) (orbit G B)`.

## Main results

* `MulAction.IsBlock.imprimitivityEquiv_smul`: the identification is equivariant, from the action
  on `α` to the imprimitive wreath-product action on `orbit G B × B`.
* `MulAction.IsBlock.toWreathProduct_right`: the top component is the action on the block system.
* `MulAction.IsBlock.injective_toWreathProduct_iff`: the homomorphism is injective exactly when
  the action on `α` is faithful.
* `MulAction.IsBlock.comap_toWreathProduct_range_inl`: the preimage of the base group is the
  kernel of the action on the block system.

## References

* J. D. Dixon and B. Mortimer, *Permutation Groups*, Theorem 2.6A.
-/

public section

namespace TauCeti

open MulAction
open scoped Pointwise

variable {G α : Type*} [Group G] [MulAction G α] {B : Set α}

/-- An element of `G` carrying `B` onto the translate `C`. -/
private noncomputable def blockTransversal (C : orbit G B) : G :=
  (mem_orbit_iff.1 C.2).choose

private theorem blockTransversal_smul (C : orbit G B) : blockTransversal C • B = C :=
  (mem_orbit_iff.1 C.2).choose_spec

variable [IsPretransitive G α]

/-- For a transitive action, every point lies in exactly one translate of a nonempty block. -/
theorem _root_.MulAction.IsBlock.existsUnique_mem_orbit (hB : IsBlock G B) (hBne : B.Nonempty)
    (x : α) : ∃! C : orbit G B, x ∈ (C : Set α) := by
  obtain ⟨C, ⟨hC, hxC⟩, huniq⟩ := (hB.isBlockSystem hBne).1.2 x
  exact ⟨⟨C, hC⟩, hxC, fun D hxD ↦ Subtype.ext (huniq D ⟨D.2, hxD⟩)⟩

/-- The translate of the block `B` containing `x`. -/
private noncomputable def blockOf (hB : IsBlock G B) (hBne : B.Nonempty) (x : α) : orbit G B :=
  (hB.existsUnique_mem_orbit hBne x).exists.choose

private theorem mem_blockOf (hB : IsBlock G B) (hBne : B.Nonempty) (x : α) :
    x ∈ (blockOf hB hBne x : Set α) :=
  (hB.existsUnique_mem_orbit hBne x).exists.choose_spec

/-- For a transitive action and a nonempty block `B`, the identification of `α` with the grid
`orbit G B × B`. A point `x` is sent to the translate `C` of `B` containing it, together with the
point of `B` obtained by moving `x` back along a chosen element of `G` carrying `B` onto `C`. -/
noncomputable def _root_.MulAction.IsBlock.imprimitivityEquiv (hB : IsBlock G B)
    (hBne : B.Nonempty) : α ≃ orbit G B × B where
  toFun x :=
    (blockOf hB hBne x, ⟨(blockTransversal (blockOf hB hBne x))⁻¹ • x, by
      rw [← Set.mem_smul_set_iff_inv_smul_mem, blockTransversal_smul]
      exact mem_blockOf hB hBne x⟩)
  invFun y := blockTransversal y.1 • (y.2 : α)
  left_inv x := by simp
  right_inv y := by
    have hmem : blockTransversal y.1 • (y.2 : α) ∈ (y.1 : Set α) := by
      rw [← blockTransversal_smul y.1]
      exact Set.smul_mem_smul_set y.2.2
    have hblock : blockOf hB hBne (blockTransversal y.1 • (y.2 : α)) = y.1 :=
      (hB.existsUnique_mem_orbit hBne _).unique (mem_blockOf hB hBne _) hmem
    refine Prod.ext hblock (Subtype.ext ?_)
    simp only [hblock, inv_smul_smul]

section Grid

variable (hB : IsBlock G B) (hBne : B.Nonempty)

/-- The first coordinate of `hB.imprimitivityEquiv hBne x` is the translate of `B` containing
`x`. -/
@[simp]
theorem _root_.MulAction.IsBlock.imprimitivityEquiv_fst_eq_iff {x : α} {C : orbit G B} :
    (hB.imprimitivityEquiv hBne x).1 = C ↔ x ∈ (C : Set α) :=
  ⟨fun h ↦ h ▸ mem_blockOf hB hBne x,
    fun h ↦ (hB.existsUnique_mem_orbit hBne x).unique (mem_blockOf hB hBne x) h⟩

/-- The point of `α` corresponding to a grid position `(C, b)` lies in the translate `C`. -/
theorem _root_.MulAction.IsBlock.imprimitivityEquiv_symm_apply_mem (y : orbit G B × B) :
    (hB.imprimitivityEquiv hBne).symm y ∈ (y.1 : Set α) := by
  rw [← IsBlock.imprimitivityEquiv_fst_eq_iff hB hBne, Equiv.apply_symm_apply]

/-- Moving a point by `g` moves the translate containing it by `g`. -/
theorem _root_.MulAction.IsBlock.imprimitivityEquiv_smul_fst (g : G) (x : α) :
    (hB.imprimitivityEquiv hBne (g • x)).1 = g • (hB.imprimitivityEquiv hBne x).1 := by
  rw [IsBlock.imprimitivityEquiv_fst_eq_iff, orbit.coe_smul]
  exact Set.smul_mem_smul_set ((IsBlock.imprimitivityEquiv_fst_eq_iff hB hBne).1 rfl)

/-- Transported to the grid, the action of an element of `G` permutes the rows `{C} × B`, so it
lies in the image of the imprimitive wreath-product action. -/
private theorem _root_.MulAction.IsBlock.permCongrHom_toPerm_mem_range (g : G) :
    (hB.imprimitivityEquiv hBne).permCongrHom (MulAction.toPerm g) ∈
      (WreathProduct.imprimitiveToPerm (Equiv.Perm B) (orbit G B) B).range := by
  refine WreathProduct.mem_range_imprimitiveToPerm_iff.2 ⟨MulAction.toPerm g, fun y ↦ ?_⟩
  simpa using IsBlock.imprimitivityEquiv_smul_fst hB hBne g ((hB.imprimitivityEquiv hBne).symm y)

/-- For a transitive action and a nonempty block `B`, the homomorphism from `G` to the wreath
product `Sym(B) ≀ Sym(orbit G B)` through which `G` acts on the grid
`hB.imprimitivityEquiv hBne : α ≃ orbit G B × B`. -/
noncomputable def _root_.MulAction.IsBlock.toWreathProduct :
    G →* WreathProduct (Equiv.Perm B) (orbit G B) :=
  have : Nonempty B := hBne.to_subtype
  (MonoidHom.ofInjective (WreathProduct.imprimitiveToPerm_injective (Equiv.Perm B)
    (orbit G B) B)).symm.toMonoidHom.comp
    (((hB.imprimitivityEquiv hBne).permCongrHom.toMonoidHom.comp
      (MulAction.toPermHom G α)).codRestrict _ (IsBlock.permCongrHom_toPerm_mem_range hB hBne))

/-- The imprimitive permutation of the grid given by `hB.toWreathProduct hBne g` is the action of
`g` transported along `hB.imprimitivityEquiv hBne`. -/
@[simp]
theorem _root_.MulAction.IsBlock.imprimitiveToPerm_toWreathProduct (g : G) :
    WreathProduct.imprimitiveToPerm (Equiv.Perm B) (orbit G B) B (hB.toWreathProduct hBne g) =
      (hB.imprimitivityEquiv hBne).permCongrHom (MulAction.toPerm g) :=
  have : Nonempty B := hBne.to_subtype
  MonoidHom.apply_ofInjective_symm
    (WreathProduct.imprimitiveToPerm_injective (Equiv.Perm B) (orbit G B) B)
    ⟨_, IsBlock.permCongrHom_toPerm_mem_range hB hBne g⟩

/-- The identification `α ≃ orbit G B × B` is equivariant for the action of `G` on `α` and the
imprimitive wreath-product action through `hB.toWreathProduct hBne`. -/
theorem _root_.MulAction.IsBlock.imprimitivityEquiv_smul (g : G) (x : α) :
    hB.imprimitivityEquiv hBne (g • x) =
      hB.toWreathProduct hBne g • hB.imprimitivityEquiv hBne x := by
  have h := DFunLike.congr_fun (IsBlock.imprimitiveToPerm_toWreathProduct hB hBne g)
    (hB.imprimitivityEquiv hBne x)
  rw [WreathProduct.imprimitiveToPerm_apply] at h
  rw [WreathProduct.imprimitive_smul, h]
  simp [Equiv.permCongrHom, Equiv.permCongr_apply]

/-- The top component of `hB.toWreathProduct hBne g` is the action of `g` on the block system. -/
@[simp]
theorem _root_.MulAction.IsBlock.toWreathProduct_right (g : G) :
    (hB.toWreathProduct hBne g).right = MulAction.toPerm g := by
  refine Equiv.ext fun C ↦ ?_
  obtain ⟨b⟩ := hBne.to_subtype
  have h := congrArg Prod.fst
    (IsBlock.imprimitivityEquiv_smul hB hBne g ((hB.imprimitivityEquiv hBne).symm (C, b)))
  rw [IsBlock.imprimitivityEquiv_smul_fst, Equiv.apply_symm_apply,
    WreathProduct.imprimitive_smul] at h
  exact h.symm

/-- The base component of `hB.toWreathProduct hBne g` at the translate `C` moves a grid position
`b` to the position of `g` applied to the point at `(g⁻¹ • C, b)`. -/
theorem _root_.MulAction.IsBlock.toWreathProduct_left_apply (g : G) (C : orbit G B) (b : B) :
    (hB.toWreathProduct hBne g).left C b =
      (hB.imprimitivityEquiv hBne (g • (hB.imprimitivityEquiv hBne).symm (g⁻¹ • C, b))).2 := by
  rw [IsBlock.imprimitivityEquiv_smul, Equiv.apply_symm_apply, WreathProduct.imprimitive_smul,
    IsBlock.toWreathProduct_right]
  simp

/-- The homomorphism `hB.toWreathProduct hBne` is injective exactly when `G` acts faithfully on
`α`. In that case it embeds `G` in `Sym(B) ≀ Sym(orbit G B)`. -/
theorem _root_.MulAction.IsBlock.injective_toWreathProduct_iff :
    Function.Injective (hB.toWreathProduct hBne) ↔ FaithfulSMul G α := by
  refine ⟨fun h ↦ ⟨fun {g₁ g₂} hg ↦ h ?_⟩, fun _ g₁ g₂ hg ↦ ?_⟩
  · have : Nonempty B := hBne.to_subtype
    apply WreathProduct.imprimitiveToPerm_injective (Equiv.Perm B) (orbit G B) B
    have hperm : (MulAction.toPerm g₁ : Equiv.Perm α) = MulAction.toPerm g₂ := Equiv.ext hg
    rw [IsBlock.imprimitiveToPerm_toWreathProduct, IsBlock.imprimitiveToPerm_toWreathProduct,
      hperm]
  · refine eq_of_smul_eq_smul (α := α) fun x ↦ (hB.imprimitivityEquiv hBne).injective ?_
    rw [IsBlock.imprimitivityEquiv_smul, IsBlock.imprimitivityEquiv_smul, hg]

/-- The elements of `G` that `hB.toWreathProduct hBne` sends into the base group
`orbit G B → Equiv.Perm B` are exactly those acting trivially on the block system. -/
theorem _root_.MulAction.IsBlock.comap_toWreathProduct_range_inl :
    (SemidirectProduct.inl.range).comap (hB.toWreathProduct hBne) =
      (MulAction.toPermHom G (orbit G B)).ker := by
  ext g
  simp [SemidirectProduct.range_inl_eq_ker_rightHom]

end Grid

end TauCeti
