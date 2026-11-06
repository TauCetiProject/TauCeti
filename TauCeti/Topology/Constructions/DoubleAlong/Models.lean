/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Constructions.DoubleAlong.Basic

/-!
# Empty and universal gluing models for the topological double

Gluing along the empty subset gives the disjoint union, with swap exchanging its summands.
Gluing along the whole space gives the original space, and the swap fixes every point.
-/

public section

open Set

universe u

namespace TauCeti.DoubleAlong

variable (X : Type u) [TopologicalSpace X]

/-- With no gluing the double is the disjoint union of its two copies. -/
noncomputable def emptyHomeomorph : DoubleAlong (∅ : Set X) ≃ₜ X ⊕ X where
  toFun := desc (Y := X ⊕ X) (∅ : Set X) ⟨Sum.inl, continuous_inl⟩ ⟨Sum.inr, continuous_inr⟩
    (fun x ↦ x.property.elim)
  invFun := quotientMap ∅
  left_inv z := induction_on ∅ z (by simp) (by simp)
  right_inv z := by cases z <;> simp
  continuous_toFun := (desc (Y := X ⊕ X) (∅ : Set X) _ _ _).continuous
  continuous_invFun := (quotientMap ∅).continuous

@[simp]
theorem emptyHomeomorph_inl (x : X) : emptyHomeomorph X (inl ∅ x) = Sum.inl x := by
  simp [emptyHomeomorph]

@[simp]
theorem emptyHomeomorph_inr (x : X) : emptyHomeomorph X (inr ∅ x) = Sum.inr x := by
  simp [emptyHomeomorph]

@[simp]
theorem emptyHomeomorph_symm_inl (x : X) : (emptyHomeomorph X).symm (Sum.inl x) = inl ∅ x := by
  simp [emptyHomeomorph]

@[simp]
theorem emptyHomeomorph_symm_inr (x : X) : (emptyHomeomorph X).symm (Sum.inr x) = inr ∅ x := by
  simp [emptyHomeomorph]

/-- In the disjoint-union model the involution is the usual sum swap. -/
@[simp]
theorem emptyHomeomorph_swap (z : DoubleAlong (∅ : Set X)) :
    emptyHomeomorph X (swap ∅ z) = (emptyHomeomorph X z).swap :=
  induction_on ∅ z (by simp) (by simp)

/-- Gluing the whole space identifies the two copies completely; the fold is a homeomorphism. -/
noncomputable def univHomeomorph : DoubleAlong (univ : Set X) ≃ₜ X where
  toFun := fold univ
  invFun := inl univ
  left_inv z := induction_on univ z (by simp) (by simp)
  right_inv := fold_inl univ
  continuous_toFun := (fold univ).continuous
  continuous_invFun := (inl univ).continuous

@[simp]
theorem univHomeomorph_inl (x : X) : univHomeomorph X (inl univ x) = x := by
  simp [univHomeomorph]

@[simp]
theorem univHomeomorph_inr (x : X) : univHomeomorph X (inr univ x) = x := by
  simp [univHomeomorph]

@[simp]
theorem univHomeomorph_symm_apply (x : X) : (univHomeomorph X).symm x = inl univ x := by
  simp [univHomeomorph]

/-- When everything is glued, the swap is the identity. -/
@[simp]
theorem swap_univ (z : DoubleAlong (univ : Set X)) : swap univ z = z :=
  (swap_eq_self_iff _ _).2 (mem_univ _)

end TauCeti.DoubleAlong
