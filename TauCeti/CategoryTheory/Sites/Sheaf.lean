/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Componentwise identities for sheaf isomorphisms

This file provides `@[simp]` and `@[reassoc]` componentwise cancellation lemmas for the underlying
natural transformations of isomorphisms in `Sheaf J A`.
-/

public section

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {A : Type*} [Category* A]

/-- Componentwise left-inverse identity for the underlying natural transformation of a sheaf
isomorphism. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma inv_hom_id_hom_app {F G : Sheaf J A} (e : F ≅ G) (X : Cᵒᵖ) :
    e.inv.hom.app X ≫ e.hom.hom.app X = 𝟙 _ := by
  rw [← NatTrans.comp_app, ObjectProperty.isoInv_hom_id_hom, NatTrans.id_app]

/-- Componentwise right-inverse identity for the underlying natural transformation of a sheaf
isomorphism. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma hom_inv_id_hom_app {F G : Sheaf J A} (e : F ≅ G) (X : Cᵒᵖ) :
    e.hom.hom.app X ≫ e.inv.hom.app X = 𝟙 _ := by
  rw [← NatTrans.comp_app, ObjectProperty.isoHom_inv_id_hom, NatTrans.id_app]

end CategoryTheory.Sheaf
