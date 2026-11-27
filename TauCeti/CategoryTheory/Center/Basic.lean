/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Center.Basic
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.SingleObj

/-!
# Components of central elements

An element `z` of the centre `CatCenter C` is a natural endomorphism of the identity functor, so
conjugating its component at `X` by an isomorphism `e : X ≅ Y` gives its component at `Y`
(`CategoryTheory.CatCenter.inv_comp_app_comp_hom`). For a thin category `D` and a monoid `G`, an
element of the centre of `D × SingleObj G` is determined by its group components
(`CategoryTheory.CatCenter.ext_prod_singleObj`).
-/

public section

universe v u

namespace CategoryTheory.CatCenter

variable {C : Type u} [Category.{v} C]

/-- Conjugating the component of a central element by an isomorphism gives its component at the
target. -/
lemma inv_comp_app_comp_hom (z : CatCenter C) {X Y : C} (e : X ≅ Y) :
    e.inv ≫ z.app X ≫ e.hom = z.app Y := by
  rw [← z.naturality, e.inv_hom_id_assoc]

/-- A central endomorphism of `D × SingleObj G`, for a thin category `D` (such as `Discrete I` or
`Codiscrete I`), is determined by its group components. -/
theorem ext_prod_singleObj {D : Type*} [Category* D] [Quiver.IsThin D] {G : Type*} [Monoid G]
    {z w : CatCenter (D × SingleObj G)}
    (h : ∀ x : D × SingleObj G, (z.app x).2 = (w.app x).2) : z = w :=
  CatCenter.ext _ _ fun x ↦ Prod.hom_ext (Subsingleton.elim _ _) (h x)

end CategoryTheory.CatCenter
