/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Center.Basic

/-!
# Components of central elements along isomorphisms

An element `z` of the centre `CatCenter C` is a natural endomorphism of the identity functor, so
conjugating its component at `X` by an isomorphism `e : X ≅ Y` gives its component at `Y`
(`CategoryTheory.CatCenter.inv_comp_app_comp_hom`).
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

end CategoryTheory.CatCenter
