/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# Representations of subfunctors

This file records the compatibility of a representing equivalence with the underlying functor
when the represented presheaf is a subfunctor.
-/

public section

open CategoryTheory

universe u v w

namespace CategoryTheory.Subfunctor

/-- Mapping in a subfunctor sends an element to the image of its underlying value. -/
@[simp]
theorem toFunctor_map_val {C : Type u} [Category.{v} C] {F : C ⥤ Type w}
    (G : Subfunctor F) {X Y : C} (f : X ⟶ Y) (x : G.toFunctor.obj X) :
    (G.toFunctor.map f x).val = F.map f x.val := rfl

end CategoryTheory.Subfunctor

namespace CategoryTheory.Functor.RepresentableBy

variable {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w} {G : Subfunctor F} {Y : C}

/-- The element classified by a composite in a represented subfunctor is the corresponding
restriction of the underlying element. -/
theorem homEquiv_comp_val (e : G.toFunctor.RepresentableBy Y) {X X' : C}
    (f : X ⟶ X') (g : X' ⟶ Y) :
    (e.homEquiv (f ≫ g)).val = F.map f.op (e.homEquiv g).val := by
  simpa only [Subfunctor.toFunctor_map_val] using congrArg Subtype.val (e.homEquiv_comp f g)

end CategoryTheory.Functor.RepresentableBy
