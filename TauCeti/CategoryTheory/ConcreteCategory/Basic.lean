/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.EqToHom

/-!
# Basic lemmas for concrete categories

Elementwise and pointwise properties of morphisms and functors in a concrete category.

## Main results

* `CategoryTheory.Functor.map_comp_eq_of_apply_eq`: functorial composition out of a concrete
  category can be checked pointwise on the underlying functions, even when the morphisms have
  different presentations.
* `TauCeti.eqToHom_apply_heq`: applying the transport morphism `eqToHom h` along an equality
  `h : X = Y` of objects in a concrete category preserves elements up to heterogeneous equality.
-/

public section

open CategoryTheory

universe w v u

namespace CategoryTheory.Functor

variable {C : Type*} [Category C] {FC : C → C → Type*} {CC : C → Type w}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]

/-- A functor from a concrete category maps pointwise-equal composites to equal morphisms. -/
lemma map_comp_eq_of_apply_eq {D : Type u} [Category.{v} D]
    (F : C ⥤ D) {A B E : C}
    (f : A ⟶ B) (g : B ⟶ E) (h : A ⟶ E) (hfg : ∀ x, g (f x) = h x) :
    F.map f ≫ F.map g = F.map h := by
  rw [← F.map_comp]
  exact congrArg F.map (ConcreteCategory.ext_apply fun x ↦ (comp_apply f g x).trans (hfg x))

end CategoryTheory.Functor

namespace TauCeti

/-- Applying the transport morphism `eqToHom h` along an equality `h : X = Y` of objects in a
concrete category preserves elements up to heterogeneous equality. -/
@[simp]
theorem eqToHom_apply_heq {C : Type*} [Category* C] {FC : C → C → Type*} {CC : C → Type*}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    {X Y : C} (h : X = Y) (x : ToType X) :
    (eqToHom h) x ≍ x := by
  subst h
  simp

end TauCeti
