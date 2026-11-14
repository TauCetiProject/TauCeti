/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Basic

/-!
# Functors from concrete categories

Functorial composition out of a concrete category can be checked pointwise on the underlying
functions, even when the morphisms have different presentations.
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
