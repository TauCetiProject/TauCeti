/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Functors from and into concrete categories

Functorial composition out of a concrete category can be checked pointwise on the underlying
functions, even when the morphisms have different presentations. Dually, precomposing with an
isomorphism does not change the range of a morphism under a functor into a concrete category
(`CategoryTheory.Functor.range_map_comp_of_isIso`).
-/

public section

open CategoryTheory

universe w v' v u' u

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

/-- Precomposing with an isomorphism does not change the range of the image under a functor into
a concrete category. -/
lemma range_map_comp_of_isIso {E : Type u'} [Category.{v'} E] {D : Type u} [Category.{v} D]
    {FD : D → D → Type*} {CD : D → Type w} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory D FD] (F : E ⥤ D) {X Y Z : E} (e : X ⟶ Y) [IsIso e] (g : Y ⟶ Z) :
    Set.range (F.map (e ≫ g)) = Set.range (F.map g) := by
  rw [F.map_comp, ConcreteCategory.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso (F.map e)).surjective.range_comp _

end CategoryTheory.Functor
