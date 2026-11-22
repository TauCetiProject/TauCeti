/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.EqToHom

/-!
# Basic lemmas for concrete categories

Elementwise and pointwise properties of morphisms and functors in a concrete category.

## Main results

* `CategoryTheory.ConcreteCategory.range_comp_of_isIso`: precomposing with an isomorphism
  in a concrete category does not change the range of a morphism.
* `CategoryTheory.Functor.map_comp_eq_of_apply_eq`: functorial composition out of a concrete
  category can be checked pointwise on the underlying functions, even when the morphisms have
  different presentations.
* `CategoryTheory.Functor.range_map_comp_of_isIso`: precomposing with an isomorphism does not
  change the range of a morphism under a functor into a concrete category.
* `TauCeti.eqToHom_apply_heq`: applying the transport morphism `eqToHom h` along an equality
  `h : X = Y` of objects in a concrete category preserves elements up to heterogeneous equality.
-/

public section

open CategoryTheory

universe w v' v u' u

namespace CategoryTheory.ConcreteCategory

/-- Precomposing with an isomorphism in a concrete category does not change the range of a
morphism. -/
lemma range_comp_of_isIso {D : Type u} [Category.{v} D]
    {FD : D → D → Type*} {CD : D → Type w} [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory D FD] {X Y Z : D} (e : X ⟶ Y) [IsIso e] (g : Y ⟶ Z) :
    Set.range ⇑(e ≫ g) = Set.range ⇑g := by
  rw [ConcreteCategory.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso e).surjective.range_comp _

end CategoryTheory.ConcreteCategory

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
  rw [F.map_comp]
  exact ConcreteCategory.range_comp_of_isIso (F.map e) (F.map g)

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
