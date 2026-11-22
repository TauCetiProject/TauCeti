/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# Basic lemmas for concrete categories

Elementwise and pointwise properties of morphisms and functors in a concrete category.

## Main results

* `CategoryTheory.Functor.map_comp_eq_of_apply_eq`: functorial composition out of a concrete
  category can be checked pointwise on the underlying functions, even when the morphisms have
  different presentations.
* `CategoryTheory.ConcreteCategory.isZero_iff_forall_eq_zero`: in a concrete category with zero
  morphisms whose forgetful functor preserves the terminal object, an object whose underlying
  type carries a zero is zero exactly when every element of that type is `0`.
* `TauCeti.eqToHom_apply_heq`: applying the transport morphism `eqToHom h` along an equality
  `h : X = Y` of objects in a concrete category preserves elements up to heterogeneous equality.
-/

public section

open CategoryTheory CategoryTheory.Limits

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

namespace CategoryTheory.ConcreteCategory

variable {C : Type*} [Category C] {FC : C → C → Type*} {CC : C → Type w}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]

/-- In a concrete category with zero morphisms whose forgetful functor preserves the terminal
object, an object whose underlying type carries a zero is zero exactly when that type has no
element other than `0`. -/
theorem isZero_iff_forall_eq_zero [∀ A, Zero (CC A)] [HasZeroMorphisms C]
    [PreservesLimit (Functor.empty.{0} C) (forget C)] (A : C) :
    IsZero A ↔ ∀ a : ToType A, a = 0 :=
  ⟨fun hA _ ↦
      -- the forgetful functor sends the zero object `A` to a terminal type
      have := Types.isTerminalEquivUnique _ (hA.isTerminal.isTerminalObj (forget C))
      Subsingleton.elim _ _,
    fun h ↦ (IsZero.iff_id_eq_zero _).2
      (ConcreteCategory.hom_ext _ _ fun _ ↦ (h _).trans (h _).symm)⟩

end CategoryTheory.ConcreteCategory

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
