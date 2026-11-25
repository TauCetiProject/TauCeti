/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# Zero objects in concrete categories

In a concrete category with zero morphisms whose forgetful functor preserves the terminal object,
the zero objects are exactly the objects whose underlying type is a subsingleton.

## Main results

* `CategoryTheory.ConcreteCategory.isZero_iff_subsingleton`: an object of such a concrete category
  is zero exactly when its underlying type has at most one element.
-/

public section

open CategoryTheory CategoryTheory.Limits

universe w

namespace CategoryTheory.ConcreteCategory

variable {C : Type*} [Category C] {FC : C → C → Type*} {CC : C → Type w}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]

/-- In a concrete category with zero morphisms whose forgetful functor preserves the terminal
object, an object is zero exactly when its underlying type has at most one element. -/
theorem isZero_iff_subsingleton [HasZeroMorphisms C]
    [PreservesLimit (Functor.empty.{0} C) (forget C)] (A : C) :
    IsZero A ↔ Subsingleton (ToType A) :=
  ⟨fun hA ↦
      -- the forgetful functor sends the zero object `A` to a terminal type
      have := Types.isTerminalEquivUnique _ (hA.isTerminal.isTerminalObj (forget C))
      ⟨fun a b ↦ Subsingleton.elim a b⟩,
    fun _ ↦ (IsZero.iff_id_eq_zero _).2
      (ConcreteCategory.hom_ext _ _ fun _ ↦ Subsingleton.elim _ _)⟩

end CategoryTheory.ConcreteCategory
