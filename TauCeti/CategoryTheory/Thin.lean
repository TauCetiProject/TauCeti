/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.InducedCategory

/-!
# Thin categories: induced categories

A category is thin (`Quiver.IsThin`) when there is at most one morphism between any two objects.
Mathlib records that functor categories into a thin category are thin, that the opposite of a thin
category is thin, and that every functor out of a thin category is faithful. This file records one
further closure property: a category induced along a map into a thin category is thin.

The motivating instance is the category of members of a family `B` of opens of a topological
space, `InducedCategory (Opens X) (Subtype.val : B → Opens X)`, which indexes the limits describing
a presheaf adapted to `B`. Thinness makes the functor laws of functors between such index
categories instances of `Subsingleton.elim`, and it makes their faithfulness automatic. It does
not by itself make such a functor full: a preimage must still be constructed, although thinness
then discharges the equation the preimage has to satisfy.

## Main results

* `TauCeti.CategoryTheory.instIsThinInducedCategory`: a category induced along a map into a thin
  category is thin.
-/

public section

namespace TauCeti

universe v₂ u₁ u₂

namespace CategoryTheory

open _root_.CategoryTheory

/-- A category induced along a map into a thin category is thin. -/
instance instIsThinInducedCategory {C : Type u₁} {D : Type u₂} [Category.{v₂} D] [Quiver.IsThin D]
    (F : C → D) : Quiver.IsThin (InducedCategory D F) :=
  fun _ _ ↦ ⟨fun _ _ ↦ InducedCategory.hom_ext (Subsingleton.elim _ _)⟩

end CategoryTheory

end TauCeti

end
