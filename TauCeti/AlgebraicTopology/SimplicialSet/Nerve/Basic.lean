/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# Faces of `3`-simplices of a nerve

A `3`-simplex of the nerve of a category `C` is a sequence of three composable morphisms
`ComposableArrows.mk₃ f g h`. Its faces are the `2`-simplices obtained by dropping a vertex,
whose arrows are composites of consecutive arrows among `f`, `g` and `h`. This extends Mathlib's
description of the faces of `2`-simplices (`CategoryTheory.nerve.δ₀_mk₂_eq`, …).

## Main results

* `CategoryTheory.nerve.δ₀_mk₃_eq`, …, `CategoryTheory.nerve.δ₃_mk₃_eq`: the faces of the
  `3`-simplex of the nerve given by three composable morphisms.
-/

public section

open CategoryTheory Simplicial

universe u v

namespace CategoryTheory.nerve

variable {C : Type u} [Category.{v} C] {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂)
  (h : X₂ ⟶ X₃)

/-! The arrows of each face of `mk₃ f g h` are, by definition of `mk₃`, composites of consecutive
arrows among `f`, `g` and `h`, so the faces are determined by `ComposableArrows.ext₂_of_arrow`. -/

/-- The face of `mk₃ f g h` opposite to the vertex `0`. -/
@[simp]
theorem δ₀_mk₃_eq :
    (nerve C).δ 0 (ComposableArrows.mk₃ f g h) = ComposableArrows.mk₂ g h :=
  ComposableArrows.ext₂_of_arrow rfl rfl

/-- The face of `mk₃ f g h` opposite to the vertex `1`. -/
@[simp]
theorem δ₁_mk₃_eq :
    (nerve C).δ 1 (ComposableArrows.mk₃ f g h) = ComposableArrows.mk₂ (f ≫ g) h :=
  ComposableArrows.ext₂_of_arrow rfl rfl

/-- The face of `mk₃ f g h` opposite to the vertex `2`. -/
@[simp]
theorem δ₂_mk₃_eq :
    (nerve C).δ 2 (ComposableArrows.mk₃ f g h) = ComposableArrows.mk₂ f (g ≫ h) :=
  ComposableArrows.ext₂_of_arrow rfl rfl

/-- The face of `mk₃ f g h` opposite to the vertex `3`. -/
@[simp]
theorem δ₃_mk₃_eq :
    (nerve C).δ 3 (ComposableArrows.mk₃ f g h) = ComposableArrows.mk₂ f g :=
  ComposableArrows.ext₂_of_arrow rfl rfl

end CategoryTheory.nerve
