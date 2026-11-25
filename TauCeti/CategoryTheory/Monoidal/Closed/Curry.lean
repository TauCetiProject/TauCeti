/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Global sections of internal Homs under pre- and postcomposition

In a closed monoidal category, Mathlib identifies morphisms `A ⟶ Z` with global sections
`𝟙_ C ⟶ (A ⟶[C] Z)` of the internal Hom through `MonoidalClosed.curry'`, and records that
postcomposition on internal Homs corresponds to postcomposition of morphisms
(`MonoidalClosed.curry'_ihom_map`). This file adds the contravariant counterpart: precomposition
`MonoidalClosed.pre f` on internal Homs corresponds to precomposition with `f`
(`MonoidalClosed.curry'_pre_app`), and the counterpart for `MonoidalClosed.uncurry'` of the
naturality of uncurrying in the target (`MonoidalClosed.uncurry'_natural_right`).
-/

public section

namespace CategoryTheory.MonoidalClosed

open MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Precomposing the global section `curry' g : 𝟙_ C ⟶ (A ⟶[C] Z)` of `g : A ⟶ Z` with
`f : B ⟶ A` gives the global section of `f ≫ g`. -/
theorem curry'_pre_app {A B Z : C} [Closed A] [Closed B] (f : B ⟶ A) (g : A ⟶ Z) :
    curry' g ≫ (pre f).app Z = curry' (f ≫ g) := by
  rw [curry', curry', curry_pre_app, rightUnitor_naturality_assoc]

/-- Uncurrying a global section `f : 𝟙_ C ⟶ (A ⟶[C] Y)` postcomposed on the internal Hom with
`g : Y ⟶ Z` gives the uncurried morphism `A ⟶ Y` followed by `g`. -/
theorem uncurry'_natural_right {A Y Z : C} [Closed A] (f : 𝟙_ C ⟶ (ihom A).obj Y) (g : Y ⟶ Z) :
    uncurry' (f ≫ (ihom A).map g) = uncurry' f ≫ g := by
  rw [uncurry', uncurry', uncurry_natural_right, Category.assoc]

end CategoryTheory.MonoidalClosed
