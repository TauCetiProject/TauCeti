/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Evaluating curried maps in cartesian closed categories

In a cartesian monoidal category, Mathlib records that evaluation undoes currying after
whiskering (`MonoidalClosed.whiskerLeft_curry_ihom_ev_app`). This file restates it for maps into
the product given by `CartesianMonoidalCategory.lift`: evaluating the pair of `a : W ⟶ A` and
`b ≫ curry f` gives the pair of `a` and `b` followed by `f`
(`MonoidalClosed.lift_curry_ihom_ev_app`).
-/

public section

namespace CategoryTheory.MonoidalClosed

open MonoidalCategory CartesianMonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- Composing with the evaluation map `A ⊗ (A ⟶[C] Z) ⟶ Z` undoes currying. -/
@[reassoc]
lemma lift_curry_ihom_ev_app {A W Y Z : C} [Closed A] (a : W ⟶ A) (b : W ⟶ Y)
    (f : A ⊗ Y ⟶ Z) : lift a (b ≫ curry f) ≫ (ihom.ev A).app Z = lift a b ≫ f := by
  rw [← lift_whiskerLeft, Category.assoc, whiskerLeft_curry_ihom_ev_app]

end CategoryTheory.MonoidalClosed
