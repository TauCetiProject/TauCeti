/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import TauCeti.CategoryTheory.Monoidal.Closed.Basic

/-!
# Evaluating curried maps in cartesian closed categories

In a cartesian monoidal category, Mathlib records that evaluation undoes currying after
whiskering (`MonoidalClosed.whiskerLeft_curry_ihom_ev_app`). This file adds:

* `MonoidalClosed.lift_curry_ihom_ev_app`: restates evaluation after currying for maps into the
  product given by `CartesianMonoidalCategory.lift`.
* `cartesianClosedOfEquiv_curry`: expresses currying in `cartesianClosedOfEquiv e` in terms of
  `(CartesianMonoidalCategory.prodComparisonIso e.inverse X Y).inv ≫ e.inverse.map f`, currying in
  the source category, and `e.symm.toAdjunction.homEquiv`.
-/

public section

namespace CategoryTheory

open MonoidalCategory CartesianMonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

/-- Composing with the evaluation map `A ⊗ (A ⟶[C] Z) ⟶ Z` undoes currying. -/
@[reassoc]
lemma MonoidalClosed.lift_curry_ihom_ev_app {A W Y Z : C} [Closed A] (a : W ⟶ A) (b : W ⟶ Y)
    (f : A ⊗ Y ⟶ Z) : lift a (b ≫ curry f) ≫ (ihom.ev A).app Z = lift a b ≫ f := by
  rw [← lift_whiskerLeft, Category.assoc, whiskerLeft_curry_ihom_ev_app]

section OfEquiv

universe v₂ u₂

open MonoidalClosed

variable {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]

/-- Currying in `cartesianClosedOfEquiv e` factors through
`(CartesianMonoidalCategory.prodComparisonIso e.inverse X Y).inv ≫ e.inverse.map f`, currying in
`C`, and `e.symm.toAdjunction.homEquiv`. -/
theorem cartesianClosedOfEquiv_curry [MonoidalClosed C] (e : C ≌ D) {X Y Z : D}
    (f : X ⊗ Y ⟶ Z) :
    letI := cartesianClosedOfEquiv e
    MonoidalClosed.curry f =
      e.symm.toAdjunction.homEquiv Y ((ihom (e.inverse.obj X)).obj (e.inverse.obj Z))
        (MonoidalClosed.curry
          ((prodComparisonIso e.inverse X Y).inv ≫ e.inverse.map f)) := by
  let _ : e.inverse.Monoidal := .ofChosenFiniteProducts _
  simpa [Functor.Monoidal.μ_of_cartesianMonoidalCategory] using
    MonoidalClosed.ofEquiv_curry e.inverse e.symm.toAdjunction f

end OfEquiv

end CategoryTheory
