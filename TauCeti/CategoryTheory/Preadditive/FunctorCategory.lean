/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# Additive diagrams in preadditive functor categories

This file provides additivity lemmas for diagrams of additive functors and their colimits in a
functor category `C ⥤ D` between preadditive categories.

## Main results

* `CategoryTheory.Functor.comp_obj_additive`: precomposing a diagram of additive functors
  produces a diagram of additive functors.
* `CategoryTheory.Limits.additive_colimit`: a colimit of additive functors into a preadditive
  category with colimits of that shape is additive.
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.Limits

universe w w' v₁ v₂ u₁ u₂

variable {T : Type w} [Category.{w'} T]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]

/-- Precomposing a diagram of additive functors with `F : T ⥤ A` produces a diagram of additive
functors. -/
lemma _root_.CategoryTheory.Functor.comp_obj_additive {A : Type*} [Category* A]
    (F : T ⥤ A) (G : A ⥤ C ⥤ D) [∀ a, (G.obj a).Additive] (t : T) :
    ((F ⋙ G).obj t).Additive :=
  inferInstanceAs ((G.obj (F.obj t)).Additive)

variable [HasColimitsOfShape T D]

/-- A colimit of additive functors into a category with colimits of shape `T` is additive, since
colimits in `C ⥤ D` are computed pointwise. -/
instance additive_colimit (G : T ⥤ C ⥤ D) [∀ t, (G.obj t).Additive] :
    (colimit G).Additive where
  map_add {X Y f g} := by
    ext t
    simp only [Preadditive.comp_add, ← NatTrans.naturality, (G.obj t).map_add,
      Preadditive.add_comp]

end CategoryTheory.Limits
