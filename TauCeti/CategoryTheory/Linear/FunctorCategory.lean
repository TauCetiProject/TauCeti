/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Linearity of precomposition and evaluation

For an `R`-linear category `E`, the functor categories `C ⥤ E` are `R`-linear with the pointwise
scalar action of `CategoryTheory.functorCategoryLinear`. Mathlib records that precomposition with a
fixed functor and evaluation at a fixed object are additive; this file records that they are
`R`-linear. Both identities hold componentwise by definition.

These are the instances needed to regard reindexing a functor category along an autoequivalence of
its source, for example a grading shift on `ℤ`-graded modules, as an `R`-linear autoequivalence.
-/

public section

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃ t

variable (R : Type t) [Semiring R] {C : Type u₁} {D : Type u₂} {E : Type u₃} [Category.{v₁} C]
  [Category.{v₂} D] [Category.{v₃} E] [Preadditive E] [CategoryTheory.Linear R E]

/-- Precomposition with a fixed functor is `R`-linear. -/
instance Functor.whiskeringLeft_obj_linear (F : C ⥤ D) :
    ((Functor.whiskeringLeft C D E).obj F).Linear R where
  map_smul _ _ := rfl

/-- Evaluation at a fixed object is `R`-linear. -/
instance evaluation_obj_linear (c : C) : ((evaluation C E).obj c).Linear R where
  map_smul _ _ := rfl

end CategoryTheory
