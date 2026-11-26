/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Center.Linear

/-!
# The centre of a preadditive or linear category as a commutative algebra

Mathlib makes the centre `CatCenter C` of a preadditive category `C` a ring and records that it is
commutative (`IsMulCommutative (CatCenter C)`). This file bundles the two into a `CommRing`
instance. For an `R`-linear category `C`, Mathlib's ring morphism `Linear.toCatCenter R C`,
`a ↦ (a • 𝟙 X)_X`, then makes `CatCenter C` an `R`-algebra.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.CatCenter

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The centre of a preadditive category is a commutative ring. -/
instance instCommRing : CommRing (CatCenter C) where
  mul_comm := mul_comm'

variable (R : Type w) [CommRing R] [Linear R C]

/-- The centre of an `R`-linear category is an `R`-algebra: `a : R` acts on every object as the
scalar `a` (Mathlib's `CategoryTheory.Linear.toCatCenter`). -/
instance instAlgebra : Algebra R (CatCenter C) :=
  (Linear.toCatCenter R C).toAlgebra

variable {R}

/-- The image of `a : R` in the centre acts on every object `X` as `a • 𝟙 X`.

This is not a simp lemma: categories of concrete objects state the action on elements instead. -/
lemma algebraMap_app (a : R) (X : C) :
    (algebraMap R (CatCenter C) a).app X = a • 𝟙 X :=
  rfl

end CategoryTheory.CatCenter
