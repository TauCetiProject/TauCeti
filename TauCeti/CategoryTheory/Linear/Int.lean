/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.Basic

/-!
# Uniqueness of the `ℤ`-linear structure of a preadditive category

Every preadditive category is `ℤ`-linear through the integer multiples of morphisms
(`CategoryTheory.Linear.preadditiveIntLinear`). An abelian group carries only one `ℤ`-module
structure (`AddCommMonoid.subsingletonIntModule`), so this is the only `ℤ`-linear structure
(`CategoryTheory.Linear.subsingletonInt`). A category can nevertheless be presented with
`ℤ`-linear structures that are not definitionally equal: for `ModuleCat ℤ`, Mathlib's linear
structure as a category of modules over the commutative ring `ℤ` and the structure of a preadditive
category. Constructions taking the linear structure as an instance argument, such as cohomology
with `ℤ`-module values, can be compared across the two by this uniqueness.
-/

public section

namespace CategoryTheory.Linear

variable (C : Type*) [Category C] [Preadditive C]

/-- **A preadditive category has only one `ℤ`-linear structure**, since the group of morphisms
between two objects has only one `ℤ`-module structure. -/
instance subsingletonInt : Subsingleton (Linear ℤ C) :=
  ⟨fun a b ↦ by
    obtain ⟨_, _, _⟩ := a
    obtain ⟨_, _, _⟩ := b
    congr
    funext X Y
    exact Subsingleton.elim _ _⟩

end CategoryTheory.Linear
