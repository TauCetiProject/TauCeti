/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# The tensor unit of `ModuleCat R`

The tensor unit `𝟙_ (ModuleCat R)` of the monoidal category of modules over a commutative ring `R`
is `R` itself. This file records the consequences that instance search and `Module.finrank` do
not see through the monoidal structure: the unit is a free, finitely generated `R`-module
(`ModuleCat.free_tensorUnit`, `ModuleCat.finite_tensorUnit`), of rank one when `R` satisfies the
strong rank condition (`ModuleCat.finrank_tensorUnit`).
-/

public section

open CategoryTheory MonoidalCategory

universe u

namespace ModuleCat

variable (R : Type u) [CommRing R]

/-- The tensor unit of `ModuleCat R`, which is `R` itself, is a free `R`-module. -/
instance free_tensorUnit : Module.Free R (𝟙_ (ModuleCat.{u} R)) :=
  inferInstanceAs (Module.Free R R)

/-- The tensor unit of `ModuleCat R`, which is `R` itself, is a finitely generated `R`-module. -/
instance finite_tensorUnit : Module.Finite R (𝟙_ (ModuleCat.{u} R)) :=
  inferInstanceAs (Module.Finite R R)

/-- The tensor unit of `ModuleCat R`, which is `R` itself, has rank one over `R`. -/
@[simp]
theorem finrank_tensorUnit [StrongRankCondition R] : Module.finrank R (𝟙_ (ModuleCat.{u} R)) = 1 :=
  Module.finrank_self R

end ModuleCat
