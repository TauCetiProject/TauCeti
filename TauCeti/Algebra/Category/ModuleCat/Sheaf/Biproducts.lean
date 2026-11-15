/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Finite biproducts of sheaves of modules

Sheaves of modules over a sheaf of rings form a preadditive category with finite limits, so
they have finite biproducts. No sheafification hypotheses are needed: finite products of sheaves
of modules are computed sectionwise. These biproducts provide the finite direct sums used to
construct finite free sheaves and their monoidal duality.

## Main declaration

* `TauCeti.SheafOfModules.hasFiniteBiproducts`.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe v u v₁ u₁

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})

/-- Sheaves of modules have finite biproducts, since they form a preadditive category with finite
products. -/
instance hasFiniteBiproducts : HasFiniteBiproducts (SheafOfModules.{v} R) :=
  .of_hasFiniteProducts

end SheafOfModules

end TauCeti
