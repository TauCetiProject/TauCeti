/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Finite biproducts of sheaves of modules

Sheaves of modules over a sheaf of rings form a preadditive category with finite coproducts, so
they have finite biproducts. Mathlib obtains this from the abelian structure, which requires
`HasSheafify`; this file records it under the weaker assumptions (`HasWeakSheafify` and
`WEqualsLocallyBijective`) used by the monoidal structure on sheaves of modules, so that finite
direct sums `⨁ f` can be formed there.

## Main declaration

* `TauCeti.SheafOfModules.hasFiniteBiproducts`.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe u v₁ u₁

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Sheaves of modules have finite biproducts, since they form a preadditive category with finite
coproducts. -/
instance hasFiniteBiproducts : HasFiniteBiproducts (SheafOfModules.{u} R) :=
  .of_hasFiniteCoproducts

end SheafOfModules

end TauCeti
