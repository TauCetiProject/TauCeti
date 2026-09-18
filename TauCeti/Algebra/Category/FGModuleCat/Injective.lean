/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Injective

/-!
# Injective finitely generated modules

Over a noetherian ring, a finitely generated module that is injective as a module is an injective
object of `FGModuleCat R`. The noetherian hypothesis ensures that the inclusion of `FGModuleCat R`
into `ModuleCat R` preserves monomorphisms.

## Main results

* `FGModuleCat.injective_of_moduleInjective`: over a noetherian ring, an injective module that is
  finitely generated is an injective object of `FGModuleCat R`.
-/

public section

namespace TauCeti

open CategoryTheory

universe u

variable {R : Type u} [Ring R] [IsNoetherianRing R]

/-- Over a noetherian ring, a finitely generated injective module is an injective object of
`FGModuleCat R`. -/
theorem _root_.FGModuleCat.injective_of_moduleInjective (X : FGModuleCat.{u} R)
    [Module.Injective R X] : Injective X :=
  (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).injective_of_map_injective
    ((Module.injective_iff_injective_object R X).mp inferInstance)

end TauCeti
