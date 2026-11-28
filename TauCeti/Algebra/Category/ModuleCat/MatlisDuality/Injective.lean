/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.Basic
public import Mathlib.Algebra.Category.ModuleCat.Injective

/-!
# Injectivity of Matlis duals

The Matlis dual of a projective right module is an injective left module when the dualizing
coefficients are injective over the base ring.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v w

attribute [local instance] ModuleCat.moduleOfAlgebra ModuleCat.isScalarTower_moduleOfAlgebra

/-- **The Matlis dual of a projective right module is injective.** -/
theorem injective_matlisDualOpObj_of_projective (R : Type*) [CommRing R]
    {A : Type u} [Ring A] [Algebra R A] (E : Type v) [AddCommGroup E] [Module R E]
    [Module.Injective R E] [Small.{v} R] (P : ModuleCat.{max u v w} Aᵐᵒᵖ)
    [Module.Projective Aᵐᵒᵖ P] : Injective (ModuleCat.matlisDualOpObj R E P) := by
  have := Module.injective_object_of_injective_module A (MatlisDual R E P)
  exact Injective.of_iso (ModuleCat.matlisDualOpObjEquiv R E P).toModuleIso.symm this

end TauCeti
