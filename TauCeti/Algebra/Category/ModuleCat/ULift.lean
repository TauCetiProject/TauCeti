/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.ULift

/-!
# Restriction of scalars along universe-lifted rings

Every module `M` over a ring `R` carries a scalar action of the universe-lifted ring `ULift.{u} R`
through `ULift.down : ULift.{u} R → R` (`ULift.module`). Restricting that `ULift.{u} R`-module
structure back to `R` along `ULift.up : R →+* ULift.{u} R` recovers `M` as an `R`-module
(`ModuleCat.restrictScalarsUliftIso`). Unlike `ModuleCat.restrictScalarsAlgebraMapIso`, this
identification needs no commutativity assumption on `R`.
-/

public section

noncomputable section

open CategoryTheory

universe u v w

namespace ModuleCat

variable {R : Type v} [Ring R]

/-- Restricting the scalars of an `R`-module `M`, viewed as a `ULift.{u} R`-module via
`ULift.module`, along `ULift.up : R →+* ULift.{u} R` recovers `M` as an `R`-module. -/
def restrictScalarsUliftIso (M : Type w) [AddCommGroup M] [Module R M] :
    (restrictScalars.{w} ((ULift.ringEquiv : ULift.{u} R ≃+* R).symm : R →+* ULift.{u} R)).obj
      (of (ULift.{u} R) M) ≅ of R M :=
  LinearEquiv.toModuleIso
    { __ := AddEquiv.refl M
      map_smul' := fun _ _ ↦ rfl }

/-- Evaluating the forward map of `ModuleCat.restrictScalarsUliftIso` is the identity on `M`. -/
@[simp]
theorem restrictScalarsUliftIso_hom_apply (M : Type w) [AddCommGroup M] [Module R M] (m : M) :
    (restrictScalarsUliftIso.{u} (R := R) M).hom m = m :=
  (rfl)

/-- Evaluating the inverse map of `ModuleCat.restrictScalarsUliftIso` is the identity on `M`. -/
@[simp]
theorem restrictScalarsUliftIso_inv_apply (M : Type w) [AddCommGroup M] [Module R M] (m : M) :
    (restrictScalarsUliftIso.{u} (R := R) M).inv m = m :=
  (rfl)

end ModuleCat

end
