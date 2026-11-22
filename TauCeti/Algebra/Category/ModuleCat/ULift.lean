/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Module.ULift
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.Finiteness.Small

/-!
# Universe lifts of modules

Every module `M` over a ring `R` carries a scalar action of the universe-lifted ring `ULift.{u} R`
through `ULift.down : ULift.{u} R → R` (`ULift.module`). Restricting that `ULift.{u} R`-module
structure back to `R` along `ULift.up : R →+* ULift.{u} R` recovers `M` as an `R`-module
(`ModuleCat.restrictScalarsUliftIso`). Unlike `ModuleCat.restrictScalarsAlgebraMapIso`, this
identification needs no commutativity assumption on `R`.

The universe lift functor `ModuleCat.uliftFunctor` from `ModuleCat.{w} R` to
`ModuleCat.{max w w'} R` reflects projective and injective modules, and preserves them when `R` is
small in the universe `w` (`ModuleCat.projective_uliftFunctor_obj_iff`,
`ModuleCat.injective_uliftFunctor_obj_iff`). When `R` is small in the universe `w`, every finitely
generated module in the larger universe is, up to isomorphism, the lift of one in universe `w`
(`ModuleCat.exists_uliftFunctor_obj_iso`).
-/

public section

noncomputable section

open CategoryTheory

universe u v w w'

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

/-- A module is projective exactly when its universe lift is, when the ring is small in the
universe of the module. -/
theorem projective_uliftFunctor_obj_iff [Small.{w} R] (M : ModuleCat.{w} R) :
    Projective ((uliftFunctor.{w'} R).obj M) ↔ Projective M := by
  refine ⟨fun h ↦ ?_, fun h ↦ (uliftFunctor.{w'} R).projective_obj_of_projective h⟩
  have : Small.{max w w'} R := small_lift R
  have : Module.Projective R (ULift.{w'} M) :=
    ((uliftFunctor.{w'} R).obj M).projective_of_module_projective
  have : Module.Projective R M :=
    Module.Projective.of_equiv (ULift.moduleEquiv : ULift.{w'} M ≃ₗ[R] M)
  exact M.projective_of_categoryTheory_projective

/-- A module is injective exactly when its universe lift is, when the ring is small in the
universe of the module. -/
theorem injective_uliftFunctor_obj_iff [Small.{w} R] (M : ModuleCat.{w} R) :
    Injective ((uliftFunctor.{w'} R).obj M) ↔ Injective M := by
  refine ⟨fun h ↦ ?_, fun h ↦ (uliftFunctor.{w'} R).injective_obj_of_injective h⟩
  have : Small.{max w w'} R := small_lift R
  have : Module.Injective R (ULift.{w'} M) := (Module.injective_iff_injective_object R _).mpr h
  have : Module.Injective R M :=
    ((Module.Baer.of_injective this).of_equiv ULift.moduleEquiv).injective
  exact (Module.injective_iff_injective_object R M).mp this

/-- When the ring is small in the universe `w`, a finitely generated module in a larger universe
is the universe lift of a finitely generated module in universe `w`. -/
theorem exists_uliftFunctor_obj_iso [Small.{w} R] (X : ModuleCat.{max w w'} R)
    [Module.Finite R X] :
    ∃ X₀ : ModuleCat.{w} R, Module.Finite R X₀ ∧ Nonempty ((uliftFunctor.{w'} R).obj X₀ ≅ X) := by
  have : Small.{w} X := Module.Finite.small R X
  exact ⟨of R (Shrink.{w} X), Module.Finite.equiv (Shrink.linearEquiv R X).symm,
    ⟨(ULift.moduleEquiv.trans (Shrink.linearEquiv R X)).toModuleIso⟩⟩

end ModuleCat

end
