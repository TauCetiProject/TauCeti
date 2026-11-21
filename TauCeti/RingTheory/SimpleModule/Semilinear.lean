/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Semisimplicity and semilinear maps

Semisimplicity transfers along injective and surjective semilinear maps whose scalar
homomorphism is surjective.
-/

public section

open Submodule LinearMap

variable {R S : Type*} [Ring R] [Ring S]
  {M' : Type*} [AddCommGroup M'] [Module R M']
  {N' : Type*} [AddCommGroup N'] [Module S N']
  {σ : R →+* S} (l : M' →ₛₗ[σ] N')

/-- An injective semilinear map over a surjective ring homomorphism pulls back semisimplicity. -/
theorem LinearMap.isSemisimpleModule_of_injective
    [RingHomSurjective σ] (hl : Function.Injective l) [IsSemisimpleModule S N'] :
    IsSemisimpleModule R M' :=
  (l.rangeRestrict.isSemisimpleModule_iff_of_bijective
    ⟨l.injective_rangeRestrict_iff.2 hl, l.surjective_rangeRestrict⟩).2 inferInstance

/-- A surjective semilinear map over a surjective ring homomorphism preserves semisimplicity. -/
theorem LinearMap.isSemisimpleModule_of_surjective
    [RingHomSurjective σ] (hl : Function.Surjective l) [IsSemisimpleModule R M'] :
    IsSemisimpleModule S N' :=
  have hb : Function.Bijective ((ker l).liftQ l le_rfl) :=
    ⟨ker_eq_bot.1 ((ker l).ker_liftQ_eq_bot' l rfl), .of_comp (g := (ker l).mkQ) hl⟩
  (isSemisimpleModule_iff_of_bijective _ hb).1 inferInstance
