/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Stalk ranks under surjections

A surjection from a finite module cannot increase the rank at any prime.
-/

public section

/-- A surjection from a finite module cannot increase its stalk rank. -/
theorem LinearMap.rankAtStalk_le_of_surjective {R P Q : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] [Module.Finite R P]
    (f : P →ₗ[R] Q) (hf : Function.Surjective f) (p : PrimeSpectrum R) :
    Module.rankAtStalk Q p ≤ Module.rankAtStalk P p := by
  have h := LinearMap.finrank_le_finrank_of_surjective
    (f := f.baseChange (Localization.AtPrime p.asIdeal))
    (LinearMap.baseChange_surjective _ hf)
  simpa only [← Module.rankAtStalk_eq_finrank_tensorProduct] using h

