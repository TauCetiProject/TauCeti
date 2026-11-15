/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Basic properties of quadratic maps

This file records elementary consequences of the quadratic-map axioms.

## Main results

* `QuadraticMap.Anisotropic.comp`: injective pullback preserves anisotropy.
* `QuadraticMap.anisotropic_smul_iff`: scaling by a unit preserves anisotropy.
* `QuadraticMap.nontrivial_of_ne_zero`: the source of a nonzero quadratic map is nontrivial.
-/

public section

namespace QuadraticMap

/-- The source of a nonzero quadratic map is nontrivial. -/
theorem nontrivial_of_ne_zero {S V N : Type*} [CommSemiring S] [AddCommMonoid V]
    [Module S V] [AddCommMonoid N] [Module S N] {Q : QuadraticMap S V N} (hQ : Q ≠ 0) :
    Nontrivial V := by
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hQ
  exact nontrivial_of_ne v 0 (fun h ↦ hv (by simp [h]))

/-- An injective pullback of an anisotropic quadratic map is anisotropic. -/
theorem Anisotropic.comp {R M N P : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P] {Q : QuadraticMap R M N} (hQ : Q.Anisotropic)
    (f : P →ₗ[R] M) (hf : Function.Injective f) : (Q.comp f).Anisotropic := by
  intro x hx
  apply hf
  rw [map_zero]
  exact hQ _ hx

/-- Scaling a quadratic map by a unit does not change its anisotropy. -/
@[simp]
theorem anisotropic_smul_iff {S R M N : Type*} [Monoid S] [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [DistribMulAction S N] [SMulCommClass S R N] {a : S} (ha : IsUnit a)
    (Q : QuadraticMap R M N) :
    (a • Q).Anisotropic ↔ Q.Anisotropic := by
  simp only [Anisotropic, smul_apply, ha.smul_eq_zero]

end QuadraticMap
