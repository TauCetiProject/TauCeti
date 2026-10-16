/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Artinian.Module

/-!
# Module properties of dual numbers

The coordinatewise scalar action on dual numbers commutes with multiplication. These
instances make bilinear multiplication and convolution available with that module structure.
Dual numbers over an Artinian ring are also Artinian, using their product module structure.
Multiplication by `ε` is exact over a commutative ring.
-/

public section

namespace TauCeti

variable {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]

/-- Coordinatewise scalar multiplication associates with multiplication of dual numbers. -/
instance dualNumberIsScalarTower : IsScalarTower R (DualNumber B) (DualNumber B) where
  smul_assoc r x y := by
    ext <;> simp [smul_eq_mul, smul_add]

/-- Coordinatewise scalar multiplication commutes with left multiplication of dual numbers. -/
instance dualNumberSMulCommClass : SMulCommClass R (DualNumber B) (DualNumber B) where
  smul_comm r x y := by
    ext <;> simp [smul_eq_mul, smul_add]

/-- Dual numbers over an Artinian ring form an Artinian ring. -/
instance dualNumberIsArtinianRing {R : Type*} [Ring R] [IsArtinianRing R] :
    IsArtinianRing (DualNumber R) := by
  have : IsScalarTower R (DualNumber R) (DualNumber R) :=
    ⟨fun r x y ↦ by
      simpa only [smul_eq_mul, ← TrivSqZeroExt.inl_mul_eq_smul] using
        mul_assoc (TrivSqZeroExt.inl r) x y⟩
  exact isArtinian_of_tower R (inferInstanceAs (IsArtinian R (R × R)))

/-- Multiplication by `ε` on the dual numbers is exact. -/
theorem dualNumber_mul_eps_exact {R : Type*} [CommRing R] :
    Function.Exact
      (LinearMap.toSpanSingleton (DualNumber R) (DualNumber R) DualNumber.eps)
      (LinearMap.toSpanSingleton (DualNumber R) (DualNumber R) DualNumber.eps) := by
  intro x
  constructor
  · intro hx
    have hx' : x.fst = 0 := by
      have h := congrArg TrivSqZeroExt.snd hx
      simpa [LinearMap.toSpanSingleton_apply] using h
    refine ⟨TrivSqZeroExt.inl x.snd, ?_⟩
    rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x, hx']
    simp [LinearMap.toSpanSingleton_apply, DualNumber.inr_eq_smul_eps,
      ← TrivSqZeroExt.inl_mul_eq_smul]
  · rintro ⟨y, rfl⟩
    simp [LinearMap.toSpanSingleton_apply, smul_eq_mul, mul_assoc]

end TauCeti
