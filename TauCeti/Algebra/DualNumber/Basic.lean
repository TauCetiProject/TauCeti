/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.RingTheory.Artinian.Module

/-!
# Basic properties of dual numbers

The coordinatewise scalar action on dual numbers commutes with multiplication. These
instances make bilinear multiplication and convolution available with that module structure.
Dual numbers over an Artinian ring are also Artinian, using their product module structure, and
they are a finite module over their coefficient ring.
Multiplication by `ε` is exact over a commutative ring.
Algebra maps on dual numbers evaluate in terms of their restriction to constants and
their value on `ε`. The dual numbers are free of rank two on the basis `1, ε`, so linear maps
out of them are determined by their values on `1` and `ε`.
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

namespace AlgHom

open TrivSqZeroExt

/-- An algebra map on dual numbers is determined pointwise by its restriction to constants
and its value on the infinitesimal parameter. -/
theorem apply_dualNumber {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] (χ : DualNumber A →ₐ[R] B) (z : DualNumber A) :
    χ z = χ (inl z.fst) + χ (inl z.snd) * χ DualNumber.eps := by
  have hz := congrArg (fun f : DualNumber A →ₐ[R] B ↦ f z)
    (DualNumber.lift.apply_symm_apply χ)
  simpa only [DualNumber.lift_apply_apply, DualNumber.coe_lift_symm_apply,
    AlgHom.comp_apply, inlAlgHom_apply] using hz.symm

end AlgHom

namespace TauCeti

open TrivSqZeroExt DualNumber

section DualNumberBasis

variable (R : Type*) [Semiring R]

/-- The basis `1, ε` of the dual numbers `R[ε]` as a free `R`-module of rank two. -/
noncomputable def dualNumberBasis : Module.Basis (Fin 2) R (DualNumber R) :=
  Module.Basis.finTwoProd R

/- `DualNumber R` is `R × R` with the product module structure, `1 = (1, 0)` and `ε = (0, 1)`,
so the `Module.Basis.finTwoProd` lemmas below apply definitionally. -/

/-- The first basis vector of `TauCeti.dualNumberBasis` is `1`. -/
@[simp]
theorem dualNumberBasis_zero : dualNumberBasis R 0 = 1 :=
  Module.Basis.finTwoProd_zero R

/-- The second basis vector of `TauCeti.dualNumberBasis` is `ε`. -/
@[simp]
theorem dualNumberBasis_one : dualNumberBasis R 1 = eps :=
  Module.Basis.finTwoProd_one R

/-- The dual numbers are a finite module over their coefficient ring, with basis `1, ε`. -/
instance dualNumberModuleFinite : Module.Finite R (DualNumber R) :=
  Module.Finite.of_basis (dualNumberBasis R)

variable {R}

/-- The coordinate of `x` along `1` is its scalar part. -/
@[simp]
theorem _root_.DualNumber.dualNumberBasis_repr_zero (x : DualNumber R) :
    (dualNumberBasis R).repr x 0 = x.fst :=
  congrFun (Module.Basis.coe_finTwoProd_repr x) 0

/-- The coordinate of `x` along `ε` is its infinitesimal part. -/
@[simp]
theorem _root_.DualNumber.dualNumberBasis_repr_one (x : DualNumber R) :
    (dualNumberBasis R).repr x 1 = x.snd :=
  congrFun (Module.Basis.coe_finTwoProd_repr x) 1

/-- A linear map out of the dual numbers is determined by its values on `1` and `ε`. -/
theorem dualNumber_linearMap_ext {M : Type*} [AddCommMonoid M] [Module R M]
    ⦃f g : DualNumber R →ₗ[R] M⦄ (h1 : f 1 = g 1) (hε : f eps = g eps) : f = g :=
  (dualNumberBasis R).ext fun i => by fin_cases i <;> simpa

end DualNumberBasis

end TauCeti
