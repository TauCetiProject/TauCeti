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
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Basic properties of dual numbers

A coordinatewise scalar action on dual numbers forms a scalar tower with multiplication whenever
the action on the coefficients does, and it commutes with multiplication whenever the action on
the coefficients does; the two laws lift separately. When the coordinatewise action is a module
structure over a commutative semiring, together they make multiplication bilinear, which makes
bilinear multiplication and convolution available with that module structure.
The dual numbers are a finite module over their coefficient ring, so dual numbers over an
Artinian ring are also Artinian, and dual numbers over a finite or free module are again finite
or free.
Multiplication by `ε` is exact over any semiring. Over any ring, each element
`1 + inr c` is a unit with inverse `1 - inr c`.
Algebra maps on dual numbers evaluate in terms of their restriction to constants and
their value on `ε`. Over a nontrivial semiring `ε` is a nonzero nilpotent, so the dual numbers
are neither reduced nor a field. The dual numbers are free of rank two on the basis `1, ε`, so
linear maps out of them are determined by their values on `1` and `ε`.
-/

public section

namespace TauCeti

/-- The unit `1 + inr c` in the dual numbers, with inverse `1 - inr c`. -/
def dualNumberUnit {R : Type*} [Ring R] (c : R) : (DualNumber R)ˣ where
  val := 1 + TrivSqZeroExt.inr c
  inv := 1 - TrivSqZeroExt.inr c
  val_inv := by ext <;> simp [TrivSqZeroExt.snd_mul, smul_eq_mul]
  inv_val := by ext <;> simp [TrivSqZeroExt.snd_mul, smul_eq_mul]

/-- The underlying dual number of `dualNumberUnit c` is `1 + inr c`. -/
@[simp]
theorem coe_dualNumberUnit {R : Type*} [Ring R] (c : R) :
    (dualNumberUnit c : DualNumber R) = 1 + TrivSqZeroExt.inr c := (rfl)

/-- The underlying dual number of the inverse of `dualNumberUnit c` is `1 - inr c`. -/
@[simp]
theorem coe_dualNumberUnit_inv {R : Type*} [Ring R] (c : R) :
    (((dualNumberUnit c)⁻¹ : (DualNumber R)ˣ) : DualNumber R) =
      1 - TrivSqZeroExt.inr c := (rfl)

/-- The scalar projection sends `dualNumberUnit c` to the identity unit. -/
@[simp]
theorem map_fstHom_dualNumberUnit {R B : Type*} [CommSemiring R] [Ring B] [Algebra R B]
    (c : B) :
    Units.map (TrivSqZeroExt.fstHom R B B : DualNumber B →* B) (dualNumberUnit c) = 1 := by
  ext
  simp

variable {R B : Type*} [Semiring B] [SMul R B]

/-- Coordinatewise scalar multiplication associates with multiplication of dual numbers
whenever it associates with multiplication of the coefficients. -/
instance dualNumberIsScalarTower [IsScalarTower R B B] :
    IsScalarTower R (DualNumber B) (DualNumber B) :=
  .of_smul_one_mul fun r x ↦ by
    have h : r • (0 : B) = 0 := by rw [← smul_one_mul, mul_zero]
    ext <;> simp [h, smul_one_mul]

/-- Coordinatewise scalar multiplication commutes with left multiplication of dual numbers
whenever it commutes with left multiplication of the coefficients. -/
instance dualNumberSMulCommClass [SMulCommClass R B B] :
    SMulCommClass R (DualNumber B) (DualNumber B) :=
  .of_mul_smul_one fun r x ↦ by
    have h : r • (0 : B) = 0 := by rw [← mul_smul_one, zero_mul]
    ext <;> simp [h, mul_smul_one]

/-- Multiplication by `ε` on the dual numbers is exact. -/
theorem dualNumber_mul_eps_exact {R : Type*} [Semiring R] :
    Function.Exact
      (LinearMap.toSpanSingleton (DualNumber R) (DualNumber R) DualNumber.eps)
      (LinearMap.toSpanSingleton (DualNumber R) (DualNumber R) DualNumber.eps) := by
  intro x
  -- `x * ε = inr x.fst`, so both sides say that `ε` divides `x`.
  have h : x * DualNumber.eps = 0 ↔ x.fst = 0 := by simp [TrivSqZeroExt.ext_iff]
  simp only [LinearMap.toSpanSingleton_apply, smul_eq_mul, Set.mem_range, h,
    DualNumber.fst_eq_zero_iff_eps_dvd, dvd_def]
  exact exists_congr fun y ↦ by rw [(DualNumber.commute_eps_left y).eq, eq_comm]

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

namespace DualNumber

variable {R : Type*} [Semiring R] [Nontrivial R]

/-- Over a nontrivial semiring, `ε` is nonzero. -/
theorem eps_ne_zero : (ε : R[ε]) ≠ 0 := fun h ↦
  one_ne_zero (α := R) (by simpa using congr(TrivSqZeroExt.snd $h))

/-- Over a nontrivial semiring, the dual numbers are not reduced: `ε` is a nonzero nilpotent. -/
theorem not_isReduced : ¬IsReduced R[ε] := fun _ ↦ eps_ne_zero (R := R) isNilpotent_eps.eq_zero

/-- Over a nontrivial semiring, the dual numbers do not form a field. -/
theorem not_isField : ¬IsField R[ε] := fun h ↦ by
  have := h.isDomain
  exact not_isReduced (R := R) inferInstance

end DualNumber

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

/-- Dual numbers over a finite `R`-module form a finite `R`-module. -/
instance dualNumberModuleFinite {R B : Type*} [Semiring R] [AddCommMonoid B] [Module R B]
    [Module.Finite R B] : Module.Finite R (DualNumber B) :=
  inferInstanceAs (Module.Finite R (B × B))

/-- Dual numbers over a free `R`-module form a free `R`-module. -/
instance dualNumberModuleFree {R B : Type*} [Semiring R] [AddCommMonoid B] [Module R B]
    [Module.Free R B] : Module.Free R (DualNumber B) :=
  inferInstanceAs (Module.Free R (B × B))

/-- Dual numbers over an Artinian ring form an Artinian ring. -/
instance dualNumberIsArtinianRing {R : Type*} [Ring R] [IsArtinianRing R] :
    IsArtinianRing (DualNumber R) :=
  .of_finite R (DualNumber R)

end TauCeti
