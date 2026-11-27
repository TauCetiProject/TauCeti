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
public import Mathlib.RingTheory.DualNumber
import Mathlib.LinearAlgebra.Basis.Prod
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
`1 + inr c` is a unit with inverse `1 - inr c`; these units multiply by adding the
infinitesimal parts, so the `n`th power of `1 + inr c` is `1 + inr (n • c)`, and `1 + inr c`
determines `c`.
Algebra maps on dual numbers evaluate in terms of their restriction to constants and
their value on `ε`. In particular an `R`-algebra endomorphism `f` of `R[ε]` multiplies
`ε`-coefficients by that of `f ε`, and over a reduced semiring `f ε` has zero `R`-component, so
`f ε = (f ε).snd • ε`. Over a nontrivial semiring `ε` is a nonzero nilpotent, so the dual numbers
are neither reduced nor a field; over a field, the maximal ideal `(ε)` squares to zero. The dual
numbers are free of rank two on the basis `1, ε`, so linear maps out of them are determined by
their values on `1` and `ε`.
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
theorem coe_dualNumberUnit_inv {R : Type*} [Ring R] (c : R) :
    (((dualNumberUnit c)⁻¹ : (DualNumber R)ˣ) : DualNumber R) =
      1 - TrivSqZeroExt.inr c := (rfl)

/-- `dualNumberUnit` is injective. -/
theorem dualNumberUnit_injective {R : Type*} [Ring R] :
    Function.Injective (dualNumberUnit : R → (DualNumber R)ˣ) := fun c d h ↦ by
  simpa using congr_arg (fun u : (DualNumber R)ˣ ↦ TrivSqZeroExt.snd (u : DualNumber R)) h

/-- `dualNumberUnit c = dualNumberUnit d` exactly when `c = d`. -/
@[simp]
theorem dualNumberUnit_inj {R : Type*} [Ring R] {c d : R} :
    dualNumberUnit c = dualNumberUnit d ↔ c = d :=
  dualNumberUnit_injective.eq_iff

/-- `dualNumberUnit 0` is the identity unit. -/
@[simp]
theorem dualNumberUnit_zero {R : Type*} [Ring R] : dualNumberUnit (0 : R) = 1 := by
  ext <;> simp

/-- The product of `dualNumberUnit c` and `dualNumberUnit d` is `dualNumberUnit (c + d)`. -/
@[simp]
theorem dualNumberUnit_mul {R : Type*} [Ring R] (c d : R) :
    dualNumberUnit c * dualNumberUnit d = dualNumberUnit (c + d) := by
  ext <;> simp [TrivSqZeroExt.snd_mul, add_comm]

/-- `dualNumberUnit c` is the identity unit exactly when `c = 0`. -/
@[simp]
theorem dualNumberUnit_eq_one_iff {R : Type*} [Ring R] {c : R} : dualNumberUnit c = 1 ↔ c = 0 := by
  rw [← dualNumberUnit_zero, dualNumberUnit_inj]

/-- The inverse of `dualNumberUnit c` is `dualNumberUnit (-c)`. -/
@[simp]
theorem dualNumberUnit_inv {R : Type*} [Ring R] (c : R) :
    (dualNumberUnit c)⁻¹ = dualNumberUnit (-c) := by
  rw [inv_eq_iff_mul_eq_one, dualNumberUnit_mul, add_neg_cancel, dualNumberUnit_zero]

/-- The `n`th power of `dualNumberUnit c` is `dualNumberUnit (n • c)`. -/
@[simp]
theorem dualNumberUnit_pow {R : Type*} [Ring R] (c : R) (n : ℕ) :
    dualNumberUnit c ^ n = dualNumberUnit (n • c) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, dualNumberUnit_mul, succ_nsmul]

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

open TrivSqZeroExt

variable {R : Type*} [CommSemiring R] {F : Type*} [FunLike F R[ε] R[ε]] [AlgHomClass F R R[ε] R[ε]]

/-- The `ε`-coefficient of the image of `x` under an endomorphism `f` of the dual numbers is the
`ε`-coefficient of `x` times that of `f ε`. -/
theorem snd_apply_eq_snd_mul_snd_apply_eps (f : F) (x : R[ε]) : (f x).snd = x.snd * (f ε).snd := by
  have h := congrArg snd ((AlgHom.ofClass f).apply_dualNumber x)
  rw [← algebraMap_eq_inl, AlgHom.commutes, AlgHom.commutes] at h
  simpa [DualNumber.snd_mul, algebraMap_eq_inl] using h

/-- Over a reduced semiring, an endomorphism of the dual numbers sends `ε` to an element with zero
`R`-component. -/
@[simp]
theorem fst_apply_eps_eq_zero [IsReduced R] (f : F) : (f ε).fst = 0 :=
  ((isNilpotent_eps.map f).map (fstHom R R R)).eq_zero

/-- A dual number is a multiple of `ε` exactly when its `R`-component vanishes. Applied to the
image `f ε` of `ε` under an endomorphism `f`, this says that `f ε = (f ε).snd • ε` exactly when
`(f ε).fst = 0`, which always holds over a reduced semiring
(`DualNumber.fst_apply_eps_eq_zero`). -/
theorem eq_snd_smul_eps_iff (x : R[ε]) : x = x.snd • ε ↔ x.fst = 0 := by
  refine ⟨fun h ↦ by rw [h, fst_smul, fst_eps, smul_zero], fun h ↦ ?_⟩
  conv_lhs => rw [← inl_fst_add_inr_snd_eq x]
  rw [h, inl_zero, zero_add, inr_eq_smul_eps]

end DualNumber

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

/-- Over a field `k`, the square of the maximal ideal of the dual numbers `k[ε]` is zero. -/
@[simp]
theorem maximalIdeal_sq_eq_bot {k : Type*} [Field k] :
    IsLocalRing.maximalIdeal (DualNumber k) ^ 2 = ⊥ := by
  rw [maximalIdeal_eq_span_singleton_eps, Ideal.span_singleton_pow, sq, eps_mul_eps,
    Ideal.span_singleton_zero]

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
