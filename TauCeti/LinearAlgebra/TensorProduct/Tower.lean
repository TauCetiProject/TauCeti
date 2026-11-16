/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar extension along algebra maps

For an algebra map `f : A →ₐ[R] B` and an `R`-module `M`, the induced map
`A ⊗[R] M → B ⊗[R] M` is semilinear over `f`.

For a tower `R → A → B` and an `R`-module `M`, the structure map `A → B` induces a map
`A ⊗[R] M → B ⊗[R] M` in two ways: as the `A`-linear map
`TensorProduct.AlgebraTensorModule.rTensor R M (Algebra.linearMap A B)`, and as the `R`-linear
base change of the `R`-algebra map `IsScalarTower.toAlgHom R A B`. This file records that the two
agree as functions, so the `A`-linearity of the first applies to the second.

For a subring `B` of a commutative ring `R` and an `R`-module `M`, an element of `B` can be moved
across the tensor sign of `R ⊗[B] M`.

## Main results

* `AlgHom.rTensor_toLinearMap_apply_smul`: the scalar-extension comparison induced by an algebra
  map is semilinear over that map.
* `TensorProduct.AlgebraTensorModule.rTensor_linearMap_apply`: the `A`-linear base change of the
  structure map `A → B` is the base change of the `R`-algebra map `A →ₐ[R] B`.
* `TensorProduct.AlgebraTensorModule.lTensor_eq_baseChange`: over the coefficient algebra itself,
  `TensorProduct.AlgebraTensorModule.lTensor` is `LinearMap.baseChange`.

* `TensorProduct.tmul_eq_one_tmul_smul_of_mem`: in `R ⊗[B] M`, for a subring `B` of `R` and
  `r ∈ B`, `r ⊗ m = 1 ⊗ r • m`.
* `Submodule.one_tmul_mem_baseChange_of_smul_mem`: if `a • x ∈ N` and `a` becomes a unit in `A`,
  then `1 ⊗ₜ x` lies in the base change of `N` to `A`.
* `LinearMap.liftBaseChangeSemilinear` and `AddMonoidHom.liftBaseChangeSemilinear`: semilinear
  extensions out of a scalar extension `S ⊗[R] M` along a ring homomorphism `σ : S →+* T`.
-/

public section

open TensorProduct

/-- The comparison `A ⊗[R] M → B ⊗[R] M` of scalar extensions induced by an algebra map `f`
is semilinear over `f`. -/
@[simp]
theorem AlgHom.rTensor_toLinearMap_apply_smul {R A B M : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] [Semiring B] [Algebra R B] [AddCommMonoid M] [Module R M]
    (f : A →ₐ[R] B) (a : A) (z : A ⊗[R] M) :
    LinearMap.rTensor M f.toLinearMap (a • z) =
      f a • LinearMap.rTensor M f.toLinearMap z := by
  induction z using TensorProduct.inductionOn with
  | tmul x m => simp [TensorProduct.smul_tmul', smul_eq_mul, map_mul]
  | add x y hx hy => simp [smul_add, hx, hy]

/-- The `A`-linear base change of the structure map `A → B` is, as a function, the base change
of the `R`-algebra map `A →ₐ[R] B`. -/
@[simp]
theorem TensorProduct.AlgebraTensorModule.rTensor_linearMap_apply {R A B M : Type*}
    [CommSemiring R] [CommSemiring A] [Semiring B] [Algebra R A] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] [AddCommMonoid M] [Module R M] (x : A ⊗[R] M) :
    AlgebraTensorModule.rTensor R M (Algebra.linearMap A B) x =
      (IsScalarTower.toAlgHom R A B).toLinearMap.rTensor M x := by
  rw [AlgebraTensorModule.coe_rTensor]
  exact congrArg (LinearMap.rTensor M · x) (LinearMap.ext fun a ↦ by simp)

/-- Over the coefficient algebra itself, `TensorProduct.AlgebraTensorModule.lTensor` is
`LinearMap.baseChange`: both extend scalars along `A`. -/
theorem TensorProduct.AlgebraTensorModule.lTensor_eq_baseChange {R : Type*} (A : Type*)
    {M N : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    AlgebraTensorModule.lTensor A A f = f.baseChange A :=
  AlgebraTensorModule.ext fun a x => by simp

/-- In `R ⊗[B] M`, for a subring `B` of `R`, an element `r ∈ B` can be moved across the tensor
sign: `r ⊗ m = 1 ⊗ r • m`. -/
theorem TensorProduct.tmul_eq_one_tmul_smul_of_mem {R M : Type*} [CommRing R] [AddCommMonoid M]
    [Module R M] {B : Subring R} {r : R} (hr : r ∈ B) (m : M) :
    r ⊗ₜ[B] m = (1 : R) ⊗ₜ (r • m) := by
  simpa [Subring.smul_def] using smul_tmul (⟨r, hr⟩ : B) (1 : R) m

/-- If `a • x` lies in a submodule `N` and `a` becomes a unit in the algebra `A`, then `1 ⊗ₜ x`
lies in the base change of `N` to `A`. -/
theorem Submodule.one_tmul_mem_baseChange_of_smul_mem {R A M : Type*} [CommSemiring R]
    [CommSemiring A] [Algebra R A] [AddCommMonoid M] [Module R M] (N : Submodule R M) {a : R}
    (ha : IsUnit (algebraMap R A a)) {x : M} (hx : a • x ∈ N) :
    (1 : A) ⊗ₜ x ∈ N.baseChange A := by
  obtain ⟨u, hu⟩ := ha
  have h := (N.baseChange A).smul_mem (↑u⁻¹ : A) (tmul_mem_baseChange_of_mem 1 hx)
  rwa [← smul_tmul, ← Algebra.algebraMap_eq_smul_one, ← hu, smul_tmul', smul_eq_mul,
    Units.inv_mul] at h

/-- Base change preserves left inverses: if `f ∘ₗ g = id`, then `f.baseChange A` is a left
inverse of `g.baseChange A`. -/
theorem LinearMap.baseChange_leftInverse {R A M N : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    {f : N →ₗ[R] M} {g : M →ₗ[R] N} (h : f ∘ₗ g = .id) :
    Function.LeftInverse (f.baseChange A) (g.baseChange A) := fun z ↦ by
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, h, LinearMap.baseChange_id,
    LinearMap.id_apply]

/-- Lift a semilinear map `f : M →ₛₗ[σ.comp (algebraMap R S)] V` along `S ⊗[R] M` to a
`σ`-semilinear map `(S ⊗[R] M) →ₛₗ[σ] V` sending `s ⊗ₜ m` to `σ s • f m`. -/
def LinearMap.liftBaseChangeSemilinear {R S T M V : Type*} [CommSemiring R] [Semiring S]
    [Algebra R S] [Semiring T] {σ : S →+* T} [AddCommMonoid M] [Module R M]
    [AddCommMonoid V] [Module T V] (f : M →ₛₗ[σ.comp (algebraMap R S)] V) :
    (S ⊗[R] M) →ₛₗ[σ] V :=
  let g : (S ⊗[R] M) →+ V :=
    TensorProduct.liftAddHom
      { toFun := fun s : S ↦
          { toFun := fun m : M ↦ σ s • f m
            map_zero' := by simp
            map_add' := fun _ _ ↦ by simp [smul_add] }
        map_zero' := by ext m; simp
        map_add' := fun _ _ ↦ by ext m; simp [add_smul] }
      (fun r s m ↦ by
        simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, Algebra.smul_def, Algebra.commutes,
          map_mul, map_smulₛₗ, RingHom.comp_apply, mul_smul])
  { toFun := g
    map_add' := g.map_add
    map_smul' := fun c z ↦ by
      refine TensorProduct.inductionOn z (fun s m ↦ ?_) (fun x y hx hy ↦ ?_)
      · simp [g, TensorProduct.smul_tmul', mul_smul]
      · simp [smul_add, hx, hy] }

@[simp]
theorem LinearMap.liftBaseChangeSemilinear_tmul {R S T M V : Type*} [CommSemiring R] [Semiring S]
    [Algebra R S] [Semiring T] {σ : S →+* T} [AddCommMonoid M] [Module R M]
    [AddCommMonoid V] [Module T V] (f : M →ₛₗ[σ.comp (algebraMap R S)] V) (s : S) (m : M) :
    f.liftBaseChangeSemilinear (s ⊗ₜ[R] m) = σ s • f m :=
  (rfl)

/-- Lift an additive homomorphism `f : X →+ V` across `S ⊗[ℤ] X` along a ring homomorphism
`σ : S →+* T` into a `T`-module `V`, sending `s ⊗ₜ x` to `σ s • f x`. -/
def AddMonoidHom.liftBaseChangeSemilinear {S T X V : Type*} [Ring S] [Ring T]
    [AddCommGroup X] [AddCommGroup V] [Module T V] (f : X →+ V) (σ : S →+* T) :
    (S ⊗[ℤ] X) →ₛₗ[σ] V :=
  LinearMap.liftBaseChangeSemilinear (R := ℤ) (σ := σ)
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun n x ↦ by
        simp only [eq_intCast, Int.cast_smul_eq_zsmul, map_zsmul] }

@[simp]
theorem AddMonoidHom.liftBaseChangeSemilinear_tmul {S T X V : Type*} [Ring S] [Ring T]
    [AddCommGroup X] [AddCommGroup V] [Module T V] (f : X →+ V) (σ : S →+* T) (s : S) (x : X) :
    f.liftBaseChangeSemilinear σ (s ⊗ₜ[ℤ] x) = σ s • f x :=
  (rfl)
