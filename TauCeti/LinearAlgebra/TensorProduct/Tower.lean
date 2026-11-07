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
theorem TensorProduct.tmul_eq_one_tmul_smul_of_mem {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {B : Subring R} {r : R} (hr : r ∈ B) (m : M) :
    r ⊗ₜ[B] m = (1 : R) ⊗ₜ (r • m) := by
  simpa [Subring.smul_def] using smul_tmul (⟨r, hr⟩ : B) (1 : R) m
