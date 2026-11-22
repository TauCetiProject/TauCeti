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

Base change of submodules and of linear maps along an `R`-algebra `A` interacts well with
elements of `R` that become units in `A`, and with left inverses.

Finally, for an `R`-algebra `A`, not necessarily commutative, and an `A`-module `M`, the action is
an `A`-linear map `A ⊗[R] M → M`. Mathlib's `LinearMap.liftBaseChange` and
`TensorProduct.lidOfCompatibleSMul` give this map only for commutative `A`.

## Main definitions

* `TauCeti.tensorSMul`: the action map `A ⊗[R] M →ₗ[A] M`, `a ⊗ m ↦ a • m`.

## Main results

* `AlgHom.rTensor_toLinearMap_apply_smul`: the scalar-extension comparison induced by an algebra
  map is semilinear over that map.
* `TensorProduct.AlgebraTensorModule.rTensor_linearMap_apply`: the `A`-linear base change of the
  structure map `A → B` is the base change of the `R`-algebra map `A →ₐ[R] B`.
* `TensorProduct.AlgebraTensorModule.lTensor_eq_baseChange`: over the coefficient algebra itself,
  `TensorProduct.AlgebraTensorModule.lTensor` is `LinearMap.baseChange`.
* `TensorProduct.AlgebraTensorModule.distribBaseChange_symm_comp_map_baseChange`: the
  comparison `(A ⊗[R] M) ⊗[A] (A ⊗[R] N) ≃ A ⊗[R] (M ⊗[R] N)` is natural in `M` and `N`, with
  its pure-tensor form
  `TensorProduct.AlgebraTensorModule.distribBaseChange_symm_baseChange_tmul_baseChange`.
* `TensorProduct.tmul_eq_one_tmul_smul_of_mem`: in `R ⊗[B] M`, for a subring `B` of `R` and
  `r ∈ B`, `r ⊗ m = 1 ⊗ r • m`.
* `Submodule.one_tmul_mem_baseChange_of_smul_mem`: if `a • x ∈ N` and `a` becomes a unit in `A`,
  then `1 ⊗ₜ x` lies in the base change of `N` to `A`.
* `LinearMap.baseChange_leftInverse`: base change preserves left inverses.
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
  | tmul x m => simp [smul_tmul']
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

/-- The comparison `(A ⊗[R] M) ⊗[A] (A ⊗[R] N) ≃ A ⊗[R] (M ⊗[R] N)` distributing scalar
extension over a tensor product is natural in both tensor factors. -/
theorem TensorProduct.AlgebraTensorModule.distribBaseChange_symm_comp_map_baseChange
    {R A M N P Q : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]
    (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
    (distribBaseChange R A P Q).symm.toLinearMap ∘ₗ
        TensorProduct.map (f.baseChange A) (g.baseChange A) =
      (TensorProduct.map f g).baseChange A ∘ₗ (distribBaseChange R A M N).symm.toLinearMap := by
  refine TensorProduct.ext' fun x y => ?_
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => simp only [LinearMap.comp_apply, add_tmul, map_add] at h₁ h₂ ⊢; rw [h₁, h₂]
  | tmul a m =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ =>
      simp only [LinearMap.comp_apply, tmul_add, map_add] at h₁ h₂ ⊢; rw [h₁, h₂]
    | tmul b n => simp

/-- Pure-tensor form of `distribBaseChange_symm_comp_map_baseChange`. -/
theorem TensorProduct.AlgebraTensorModule.distribBaseChange_symm_baseChange_tmul_baseChange
    {R A M N P Q : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]
    (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (x : A ⊗[R] M) (y : A ⊗[R] N) :
    (distribBaseChange R A P Q).symm (f.baseChange A x ⊗ₜ[A] g.baseChange A y) =
      (TensorProduct.map f g).baseChange A ((distribBaseChange R A M N).symm (x ⊗ₜ[A] y)) :=
  LinearMap.congr_fun (distribBaseChange_symm_comp_map_baseChange f g) (x ⊗ₜ[A] y)

/-- In `R ⊗[B] M`, for a subring `B` of `R`, an element `r ∈ B` can be moved across the tensor
sign: `r ⊗ m = 1 ⊗ r • m`. -/
theorem TensorProduct.tmul_eq_one_tmul_smul_of_mem {R M : Type*} [CommRing R] [AddCommMonoid M]
    [Module R M] {B : Subring R} {r : R} (hr : r ∈ B) (m : M) :
    r ⊗ₜ[B] m = (1 : R) ⊗ₜ (r • m) := by
  simpa [Subring.smul_def] using smul_tmul (⟨r, hr⟩ : B) (1 : R) m

/-- If `a • x` lies in a submodule `N` and `a` becomes a unit in the algebra `A`, then `1 ⊗ₜ x`
lies in the base change of `N` to `A`. -/
theorem Submodule.one_tmul_mem_baseChange_of_smul_mem {R A M : Type*} [CommSemiring R]
    [Semiring A] [Algebra R A] [AddCommMonoid M] [Module R M] (N : Submodule R M) {a : R}
    (ha : IsUnit (algebraMap R A a)) {x : M} (hx : a • x ∈ N) :
    (1 : A) ⊗ₜ x ∈ N.baseChange A := by
  -- `a` acts on `A ⊗[R] M` through the unit `algebraMap R A a`, and `a • (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)`.
  rw [← (N.baseChange A).smul_mem_iff' ha.unit, Units.smul_def, IsUnit.unit_spec, algebraMap_smul,
    ← tmul_smul]
  exact tmul_mem_baseChange_of_mem 1 hx

/-- Base change preserves left inverses: if `f ∘ₗ g = id`, then `f.baseChange A` is a left
inverse of `g.baseChange A`. -/
theorem LinearMap.baseChange_leftInverse {R A M N : Type*} [CommSemiring R] [Semiring A]
    [Algebra R A] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    {f : N →ₗ[R] M} {g : M →ₗ[R] N} (h : f ∘ₗ g = .id) :
    Function.LeftInverse (f.baseChange A) (g.baseChange A) := fun z ↦ by
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, h, LinearMap.baseChange_id,
    LinearMap.id_apply]

namespace TauCeti

variable (R A M : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [AddCommMonoid M]
  [Module A M] [Module R M] [IsScalarTower R A M]

/-- The action map `A ⊗[R] M →ₗ[A] M`, `a ⊗ m ↦ a • m`, of a module `M` over an `R`-algebra `A`
that need not be commutative. -/
noncomputable def tensorSMul : A ⊗[R] M →ₗ[A] M :=
  AlgebraTensorModule.lift (LinearMap.toSpanSingleton A (M →ₗ[R] M) LinearMap.id)

variable {R A M}

/-- The action map on a pure tensor. -/
@[simp]
theorem tensorSMul_tmul (a : A) (m : M) : tensorSMul R A M (a ⊗ₜ m) = a • m := by
  simp [tensorSMul]

end TauCeti
