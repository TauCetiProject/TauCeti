/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensor products of module actions

The bilinear map `TensorProduct.map₂ (Algebra.lsmul R R N).toLinearMap (LinearMap.mul R H)`
acts on pure tensors by `(a ⊗ h, n ⊗ h') ↦ a • n ⊗ h * h'`. This file records its interaction
with the unit and multiplication by `a ⊗ 1`, without choosing a tensor-product module instance.

It also records the compatibility of the base-changed action map
`(A ⊗[B] A) ⊗[R] N → A ⊗[B] N` with multiplication on the middle factor.
-/

public section

open scoped TensorProduct

namespace TensorProduct

section Action

variable {R H A N : Type*} [CommSemiring R] [Semiring H] [Algebra R H]
  [Semiring A] [Algebra R A] [AddCommMonoid N] [Module R N] [Module A N] [IsScalarTower R A N]

/-- Multiplying by `a ⊗ 1` before the tensor action is scalar multiplication by `a` afterward. -/
theorem map₂_lsmul_mul_tmul_one_mul (a : A) (u : A ⊗[R] H) (v : N ⊗[R] H) :
    map₂ (Algebra.lsmul R R N).toLinearMap (LinearMap.mul R H) ((a ⊗ₜ 1) * u) v =
      a • map₂ (Algebra.lsmul R R N).toLinearMap (LinearMap.mul R H) u v := by
  induction u with
  | add u u' hu hu' => simp only [mul_add, map_add, LinearMap.add_apply, hu, hu', smul_add]
  | tmul x h =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    induction v with
    | add v v' hv hv' => simp only [map_add, hv, hv', smul_add]
    | tmul n h' => simp [smul_tmul']

/-- The unit acts as the identity under the tensor action. -/
@[simp]
theorem map₂_lsmul_mul_one (v : N ⊗[R] H) :
    map₂ (Algebra.lsmul R R N).toLinearMap (LinearMap.mul R H) (1 : A ⊗[R] H) v = v := by
  induction v with
  | add v v' hv hv' => simp only [map_add, hv, hv']
  | tmul n h => simp [Algebra.TensorProduct.one_def]

/-- Acting by `1 ⊗ h` multiplies the right tensor factor by `h`. -/
theorem map₂_lsmul_mul_one_tmul (h : H) (v : N ⊗[R] H) :
    map₂ (Algebra.lsmul R R N).toLinearMap (LinearMap.mul R H) ((1 : A) ⊗ₜ h) v =
      (LinearMap.mulLeft R h).lTensor N v := by
  induction v with
  | add v v' hv hv' => simp only [map_add, hv, hv']
  | tmul n h' => simp

end Action

namespace AlgebraTensorModule

variable {R A B N : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [CommSemiring B] [Algebra R B] [Algebra B A] [IsScalarTower R B A]
  [AddCommMonoid N] [Module R N] [Module A N] [IsScalarTower R A N]
  [Module B N] [IsScalarTower B A N]

/-- In the base-changed action map, multiplication in the middle tensor factor can be moved
to the module argument. -/
theorem lTensor_liftBaseChange_assoc_mul_tmul (z : A ⊗[B] A) (x : A) (n : N) :
    (((((LinearMap.id : N →ₗ[R] N).liftBaseChange A).restrictScalars B).lTensor A ∘ₗ
        (assoc R B B A A N).toLinearMap).restrictScalars R) ((z * (1 ⊗ₜ x)) ⊗ₜ[R] n) =
      (((((LinearMap.id : N →ₗ[R] N).liftBaseChange A).restrictScalars B).lTensor A ∘ₗ
        (assoc R B B A A N).toLinearMap).restrictScalars R) (z ⊗ₜ[R] (x • n)) := by
  induction z with
  | add z z' hz hz' => simp only [add_mul, add_tmul, map_add, hz, hz']
  | tmul a y => simp [mul_smul]

end AlgebraTensorModule

end TensorProduct
