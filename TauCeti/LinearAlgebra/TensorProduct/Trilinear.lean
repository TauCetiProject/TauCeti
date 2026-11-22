/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Tensor linearization of trilinear maps

A trilinear map induces a linear map on the tensor product of its three input modules.
The construction is linear in the trilinear map and is uniquely characterized by its
values on triple pure tensors.
-/

public noncomputable section

open scoped TensorProduct

namespace LinearMap

variable {R E₁ E₂ E₃ F : Type*} [CommSemiring R]
  [AddCommMonoid E₁] [Module R E₁] [AddCommMonoid E₂] [Module R E₂]
  [AddCommMonoid E₃] [Module R E₃] [AddCommMonoid F] [Module R F]

variable (R E₁ E₂ E₃ F) in
/-- Linearize trilinear maps on the tensor product of their three input modules.
The linear map structure gives compatibility with zero, addition, and scalar multiplication. -/
def trilinearTensorLinearMap :
    (E₁ →ₗ[R] E₂ →ₗ[R] E₃ →ₗ[R] F) →ₗ[R] (E₁ ⊗[R] E₂) ⊗[R] E₃ →ₗ[R] F :=
  (TensorProduct.uncurry (RingHom.id R) (E₁ ⊗[R] E₂) E₃ F).comp
    (TensorProduct.uncurry (RingHom.id R) E₁ E₂ (E₃ →ₗ[R] F))

/-- The tensor linearization evaluates a pure tensor by evaluating the trilinear map. -/
@[simp]
theorem trilinearTensorLinearMap_tmul (T : E₁ →ₗ[R] E₂ →ₗ[R] E₃ →ₗ[R] F)
    (x : E₁) (y : E₂) (z : E₃) :
    trilinearTensorLinearMap R E₁ E₂ E₃ F T ((x ⊗ₜ[R] y) ⊗ₜ[R] z) = T x y z := by
  simp [trilinearTensorLinearMap]

/-- Agreement on triple pure tensors uniquely characterizes the tensor linearization. -/
theorem trilinearTensorLinearMap_unique (T : E₁ →ₗ[R] E₂ →ₗ[R] E₃ →ₗ[R] F)
    {L : (E₁ ⊗[R] E₂) ⊗[R] E₃ →ₗ[R] F}
    (h : ∀ x y z, L ((x ⊗ₜ[R] y) ⊗ₜ[R] z) = T x y z) :
    L = trilinearTensorLinearMap R E₁ E₂ E₃ F T := by
  apply TensorProduct.ext_threefold
  intro x y z
  simpa only [trilinearTensorLinearMap_tmul] using h x y z

end LinearMap
