/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Tensor linearization of trilinear maps

A map semilinear in three slots for a common scalar homomorphism induces a semilinear map
on the tensor product of its input modules. The construction is linear over the output
scalar ring and is characterized by its values on triple pure tensors, using
`TensorProduct.ext_threefold`.
-/

public noncomputable section

open scoped TensorProduct

namespace TensorProduct

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {σ : R →+* S}
variable {E₁ E₂ E₃ F : Type*}
  [AddCommMonoid E₁] [Module R E₁] [AddCommMonoid E₂] [Module R E₂]
  [AddCommMonoid E₃] [Module R E₃] [AddCommMonoid F] [Module S F]

variable (σ E₁ E₂ E₃ F) in
/-- Uncurry maps semilinear in three slots on the tensor product of their input modules.
The construction is linear over the output scalar ring, giving compatibility with zero,
addition, and scalar multiplication. -/
def uncurryThreefold :
    (E₁ →ₛₗ[σ] E₂ →ₛₗ[σ] E₃ →ₛₗ[σ] F) →ₗ[S] (E₁ ⊗[R] E₂) ⊗[R] E₃ →ₛₗ[σ] F :=
  (TensorProduct.uncurry σ (E₁ ⊗[R] E₂) E₃ F).comp
    (TensorProduct.uncurry σ E₁ E₂ (E₃ →ₛₗ[σ] F))

/-- The tensor linearization evaluates a pure tensor by evaluating the trilinear map. -/
@[simp]
theorem uncurryThreefold_tmul (T : E₁ →ₛₗ[σ] E₂ →ₛₗ[σ] E₃ →ₛₗ[σ] F)
    (x : E₁) (y : E₂) (z : E₃) :
    uncurryThreefold σ E₁ E₂ E₃ F T ((x ⊗ₜ[R] y) ⊗ₜ[R] z) = T x y z := by
  simp [uncurryThreefold]

end TensorProduct
