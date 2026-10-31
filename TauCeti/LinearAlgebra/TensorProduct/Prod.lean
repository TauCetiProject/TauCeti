/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Tensoring a product with the base ring

Mathlib's `TensorProduct.prodRight` distributes a tensor product over a binary product. When the
second factor of the product is the base ring `R` itself, composing with the right unitor
`TensorProduct.AlgebraTensorModule.rid` gives the identification
`M₁ ⊗[R] (M₂ × R) ≃ (M₁ ⊗[R] M₂) × M₁`, `m₁ ⊗ (m₂, r) ↦ (m₁ ⊗ m₂, r • m₁)`. It is linear over
any `R`-algebra `S` acting on `M₁`. For `M₁ = S` this describes the scalar extension of `M₂ × R`
to `S`: adjoining one direction to `M₂` and then extending scalars adjoins one direction to the
scalar extension of `M₂`.

## Main declarations

* `TensorProduct.prodRightRid`: the identification `M₁ ⊗[R] (M₂ × R) ≃ (M₁ ⊗[R] M₂) × M₁`.
* `TensorProduct.prodRightRid_tmul` and `TensorProduct.prodRightRid_symm_apply`: its values on
  pure tensors and its inverse.
-/

public section

open scoped TensorProduct

namespace TensorProduct

variable (R S M₁ M₂ : Type*)
variable [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M₁] [AddCommMonoid M₂]
variable [Module R M₁] [Module S M₁] [IsScalarTower R S M₁] [Module R M₂]

/-- The `S`-linear equivalence `M₁ ⊗[R] (M₂ × R) ≃ (M₁ ⊗[R] M₂) × M₁`,
`m₁ ⊗ (m₂, r) ↦ (m₁ ⊗ m₂, r • m₁)`, obtained from `TensorProduct.prodRight` and the right
unitor. -/
noncomputable def prodRightRid : M₁ ⊗[R] (M₂ × R) ≃ₗ[S] (M₁ ⊗[R] M₂) × M₁ :=
  prodRight R S M₁ M₂ R ≪≫ₗ (LinearEquiv.refl S _).prodCongr (AlgebraTensorModule.rid R S M₁)

variable {R S M₁ M₂}

/-- `TensorProduct.prodRightRid` sends `m₁ ⊗ (m₂, r)` to `(m₁ ⊗ m₂, r • m₁)`. -/
@[simp]
theorem prodRightRid_tmul (m₁ : M₁) (m : M₂ × R) :
    prodRightRid R S M₁ M₂ (m₁ ⊗ₜ m) = (m₁ ⊗ₜ m.1, m.2 • m₁) := by
  simp [prodRightRid]

/-- The inverse of `TensorProduct.prodRightRid` sends `(x, m₁)` to the image of `x` under the
inclusion `M₂ → M₂ × R`, plus `m₁ ⊗ (0, 1)`. -/
@[simp]
theorem prodRightRid_symm_apply (x : M₁ ⊗[R] M₂) (m₁ : M₁) :
    (prodRightRid R S M₁ M₂).symm (x, m₁) =
      (LinearMap.inl R M₂ R).lTensor M₁ x + m₁ ⊗ₜ (0, 1) := by
  simp [prodRightRid, prodRight]

end TensorProduct
