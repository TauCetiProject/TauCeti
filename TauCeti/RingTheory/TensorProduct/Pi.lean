/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Tensor products of algebras distribute over a product in the left factor

Mathlib's `Algebra.TensorProduct.prodRight` distributes `A ⊗[R] (B × C)` over the product in the
right factor. This file gives the algebra equivalence for a product in the left factor,
`(A₁ × A₂) ⊗[R] B ≃ₐ[R] (A₁ ⊗[R] B) × (A₂ ⊗[R] B)`: the algebra form of Mathlib's linear
`TensorProduct.prodLeft`.

## Main declarations

* `TauCeti.Algebra.TensorProduct.prodLeft`: the algebra equivalence above.
-/

public section

open scoped TensorProduct

namespace TauCeti.Algebra.TensorProduct

variable (R A₁ A₂ B : Type*) [CommSemiring R] [Semiring A₁] [Semiring A₂] [Semiring B]
  [Algebra R A₁] [Algebra R A₂] [Algebra R B]

/-- The tensor product of algebras distributes over a product in the left factor:
`(A₁ × A₂) ⊗[R] B ≃ₐ[R] (A₁ ⊗[R] B) × (A₂ ⊗[R] B)`. -/
def prodLeft : (A₁ × A₂) ⊗[R] B ≃ₐ[R] (A₁ ⊗[R] B) × (A₂ ⊗[R] B) :=
  (Algebra.TensorProduct.comm R _ _).trans <|
    (Algebra.TensorProduct.prodRight R R B A₁ A₂).trans <|
    AlgEquiv.prodCongr (Algebra.TensorProduct.comm R B A₁) (Algebra.TensorProduct.comm R B A₂)

variable {R A₁ A₂ B}

/-- `prodLeft` sends a pure tensor `(a₁, a₂) ⊗ₜ b` to the pair `(a₁ ⊗ₜ b, a₂ ⊗ₜ b)`. -/
@[simp]
theorem prodLeft_tmul (a₁ : A₁) (a₂ : A₂) (b : B) :
    prodLeft R A₁ A₂ B ((a₁, a₂) ⊗ₜ b) = (a₁ ⊗ₜ b, a₂ ⊗ₜ b) := by
  simp only [prodLeft, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
    Algebra.TensorProduct.prodRight_tmul, AlgEquiv.prodCongr_apply, Equiv.prodCongr_apply,
    EquivLike.coe_coe, Prod.map_apply]

/-- The inverse of `prodLeft` sends `(a₁ ⊗ₜ b, a₂ ⊗ₜ b)` to `(a₁, a₂) ⊗ₜ b`. -/
@[simp]
theorem prodLeft_symm_tmul (a₁ : A₁) (a₂ : A₂) (b : B) :
    (prodLeft R A₁ A₂ B).symm (a₁ ⊗ₜ b, a₂ ⊗ₜ b) = (a₁, a₂) ⊗ₜ b :=
  (AlgEquiv.symm_apply_eq _).2 (prodLeft_tmul a₁ a₂ b).symm

end TauCeti.Algebra.TensorProduct
