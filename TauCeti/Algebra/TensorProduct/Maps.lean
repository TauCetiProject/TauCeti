/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Algebra maps out of tensor products

Mathlib's `Algebra.TensorProduct.productMap` assembles two algebra maps into a commutative
algebra. This file records compatibility with post-composition and reconstruction from the
two restrictions along the canonical inclusions. The source algebras need not be commutative
and carry no coalgebra structure.
-/

public section

open scoped TensorProduct

namespace AlgHom

variable {R H₁ H₂ A B : Type*} [CommSemiring R]
variable [Semiring H₁] [Semiring H₂] [CommSemiring A] [CommSemiring B]
variable [Algebra R H₁] [Algebra R H₂] [Algebra R A] [Algebra R B]

/-- Post-composition distributes over the tensor-product map induced by a pair of algebra maps. -/
theorem comp_productMap (φ : A →ₐ[R] B) (f₁ : H₁ →ₐ[R] A) (f₂ : H₂ →ₐ[R] A) :
    φ.comp (Algebra.TensorProduct.productMap f₁ f₂) =
      Algebra.TensorProduct.productMap (φ.comp f₁) (φ.comp f₂) := by
  apply Algebra.TensorProduct.ext'
  intro x y
  simp [Algebra.TensorProduct.productMap_apply_tmul]

/-- An algebra map out of a tensor product is recovered from its two restrictions. -/
@[simp]
theorem productMap_comp_includeLeft_includeRight (g : (H₁ ⊗[R] H₂) →ₐ[R] A) :
    Algebra.TensorProduct.productMap (g.comp Algebra.TensorProduct.includeLeft)
        (g.comp Algebra.TensorProduct.includeRight) = g := by
  apply Algebra.TensorProduct.ext'
  intro x y
  simp [Algebra.TensorProduct.productMap_apply_tmul, ← map_mul]

end AlgHom
