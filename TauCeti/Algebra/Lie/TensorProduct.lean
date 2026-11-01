/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Prod
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Lie homomorphisms from products to tensor products

Two Lie homomorphisms into associative algebras induce a Lie homomorphism from the product of
their domains to the tensor product of their codomains. The two images commute because they lie
in separate tensor factors.

## Main definitions

* `LieHom.prodToTensor`: the induced Lie homomorphism from a product to a tensor product.
-/

public section

open scoped TensorProduct

namespace LieHom

variable {R L M A B : Type*}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]
variable [Ring A] [Algebra R A] [Ring B] [Algebra R B]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Two Lie homomorphisms into associative algebras induce a Lie homomorphism from the product of
their domains to the tensor product of their codomains, with each image placed in its corresponding
tensor factor. -/
def prodToTensor (f : L →ₗ⁅R⁆ A) (g : M →ₗ⁅R⁆ B) : (L × M) →ₗ⁅R⁆ (A ⊗[R] B) where
  __ := (Algebra.TensorProduct.includeLeft.toLinearMap ∘ₗ f.toLinearMap).coprod
    (Algebra.TensorProduct.includeRight.toLinearMap ∘ₗ g.toLinearMap)
  map_lie' {_ _} := by
    simp [LieRing.of_associative_ring_bracket, mul_add, add_mul, TensorProduct.sub_tmul,
      TensorProduct.tmul_sub]
    abel

/-- Compute the product-to-tensor Lie homomorphism on a pair:
`prodToTensor f g (x, y) = f x ⊗ 1 + 1 ⊗ g y`. -/
@[simp]
theorem prodToTensor_apply (f : L →ₗ⁅R⁆ A) (g : M →ₗ⁅R⁆ B) (z : L × M) :
    prodToTensor f g z = f z.1 ⊗ₜ[R] (1 : B) + (1 : A) ⊗ₜ[R] g z.2 := by
  rw [← coe_toLinearMap]
  simp only [prodToTensor, LinearMap.coprod_apply, LinearMap.comp_apply, coe_toLinearMap,
    AlgHom.toLinearMap_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply]

end LieHom
