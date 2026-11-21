/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PiTensorProduct

/-!
# Basic algebra identities for indexed tensor products

When each `A i` is a non-unital non-associative semiring and an `R`-module whose scalar action
forms a scalar tower with, and commutes with, its multiplication, the factorwise multiplication of
`⨂[R] i, A i` has the same two properties (`PiTensorProduct.isScalarTower_right`,
`PiTensorProduct.smulCommClass_right`). So `LinearMap.mulLeft` and `LinearMap.mulRight` are
available on the tensor product without an algebra structure on the factors.

For a family of `R`-algebras `A i` over a commutative semiring `R`, the algebra multiplication on
the indexed tensor product `⨂[R] i, A i` acts factorwise on pure tensors
(`PiTensorProduct.tprod_mul_tprod`), so it coincides with the bilinear map
`PiTensorProduct.map₂ (fun i ↦ LinearMap.mul R (A i))` obtained by applying factorwise
multiplication (`PiTensorProduct.map₂_mul`). No commutativity of the factors or finiteness of the
index type is required.

## Main results

* `PiTensorProduct.isScalarTower_right`, `PiTensorProduct.smulCommClass_right`: the factorwise
  multiplication of `⨂[R] i, A i` is compatible with scalar multiplication by `R`.
* `PiTensorProduct.map₂_mul`: `PiTensorProduct.map₂ (fun i ↦ LinearMap.mul R (A i))` equals
  `LinearMap.mul R (⨂[R] i, A i)`.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

variable {R : Type*} [CommSemiring R]

section NonUnitalNonAssocSemiring

variable {ι : Type*} {A : ι → Type*} [∀ i, NonUnitalNonAssocSemiring (A i)]
  [∀ i, Module R (A i)] [∀ i, SMulCommClass R (A i) (A i)] [∀ i, IsScalarTower R (A i) (A i)]

/-- Scalar multiplication by `R` forms a scalar tower with the factorwise multiplication of an
indexed tensor product, since that multiplication is `R`-linear in its left argument. -/
instance isScalarTower_right : IsScalarTower R (⨂[R] i, A i) (⨂[R] i, A i) where
  smul_assoc r x y := LinearMap.map_smul₂ mul r x y

/-- Scalar multiplication by `R` commutes with the factorwise multiplication of an indexed tensor
product, since that multiplication is `R`-linear in its right argument. -/
instance smulCommClass_right : SMulCommClass R (⨂[R] i, A i) (⨂[R] i, A i) where
  smul_comm r x y := (map_smul (mul x) r y).symm

end NonUnitalNonAssocSemiring

/-- Applying algebra multiplication in every factor via `PiTensorProduct.map₂` is the
multiplication of the indexed tensor product of algebras. -/
@[simp]
theorem map₂_mul {ι : Type*} {A : ι → Type*} [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] :
    PiTensorProduct.map₂ (fun i ↦ LinearMap.mul R (A i)) = LinearMap.mul R (⨂[R] i, A i) := by
  ext x y
  simp [map₂_tprod_tprod, tprod_mul_tprod, Pi.mul_def]

end PiTensorProduct
