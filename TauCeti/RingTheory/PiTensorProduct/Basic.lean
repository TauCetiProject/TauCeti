/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PiTensorProduct

/-!
# Basic algebra identities for indexed tensor products

For a family of `R`-algebras `A i` over a commutative semiring `R`, the algebra multiplication on
the indexed tensor product `⨂[R] i, A i` acts factorwise on pure tensors
(`PiTensorProduct.tprod_mul_tprod`), so it coincides with the bilinear map
`PiTensorProduct.map₂ (fun i ↦ LinearMap.mul R (A i))` obtained by applying factorwise
multiplication (`PiTensorProduct.map₂_mul`). No commutativity of the factors or finiteness of the
index type is required.

## Main results

* `PiTensorProduct.map₂_mul`: `PiTensorProduct.map₂ (fun i ↦ LinearMap.mul R (A i))` equals
  `LinearMap.mul R (⨂[R] i, A i)`.
-/

public section

open scoped TensorProduct

namespace PiTensorProduct

variable {R : Type*} [CommSemiring R]

/-- Applying algebra multiplication in every factor via `PiTensorProduct.map₂` is the
multiplication of the indexed tensor product of algebras. -/
@[simp]
theorem map₂_mul {ι : Type*} {A : ι → Type*} [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] :
    PiTensorProduct.map₂ (fun i ↦ LinearMap.mul R (A i)) = LinearMap.mul R (⨂[R] i, A i) := by
  ext x y
  simp [map₂_tprod_tprod, tprod_mul_tprod, Pi.mul_def]

end PiTensorProduct
