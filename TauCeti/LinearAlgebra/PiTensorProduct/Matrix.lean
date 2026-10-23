/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# The matrix of a tensor product of a family of linear maps

Given bases `b i` of the modules `M i` and `c i` of the modules `N i`, the tensor product
`PiTensorProduct.map f` of a finite family of linear maps `f i : M i →ₗ[R] N i` has, in the product
bases `Basis.piTensorProduct b` and `Basis.piTensorProduct c`, the matrix whose entry at the pair
of index tuples `(p, q)` is the product over `i` of the entries `(p i, q i)` of the matrices of the
`f i`. This is the many-factor analogue of `TensorProduct.toMatrix_map`, which identifies the matrix
of a binary tensor product of linear maps with the Kronecker product of their matrices.

## Main results

* `PiTensorProduct.toMatrix_map`: the matrix of `PiTensorProduct.map f` in product bases.
-/

public section

open Module

namespace PiTensorProduct

variable {ι R : Type*} [CommSemiring R] [Fintype ι] [DecidableEq ι]
  {M N : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
  {κ ν : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)] [∀ i, Finite (ν i)]

/-- **The matrix of a tensor product of linear maps in product bases**: its entry at `(p, q)` is
the product over the factors of the entries `(p i, q i)` of the matrices of the factors. -/
theorem toMatrix_map (b : ∀ i, Basis (κ i) R (M i)) (c : ∀ i, Basis (ν i) R (N i))
    (f : ∀ i, M i →ₗ[R] N i) :
    LinearMap.toMatrix (Basis.piTensorProduct b) (Basis.piTensorProduct c) (map f) =
      Matrix.of fun p q => ∏ i, LinearMap.toMatrix (b i) (c i) (f i) (p i) (q i) := by
  ext p q
  simp [LinearMap.toMatrix_apply, map_tprod]

end PiTensorProduct
