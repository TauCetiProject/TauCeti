/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.TensorProduct.Matrix
public import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The determinant of a tensor product of endomorphisms

For endomorphisms `f` of `M` and `g` of `N`, finite free modules over a commutative ring `R`,

`det (f ⊗ g) = det f ^ rank N * det g ^ rank M`

(`LinearMap.det_tensorProductMap`). In bases `b` of `M` and `c` of `N` the matrix of `f ⊗ g` in
the product basis `b ⊗ c` is the Kronecker product of the matrices of `f` and `g`
(`TensorProduct.toMatrix_map`), whose determinant is computed by `Matrix.det_kronecker`.

For line bundles, `rank M = rank N = 1`, this is the multiplicativity of the transition functions
of a tensor product, the reason why the first Chern class of a tensor product of complex line
bundles is the sum of their first Chern classes.
-/

public section

open Module

namespace LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
  [Module.Finite R M] [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N]

/-- The determinant of `f ⊗ g` is `det f ^ rank N * det g ^ rank M`. -/
theorem det_tensorProductMap (f : M →ₗ[R] M) (g : N →ₗ[R] N) :
    LinearMap.det (TensorProduct.map f g) =
      LinearMap.det f ^ finrank R N * LinearMap.det g ^ finrank R M := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  let b := Free.chooseBasis R M
  let c := Free.chooseBasis R N
  rw [← LinearMap.det_toMatrix (b.tensorProduct c), TensorProduct.toMatrix_map,
    Matrix.det_kronecker, LinearMap.det_toMatrix, LinearMap.det_toMatrix,
    finrank_eq_card_chooseBasisIndex, finrank_eq_card_chooseBasisIndex]

end LinearMap
