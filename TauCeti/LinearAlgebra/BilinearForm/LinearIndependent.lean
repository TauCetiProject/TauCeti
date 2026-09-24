/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# Linear independence from the Gram matrix of a bilinear form

A family of vectors whose Gram matrix with respect to a bilinear form has nonzero determinant is
linearly independent, over any commutative ring without zero divisors. A linear relation
`∑ x, g x • c x = 0` pairs with every `c y` to give `G *ᵥ g = 0` for the Gram matrix `G`, and a
square matrix with nonzero determinant has trivial kernel (`Matrix.eq_zero_of_mulVec_eq_zero`).
Mathlib has the matrix statement but not the bilinear-form criterion.

## Main results

* `LinearMap.BilinForm.linearIndependent_of_det_ne_zero`: a family whose Gram matrix with respect
  to a bilinear form has nonzero determinant is linearly independent.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {R M : Type*} [CommRing R] [NoZeroDivisors R] [AddCommGroup M] [Module R M]

/-- A family whose Gram matrix with respect to a bilinear form has nonzero determinant is
linearly independent. -/
theorem linearIndependent_of_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : BilinForm R M) {c : ι → M}
    (h : (Matrix.of fun x y => B (c x) (c y)).det ≠ 0) : LinearIndependent R c := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  refine congrFun (Matrix.eq_zero_of_mulVec_eq_zero h (v := g) ?_)
  funext y
  calc Matrix.mulVec (Matrix.of fun x y => B (c x) (c y)) g y = B (c y) (∑ x, g x • c x) := by
        simp [Matrix.mulVec, dotProduct, mul_comm]
    _ = 0 := by rw [hg, map_zero]

end LinearMap.BilinForm
