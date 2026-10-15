/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Linear independence from the Gram matrix of a bilinear form

A family of vectors whose Gram matrix with respect to a bilinear form has nonzero determinant is
linearly independent, over any commutative ring without zero divisors. A linear relation
`∑ x, g x • c x = 0` pairs with every `c y` to give `G *ᵥ g = 0` for the Gram matrix `G`, and a
square matrix with nonzero determinant has trivial kernel (`Matrix.eq_zero_of_mulVec_eq_zero`).
Mathlib has the matrix statement but not the bilinear-form criterion.

The more general unit-determinant criterion allows a common non-zero-divisor factor in the Gram
matrix, without requiring the coefficient ring to have no zero divisors.

## Main results

* `LinearMap.BilinForm.linearIndependent_of_det_ne_zero`: a family whose Gram matrix with respect
  to a bilinear form has nonzero determinant is linearly independent.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)
open Matrix

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

omit [NoZeroDivisors R] in
/-- If the Gram matrix of a finite family `v` is `a` times a matrix of unit determinant, with `a` a
non-zero-divisor, then `v` is linearly independent. -/
theorem linearIndependent_of_isUnit_det {B : BilinForm R M} {a : R} {ι : Type*}
    [Fintype ι] [DecidableEq ι] {v : ι → M}
    {G : Matrix ι ι R} (ha : a ∈ nonZeroDivisors R) (hG : ∀ i j, B (v i) (v j) = a * G i j)
    (hdet : IsUnit G.det) : LinearIndependent R v := by
  refine Fintype.linearIndependent_iff.mpr fun g hg ↦ ?_
  have hgG : g ᵥ* G = 0 := funext fun j ↦ (mul_cancel_left_mem_nonZeroDivisors ha).mp (by
    have := congrArg (fun x ↦ B x (v j)) hg
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hG,
      map_zero, LinearMap.zero_apply] at this
    rw [Pi.zero_apply, mul_zero, ← this, vecMul, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring)
  have hg0 : g = 0 := Matrix.vecMul_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det G).mpr hdet) (hgG.trans (Matrix.zero_vecMul G).symm)
  intro i
  simpa only [Pi.zero_apply] using congrFun hg0 i

end LinearMap.BilinForm
