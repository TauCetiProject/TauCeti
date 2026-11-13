/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.Matrix.Nonsingular

/-!
# Linear independence from the Gram matrix of a bilinear form

A finite family `c` of vectors is linearly independent as soon as its Gram matrix
`G x y = B (c x) (c y)` with respect to a bilinear form `B` is nonsingular: the rows of `G` are
the images of the `c x` under the linear map `m ↦ (y ↦ B m (c y))`, and the rows of a nonsingular
matrix are linearly independent (`Matrix.Nonsingular.linearIndependent_row`). Over a commutative
ring a matrix is nonsingular exactly when its determinant is a non-zero-divisor
(`Matrix.nonsingular_iff_det_mem_nonZeroDivisors`), which gives the determinant criteria below.

## Main results

* `LinearMap.BilinForm.linearIndependent_of_nonsingular`: over a commutative semiring with
  cancellative addition, a family whose Gram matrix is nonsingular is linearly independent.
* `LinearMap.BilinForm.linearIndependent_of_det_ne_zero`: over a commutative ring without zero
  divisors, a family whose Gram matrix has nonzero determinant is linearly independent.
* `LinearMap.BilinForm.linearIndependent_of_isUnit_det`: a family whose Gram matrix is a
  non-zero-divisor times a matrix of unit determinant is linearly independent.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)
open Matrix

variable {R M ι : Type*} [AddCommMonoid M] [Fintype ι] [DecidableEq ι]

section CommSemiring

variable [CommSemiring R] [IsCancelAdd R] [Module R M]

/-- A family whose Gram matrix with respect to a bilinear form is nonsingular is linearly
independent. -/
theorem linearIndependent_of_nonsingular (B : BilinForm R M) {c : ι → M}
    (h : (Matrix.of fun x y => B (c x) (c y)).Nonsingular) : LinearIndependent R c :=
  -- The map `m ↦ (y ↦ B m (c y))` sends `c x` to row `x` of the Gram matrix, by definition.
  .of_comp (LinearMap.pi fun y => B.flip (c y)) h.linearIndependent_row

end CommSemiring

section CommRing

variable [CommRing R] [Module R M]

/-- A family whose Gram matrix with respect to a bilinear form has nonzero determinant is
linearly independent. -/
theorem linearIndependent_of_det_ne_zero [NoZeroDivisors R] (B : BilinForm R M) {c : ι → M}
    (h : (Matrix.of fun x y => B (c x) (c y)).det ≠ 0) : LinearIndependent R c :=
  B.linearIndependent_of_nonsingular <|
    nonsingular_iff_det_mem_nonZeroDivisors.mpr <| mem_nonZeroDivisors_of_ne_zero h

/-- If the Gram matrix of a finite family `v` is `a` times a matrix of unit determinant, with `a` a
non-zero-divisor, then `v` is linearly independent. -/
theorem linearIndependent_of_isUnit_det {B : BilinForm R M} {a : R} {v : ι → M}
    {G : Matrix ι ι R} (ha : a ∈ nonZeroDivisors R) (hG : ∀ i j, B (v i) (v j) = a * G i j)
    (hdet : IsUnit G.det) : LinearIndependent R v := by
  refine B.linearIndependent_of_nonsingular <| nonsingular_iff_det_mem_nonZeroDivisors.mpr ?_
  rw [show (Matrix.of fun i j => B (v i) (v j)) = a • G by ext; simp [hG], det_smul]
  exact mul_mem (pow_mem ha _) hdet.mem_nonZeroDivisors

end CommRing

end LinearMap.BilinForm
