/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Nonsingular

/-!
# Matrices with a right inverse up to a regular scalar

If `M * J = c • 1` for a left-regular scalar `c`, then `M` is injective on vectors, even though it
need not be invertible: `c • 1` is right-regular, hence so is `M`, and for square matrices over a
commutative semiring with cancellative addition right and left regularity agree.

Conversely, the determinant of a linearly independent family in a basis of the same size is a
non-zero-divisor, although the family need not span: over `ℤ`, the family `(2)` in the basis `(1)`
of `ℤ` has determinant `2`.

## Main results

* `Matrix.mulVec_injective_of_mul_eq_smul_one`: `M * J = c • 1` with `c` left-regular forces
  `M.mulVec` to be injective.
* `Module.Basis.det_mem_nonZeroDivisors`: the determinant `b.det v` of a linearly independent
  family `v` is a non-zero-divisor.
-/

public section

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommSemiring R] [IsCancelAdd R]

/-- If `M * J = c • 1` for a left-regular scalar `c`, then multiplication of vectors by `M` is
injective. -/
theorem mulVec_injective_of_mul_eq_smul_one {c : R} (hc : IsLeftRegular c) {M J : Matrix n n R}
    (h : M * J = c • (1 : Matrix n n R)) : Function.Injective M.mulVec := by
  rw [← isLeftRegular_iff_mulVec_injective, isLeftRegular_iff_isRightRegular]
  refine IsRightRegular.of_mul (a := J) fun X Y hXY ↦ ext fun i j ↦ hc ?_
  simpa [h, mul_comm c] using congr_fun₂ hXY i j

end Matrix

namespace Module.Basis

/-- The determinant of a linearly independent family `v` in a basis `b` of the same size is a
non-zero-divisor. -/
theorem det_mem_nonZeroDivisors {ι R M : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    [AddCommGroup M] [Module R M] (b : Basis ι R M) {v : ι → M} (hv : LinearIndependent R v) :
    b.det v ∈ nonZeroDivisors R := by
  rw [det_apply, ← Matrix.nonsingular_iff_det_mem_nonZeroDivisors,
    ← Matrix.linearIndependent_col_iff]
  convert hv.map' b.equivFun.toLinearMap b.equivFun.ker using 1
  ext j i
  simp [toMatrix_apply, Matrix.col]

end Module.Basis
