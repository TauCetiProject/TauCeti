/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Matrix equivalences in the standard basis

The linear equivalence of a matrix with unit determinant acts by matrix-vector
multiplication in `Pi.basisFun`; its inverse acts by the inverse matrix. These evaluation
lemmas allow coordinate calculations without unfolding the equivalence or basis wrappers.
-/

public section

namespace Matrix

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- In the standard basis, the linear equivalence of a matrix acts by `mulVec`. -/
theorem toLinearEquiv_basisFun_apply (N : Matrix ι ι R) (hN : IsUnit N.det)
    (x : ι → R) : N.toLinearEquiv (Pi.basisFun R ι) hN x = N *ᵥ x := by
  rw [toLinearEquiv_apply, toLin_eq_toLin', toLin'_apply]

/-- In the standard basis, the inverse linear equivalence acts by the inverse matrix. -/
@[simp]
theorem toLinearEquiv_basisFun_symm_apply (N : Matrix ι ι R) (hN : IsUnit N.det)
    (x : ι → R) : (N.toLinearEquiv (Pi.basisFun R ι) hN).symm x = N⁻¹ *ᵥ x := by
  apply (N.toLinearEquiv (Pi.basisFun R ι) hN).injective
  rw [LinearEquiv.apply_symm_apply, toLinearEquiv_basisFun_apply, mulVec_mulVec,
    mul_nonsing_inv N hN, one_mulVec]

end Matrix
