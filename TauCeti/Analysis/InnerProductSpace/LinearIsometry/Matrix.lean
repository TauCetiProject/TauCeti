/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Matrices of linear isometries

The matrix of a linear isometry in finite orthonormal bases has orthonormal columns.
The domain and codomain may have different dimensions. This identity supplies left inverses
for coefficient matrices after mapping scalars into a star algebra.
-/

public section

open scoped Matrix

namespace LinearIsometry

variable {𝕜 E F ι κ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- The conjugate transpose of the matrix of a linear isometry in orthonormal bases
is a left inverse, even when the matrix is rectangular. -/
@[simp]
theorem toMatrix_conjTranspose_mul_self (i : E →ₗᵢ[𝕜] F)
    (b : OrthonormalBasis ι 𝕜 E) (c : OrthonormalBasis κ 𝕜 F) :
    (LinearMap.toMatrix b.toBasis c.toBasis i.toLinearMap)ᴴ *
      LinearMap.toMatrix b.toBasis c.toBasis i.toLinearMap = 1 := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.repr_apply_apply, LinearIsometry.coe_toLinearMap, RCLike.star_def,
    inner_conj_symm, c.sum_inner_mul_inner, i.inner_map_map, orthonormal_iff_ite.mp b.orthonormal,
    Matrix.one_apply]

end LinearIsometry
