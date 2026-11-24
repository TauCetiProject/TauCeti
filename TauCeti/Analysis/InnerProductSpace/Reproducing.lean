/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Reproducing
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Orthonormal basis expansion of real reproducing kernels

The scalar reproducing kernel of a real RKHS is the sum of the products of evaluations
of any finite orthonormal basis.
-/

public section

open scoped InnerProductSpace

namespace OrthonormalBasis

/-- A real reproducing kernel is the sum of products of evaluations of any orthonormal basis. -/
theorem sum_apply_mul_apply {H X ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [RKHS ℝ H X ℝ] [Fintype ι] (b : OrthonormalBasis ι ℝ H) (x y : X) :
    ∑ i, b i x * b i y = RKHS.kernel H x y 1 := by
  simpa only [RKHS.kerFun_inner, RKHS.inner_kerFun, RKHS.kerFun_apply, Real.inner_apply,
    mul_one, one_mul, mul_comm] using
    b.sum_inner_mul_inner (RKHS.kerFun H y 1) (RKHS.kerFun H x 1)

end OrthonormalBasis
