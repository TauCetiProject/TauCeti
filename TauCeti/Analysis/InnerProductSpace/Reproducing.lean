/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Reproducing
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Orthonormal basis expansion of scalar reproducing kernels

The scalar reproducing kernel of a real or complex RKHS is the sum of the products of
evaluations of any finite orthonormal basis, conjugating the second factor.
-/

public section

open scoped ComplexConjugate InnerProductSpace

namespace OrthonormalBasis

/-- A scalar reproducing kernel is the sum of products of orthonormal basis evaluations,
conjugating the second factor. -/
theorem sum_apply_mul_conj_apply {𝕜 H X ι : Type*} [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H] [RKHS 𝕜 H X 𝕜] [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 H) (x y : X) :
    ∑ i, b i x * conj (b i y) = RKHS.kernel H x y 1 := by
  have h := b.sum_inner_mul_inner (RKHS.kerFun H x 1) (RKHS.kerFun H y 1)
  rw [RKHS.kerFun_inner x 1 (RKHS.kerFun H y 1)] at h
  simpa only [RKHS.kerFun_inner, RKHS.inner_kerFun, RKHS.kerFun_apply, RCLike.inner_apply,
    map_one, mul_one, one_mul] using h

end OrthonormalBasis
