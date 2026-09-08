/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Quadratic forms of matrices on Euclidean space

Pulling the quadratic form `x ↦ ⟪x, B x⟫` of a square matrix `B` back along the linear map of a
rectangular matrix `A` gives the quadratic form of the congruent matrix `Aᴴ * B * A`. This is
the change-of-variables identity behind every computation of a quadratic statistic after a linear
transformation of the underlying vector.

## Main results

* `Matrix.inner_toEuclideanLin_toEuclideanLin` — the quadratic form of `B` at `A x` is the
  quadratic form of `Aᴴ * B * A` at `x`.
-/

public section

open scoped InnerProductSpace

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

/-- Pulling the quadratic form of `B` back along the linear map of `A` gives the quadratic form
of the congruent matrix `Aᴴ * B * A`. -/
theorem inner_toEuclideanLin_toEuclideanLin (A : Matrix κ ι 𝕜) (B : Matrix κ κ 𝕜)
    (x : EuclideanSpace 𝕜 ι) :
    ⟪A.toEuclideanLin x, B.toEuclideanLin (A.toEuclideanLin x)⟫_𝕜 =
      ⟪x, (Aᴴ * B * A).toEuclideanLin x⟫_𝕜 := by
  rw [← LinearMap.adjoint_inner_right, ← toEuclideanLin_conjTranspose_eq_adjoint]
  simp only [toEuclideanLin, toLpLin_mul_same, LinearMap.comp_apply]

end Matrix
