/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic.Positivity

/-!
# Rank-one Hermitian update of a Gram matrix determinant

Factorizes the determinant of `star C * C + vecMulVec (star (y ᵥ* C)) (y ᵥ* C)` for a square
matrix `C` and row vector `y` over `ℝ` or `ℂ` (`[RCLike 𝕜]`) using the matrix determinant lemma.

## Main results

* `Matrix.norm_det_star_mul_self_add_vecMulVec`:
  `‖(star C * C + vecMulVec (star (y ᵥ* C)) (y ᵥ* C)).det‖ = ‖C.det‖ ^ 2 * (1 + ∑ j, ‖y j‖ ^ 2)`.
-/

public section

namespace Matrix

/-- For a square matrix `C` and a row vector `y` over `ℝ` or `ℂ`,
`‖det (star C * C + vecMulVec (star (y ᵥ* C)) (y ᵥ* C))‖ = ‖det C‖² (1 + ∑ j, ‖y j‖²)`. -/
theorem norm_det_star_mul_self_add_vecMulVec {κ 𝕜 : Type*} [Fintype κ] [DecidableEq κ] [RCLike 𝕜]
    (C : Matrix κ κ 𝕜) (y : κ → 𝕜) :
    ‖(star C * C + vecMulVec (star (y ᵥ* C)) (y ᵥ* C)).det‖ =
      ‖C.det‖ ^ 2 * (1 + ∑ j : κ, ‖y j‖ ^ 2) := by
  have h_factor : star C * C + vecMulVec (star (y ᵥ* C)) (y ᵥ* C) =
      star C * (1 + vecMulVec (star y) y) * C := by
    simp [mul_add, add_mul, star_vecMul, mul_vecMulVec, vecMulVec_mul, star_eq_conjTranspose]
  have h_det : (1 + vecMulVec (star y) y).det = ((1 + ∑ j, ‖y j‖ ^ 2 : ℝ) : 𝕜) := by
    simp [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct, RCLike.star_def,
      RCLike.mul_conj]
  rw [h_factor, det_mul, det_mul, h_det, star_eq_conjTranspose, det_conjTranspose, norm_mul,
    norm_mul, norm_star, RCLike.norm_of_nonneg (by positivity)]
  ring

end Matrix
