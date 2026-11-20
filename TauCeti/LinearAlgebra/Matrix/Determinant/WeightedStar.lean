/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.RCLike.Basic

/-!
# Weighted conjugate determinants

The product of a determinant and a column-weighted conjugate determinant is the product of
the column weights times the squared norm of the determinant. This algebraic identity converts
products of evaluation determinants into weighted squared norms in determinant integration.
-/

public section

namespace Matrix

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- Column weights factor out of the product of a determinant and its conjugate, leaving
the squared norm of the determinant. -/
theorem det_mul_det_weighted_star (A : Matrix ι ι 𝕜) (w : ι → 𝕜) :
    A.det * det (Matrix.of fun i j ↦ w j * star (A i j)) =
      (∏ j, w j) * (‖A.det‖ ^ 2 : ℝ) := by
  have hs : (Matrix.of fun i j ↦ star (A i j)) = (starRingEnd 𝕜).mapMatrix A := by
    ext i j
    simp
  have hd := det_mul_row w (Matrix.of fun i j ↦ star (A i j))
  simp only [Matrix.of_apply] at hd
  rw [hd, hs, ← RingHom.map_det, starRingEnd_apply, mul_left_comm]
  exact congrArg ((∏ j, w j) * ·) (by
    simpa only [starRingEnd_apply, RCLike.ofReal_pow] using RCLike.mul_conj A.det)

end Matrix
