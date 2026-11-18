/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Smoothness of determinants

The determinant of a square matrix is a polynomial in its entries, so a matrix-valued map whose
entries are `C^n` has a `C^n` determinant. This is the `C^n` counterpart of Mathlib's
`Continuous.matrix_det`, and holds at every regularity, including analytic regularity, both
globally (`ContDiff.matrix_det`) and on a set (`ContDiffOn.matrix_det`).
-/

public section

variable {𝕜 E 𝔸 ι : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedCommRing 𝔸] [NormedAlgebra 𝕜 𝔸] [Fintype ι] [DecidableEq ι] {n : WithTop ℕ∞}

/-- A matrix-valued map with `C^n` entries has a `C^n` determinant. -/
theorem ContDiff.matrix_det {M : E → Matrix ι ι 𝔸} (hM : ∀ i j, ContDiff 𝕜 n fun x ↦ M x i j) :
    ContDiff 𝕜 n fun x ↦ (M x).det := by
  simp_rw [Matrix.det_apply']
  exact ContDiff.sum fun σ _ ↦ contDiff_const.mul (contDiff_prod fun i _ ↦ hM _ _)

/-- A matrix-valued map with `C^n` entries on a set has a `C^n` determinant on that set. -/
theorem ContDiffOn.matrix_det {M : E → Matrix ι ι 𝔸} {s : Set E}
    (hM : ∀ i j, ContDiffOn 𝕜 n (fun x ↦ M x i j) s) : ContDiffOn 𝕜 n (fun x ↦ (M x).det) s := by
  simp_rw [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ ↦ contDiffOn_const.mul (contDiffOn_prod fun i _ ↦ hM _ _)
