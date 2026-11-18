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
entries are `C^n` at a point has a `C^n` determinant there (`ContDiffAt.matrix_det`), and one whose
entries are `C^n` everywhere has a `C^n` determinant (`ContDiff.matrix_det`). These are the `C^n`
counterparts of Mathlib's `Continuous.matrix_det`, and hold at every regularity, including analytic
regularity.
-/

public section

variable {𝕜 E 𝔸 ι : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedCommRing 𝔸] [NormedAlgebra 𝕜 𝔸] [Fintype ι] [DecidableEq ι] {n : WithTop ℕ∞}

/-- A matrix-valued map whose entries are `C^n` at a point has a determinant which is `C^n` there.
-/
theorem ContDiffAt.matrix_det {M : E → Matrix ι ι 𝔸} {x : E}
    (hM : ∀ i j, ContDiffAt 𝕜 n (fun y ↦ M y i j) x) : ContDiffAt 𝕜 n (fun y ↦ (M y).det) x := by
  simp_rw [Matrix.det_apply']
  exact ContDiffAt.sum fun σ _ ↦ contDiffAt_const.mul (contDiffAt_prod fun i _ ↦ hM _ _)

/-- A matrix-valued map with `C^n` entries has a `C^n` determinant. -/
theorem ContDiff.matrix_det {M : E → Matrix ι ι 𝔸} (hM : ∀ i j, ContDiff 𝕜 n fun x ↦ M x i j) :
    ContDiff 𝕜 n fun x ↦ (M x).det :=
  contDiff_iff_contDiffAt.2 fun _ ↦ ContDiffAt.matrix_det fun i j ↦ (hM i j).contDiffAt
