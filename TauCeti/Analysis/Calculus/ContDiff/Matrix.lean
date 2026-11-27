/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Smoothness of determinants and adjugates

The determinant of a square matrix is a polynomial in its entries, so a matrix-valued map whose
entries are `C^n` has a `C^n` determinant. This is the `C^n` counterpart of Mathlib's
`Continuous.matrix_det`, and holds at every regularity, including analytic regularity, globally
(`ContDiff.matrix_det`), on a set (`ContDiffOn.matrix_det`) and at a point
(`ContDiffAt.matrix_det`).

Each entry of the adjugate is the determinant of a matrix whose entries are entries of the
original matrix or constants, so the adjugate of such a map again has `C^n` entries
(`ContDiff.matrix_adjugate`, `ContDiffOn.matrix_adjugate` and `ContDiffAt.matrix_adjugate`), the
`C^n` counterpart of Mathlib's `Continuous.matrix_adjugate`.
-/

public section

variable {𝕜 E 𝔸 ι : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedCommRing 𝔸] [NormedAlgebra 𝕜 𝔸] [Fintype ι] [DecidableEq ι] {n : WithTop ℕ∞}
  {s : Set E}

/-- A matrix-valued map whose entries are `C^n` on a set has a determinant that is `C^n` there. -/
theorem ContDiffOn.matrix_det {M : E → Matrix ι ι 𝔸}
    (hM : ∀ i j, ContDiffOn 𝕜 n (fun x ↦ M x i j) s) :
    ContDiffOn 𝕜 n (fun x ↦ (M x).det) s := by
  simp_rw [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ ↦ contDiffOn_const.mul (contDiffOn_prod fun i _ ↦ hM _ _)

/-- A matrix-valued map whose entries are `C^n` at a point has a determinant which is `C^n` there.
-/
theorem ContDiffAt.matrix_det {M : E → Matrix ι ι 𝔸} {x : E}
    (hM : ∀ i j, ContDiffAt 𝕜 n (fun y ↦ M y i j) x) : ContDiffAt 𝕜 n (fun y ↦ (M y).det) x := by
  simp_rw [Matrix.det_apply']
  exact ContDiffAt.sum fun σ _ ↦ contDiffAt_const.mul (contDiffAt_prod fun i _ ↦ hM _ _)

/-- A matrix-valued map with `C^n` entries has a `C^n` determinant. -/
theorem ContDiff.matrix_det {M : E → Matrix ι ι 𝔸} (hM : ∀ i j, ContDiff 𝕜 n fun x ↦ M x i j) :
    ContDiff 𝕜 n fun x ↦ (M x).det :=
  contDiffOn_univ.1 (ContDiffOn.matrix_det fun i j ↦ (hM i j).contDiffOn)

/-- A matrix-valued map whose entries are `C^n` on a set has an adjugate whose entries are `C^n`
there. -/
theorem ContDiffOn.matrix_adjugate {M : E → Matrix ι ι 𝔸}
    (hM : ∀ i j, ContDiffOn 𝕜 n (fun x ↦ M x i j) s) (i j : ι) :
    ContDiffOn 𝕜 n (fun x ↦ (M x).adjugate i j) s := by
  simp only [Matrix.adjugate_apply]
  refine ContDiffOn.matrix_det fun k l ↦ ?_
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffOn_const
  · exact hM k l

/-- A matrix-valued map whose entries are `C^n` at a point has an adjugate whose entries are `C^n`
there. -/
theorem ContDiffAt.matrix_adjugate {M : E → Matrix ι ι 𝔸} {x : E}
    (hM : ∀ i j, ContDiffAt 𝕜 n (fun y ↦ M y i j) x) (i j : ι) :
    ContDiffAt 𝕜 n (fun y ↦ (M y).adjugate i j) x := by
  simp only [Matrix.adjugate_apply]
  refine ContDiffAt.matrix_det fun k l ↦ ?_
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiffAt_const
  · exact hM k l

/-- A matrix-valued map with `C^n` entries has an adjugate with `C^n` entries. -/
theorem ContDiff.matrix_adjugate {M : E → Matrix ι ι 𝔸}
    (hM : ∀ i j, ContDiff 𝕜 n fun x ↦ M x i j) (i j : ι) :
    ContDiff 𝕜 n fun x ↦ (M x).adjugate i j :=
  contDiffOn_univ.1 (ContDiffOn.matrix_adjugate (fun i j ↦ (hM i j).contDiffOn) i j)
