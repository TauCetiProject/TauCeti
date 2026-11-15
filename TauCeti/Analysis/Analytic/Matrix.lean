/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Analytic.Constructions

/-!
# Analyticity of determinants

The determinant of a square matrix is a polynomial in its entries, so a matrix-valued map whose
entries are analytic has an analytic determinant (an entrywise analytic counterpart of Mathlib's
`Continuous.matrix_det`):

* `TauCeti.analyticWithinAt_matrix_det`, `TauCeti.analyticAt_matrix_det`: analyticity of
  `x ↦ (M x).det` at a point within a set or on a neighborhood.
* `TauCeti.analyticOn_matrix_det`, `TauCeti.analyticOnNhd_matrix_det`: analyticity of
  `x ↦ (M x).det` on a set.
-/

public section

namespace TauCeti

variable {𝕜 E 𝔸 ι : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedCommRing 𝔸] [NormedAlgebra 𝕜 𝔸] [Fintype ι] [DecidableEq ι]

/-- A matrix-valued map whose entries are analytic within `s` at `x₀` has determinant analytic
within `s` at `x₀`. -/
theorem analyticWithinAt_matrix_det {M : E → Matrix ι ι 𝔸} {s : Set E} {x₀ : E}
    (hM : ∀ i j, AnalyticWithinAt 𝕜 (fun x ↦ M x i j) s x₀) :
    AnalyticWithinAt 𝕜 (fun x ↦ (M x).det) s x₀ := by
  have hdet : (fun x ↦ (M x).det) =
      ∑ σ : Equiv.Perm ι, fun x ↦ ((Equiv.Perm.sign σ : ℤ) : 𝔸) * ∏ i, M x (σ i) i := by
    ext x
    simp [Matrix.det_apply']
  rw [hdet]
  exact Finset.univ.analyticWithinAt_sum fun σ _ ↦
    analyticWithinAt_const.mul (Finset.univ.analyticWithinAt_fun_prod fun i _ ↦ hM _ _)

/-- A matrix-valued map whose entries are analytic at `x₀` has determinant analytic at `x₀`. -/
theorem analyticAt_matrix_det {M : E → Matrix ι ι 𝔸} {x₀ : E}
    (hM : ∀ i j, AnalyticAt 𝕜 (fun x ↦ M x i j) x₀) :
    AnalyticAt 𝕜 (fun x ↦ (M x).det) x₀ := by
  simp_rw [← analyticWithinAt_univ] at hM ⊢
  exact analyticWithinAt_matrix_det hM

/-- A matrix-valued map whose entries are analytic on `s` has determinant analytic on `s`. -/
theorem analyticOn_matrix_det {M : E → Matrix ι ι 𝔸} {s : Set E}
    (hM : ∀ i j, AnalyticOn 𝕜 (fun x ↦ M x i j) s) :
    AnalyticOn 𝕜 (fun x ↦ (M x).det) s :=
  fun x hx ↦ analyticWithinAt_matrix_det fun i j ↦ hM i j x hx

/-- A matrix-valued map whose entries are neighborhood-analytic on `s` has neighborhood-analytic
determinant on `s`. -/
theorem analyticOnNhd_matrix_det {M : E → Matrix ι ι 𝔸} {s : Set E}
    (hM : ∀ i j, AnalyticOnNhd 𝕜 (fun x ↦ M x i j) s) :
    AnalyticOnNhd 𝕜 (fun x ↦ (M x).det) s :=
  fun x hx ↦ analyticAt_matrix_det fun i j ↦ hM i j x hx

end TauCeti

end
