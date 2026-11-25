/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.Analysis.InnerProductSpace.Variational.Shift

/-!
# Examples: semibounded shifts of diagonal forms on `ℝ²`

On `V = H = ℝ²` with `j = id`, the diagonal form `a = diag(1, -3)`,
`a(u, v) = u₁ v₁ - 3 u₂ v₂`, satisfies the semibounded bound `c ‖u‖² ≤ a(u, u) + ω ‖j u‖²` with
`c = 1` and `ω = 4`, and its shift by `4` is `a₄ = diag(5, 1)`. The bound also allows negative
`ω`: `a = diag(2, 3)` satisfies it with `c = 1` and `ω = -1`. The corresponding examples on `ℝ`
are in `TauCeti.Analysis.InnerProductSpace.Variational.Shift`.
-/

public section

open RCLike ContinuousLinearMap

namespace TauCeti.ShiftExamples

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The diagonal form `diag(d₁, d₂)`, `(u, v) ↦ d₁ u₁ v₁ + d₂ u₂ v₂`, on `ℝ²`. -/
noncomputable def diagForm (d : Fin 2 → ℝ) : ℝ² →L⋆[ℝ] ℝ² →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ ℝ²)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.diagonal d))

/-- The diagonal form in coordinates. -/
private theorem diagForm_apply (d : Fin 2 → ℝ) (u v : ℝ²) :
    diagForm d u v = d 0 * (u 0 * v 0) + d 1 * (u 1 * v 1) := by
  simp [diagForm, Matrix.inner_toEuclideanCLM, Matrix.mulVec_diagonal, dotProduct,
    Fin.sum_univ_two]
  ring

/-- `diag(1, -3)` on `ℝ²` satisfies the semibounded bound with `c = 1` and `ω = 4`, for
`j = id`. -/
example (u : ℝ²) :
    1 * ‖u‖ ^ 2 ≤ re (diagForm ![1, -3] u u) + 4 * ‖ContinuousLinearMap.id ℝ ℝ² u‖ ^ 2 := by
  simp only [diagForm_apply, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp
  nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]

/-- The shift by `4` of `diag(1, -3)` is `diag(5, 1)`. -/
example :
    shiftedForm (ContinuousLinearMap.id ℝ ℝ²) (diagForm ![1, -3]) 4 = diagForm ![5, 1] := by
  ext u v
  simp only [shiftedForm_apply, diagForm_apply]
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

/-- Negative `ω` is allowed: `diag(2, 3)` on `ℝ²` satisfies the semibounded bound with `c = 1`
and `ω = -1`, for `j = id`. -/
example (u : ℝ²) :
    1 * ‖u‖ ^ 2 ≤ re (diagForm ![2, 3] u u) + (-1) * ‖ContinuousLinearMap.id ℝ ℝ² u‖ ^ 2 := by
  simp only [diagForm_apply, EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
  simp
  nlinarith [sq_nonneg (u 0), sq_nonneg (u 1)]

end TauCeti.ShiftExamples
