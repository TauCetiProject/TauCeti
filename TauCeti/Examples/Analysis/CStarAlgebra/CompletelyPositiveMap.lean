/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap
import TauCeti.Analysis.CStarAlgebra.CStarMatrix

/-!
# The transpose on `M₂(ℂ)` is not `2`-positive

The transpose on `M₂(ℂ) = CStarMatrix (Fin 2) (Fin 2) ℂ` is unital, but it is not `2`-positive:
it violates the Kadison–Schwarz inequality `φ(a)⋆ φ(a) ≤ φ(a⋆a)` at the matrix unit `E₁₂`. The
transpose is also a positive map (a classical fact that this file does not prove), so this example
illustrates why `TauCeti.IsNPositive.star_map_mul_map_le_of_map_one` assumes `2`-positivity rather
than positivity.
-/

public section

open scoped ComplexOrder

namespace TauCeti.CompletelyPositiveMapExample

/-- The transpose on `M₂(ℂ)` is not `2`-positive. -/
theorem not_isNPositive_two_transpose :
    ¬ IsNPositive 2 (CStarMatrix.ofMatrixₗ.toLinearMap ∘ₗ
      (Matrix.transposeLinearEquiv (Fin 2) (Fin 2) ℂ ℂ).toLinearMap ∘ₗ
        (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.toLinearMap) := by
  set T : CStarMatrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] CStarMatrix (Fin 2) (Fin 2) ℂ :=
    CStarMatrix.ofMatrixₗ.toLinearMap ∘ₗ
      (Matrix.transposeLinearEquiv (Fin 2) (Fin 2) ℂ ℂ).toLinearMap ∘ₗ
        (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.toLinearMap
  have hT (M : CStarMatrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) : T M i j = M j i := by
    simp [T, CStarMatrix.ofMatrix_apply]
  intro h
  have h1 : T 1 = 1 := by
    ext i j
    simp [hT, CStarMatrix.one_apply, eq_comm]
  let a : CStarMatrix (Fin 2) (Fin 2) ℂ := CStarMatrix.ofMatrix !![0, 1; 0, 0]
  have hle := sub_nonneg.mpr (h.star_map_mul_map_le_of_map_one h1 a)
  have := CStarMatrix.diag_nonneg_of_nonneg hle 0
  norm_num [a, hT, CStarMatrix.mul_apply, CStarMatrix.star_apply, CStarMatrix.ofMatrix_apply,
    Fin.sum_univ_two] at this

end TauCeti.CompletelyPositiveMapExample
