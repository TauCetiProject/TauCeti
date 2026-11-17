/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyPositiveMap
import TauCeti.Analysis.CStarAlgebra.CStarMatrix

/-!
# The transpose on `M₂(ℂ)` is positive but not `2`-positive

The transpose on complex square matrices `CStarMatrix m m ℂ` is `1`-positive, that is, positive
(`isNPositive_one_transpose`). On `M₂(ℂ) = CStarMatrix (Fin 2) (Fin 2) ℂ` it is unital, but it is
not `2`-positive (`not_isNPositive_two_transpose`): it violates the Kadison–Schwarz inequality
`φ(a)⋆ φ(a) ≤ φ(a⋆a)` at the matrix unit `E₁₂`. So `1`-positivity does not imply `2`-positivity,
and `TauCeti.IsNPositive.star_map_mul_map_le_of_map_one` cannot assume positivity in place of
`2`-positivity.
-/

public section

open scoped ComplexOrder

namespace TauCeti.CompletelyPositiveMapExample

/-- The transpose on complex square matrices is `1`-positive. -/
theorem isNPositive_one_transpose {m : Type*} [Fintype m] :
    IsNPositive 1 (CStarMatrix.ofMatrixₗ.toLinearMap ∘ₗ
      (Matrix.transposeLinearEquiv m m ℂ ℂ).toLinearMap ∘ₗ
        (CStarMatrix.ofMatrixₗ (R := ℂ)).symm.toLinearMap) := by
  refine isNPositive_one_iff.mpr fun M hM =>
    CStarMatrix.nonneg_iff_forall_sum_nonneg.mpr fun x => ?_
  -- The quadratic form of the transpose at `x` is that of `M` at `star x`.
  convert CStarMatrix.nonneg_iff_forall_sum_nonneg.mp hM (star x) using 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [CStarMatrix.ofMatrix_apply, mul_assoc, mul_comm, mul_left_comm]

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
