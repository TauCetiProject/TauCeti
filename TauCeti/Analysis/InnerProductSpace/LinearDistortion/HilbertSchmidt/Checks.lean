/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearDistortion.HilbertSchmidt
public import TauCeti.Analysis.InnerProductSpace.SingularValues.Planar
import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.EckartYoung

/-!
# Checks for the Hilbert–Schmidt distortion of a linear map

Worked examples for `Orientation.hilbertSchmidtDistortion` (`q_S`) on a real inner product plane
`E` with an orthonormal basis `e`, oriented by `e` on both sides, writing `toLin e e M` for the
operator with matrix `M` in that basis:

* `diag(2, 1)` has `‖A‖_HS² = 5` and `J(A) = 2`, so `q_S(A) = 5/4`, while `q_O(A) = 2`;
* the reflection `diag(-1, 1)` has `q_S = ∞`, and the zero map has `q_S = 0`.
-/

public section

open Module Matrix LinearMap TauCeti.UnitarilyInvariantSeminorm
open scoped ENNReal

namespace TauCeti.HilbertSchmidtDistortionChecks

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Fact (finrank ℝ E = 2)] (e : OrthonormalBasis (Fin 2) ℝ E)

/-- `diag(2, 1)` has `‖A‖_HS² = 5` and `q_S = 5 / (2 · 2) = 5/4`, while `q_O = 2`, so
`5/4 ≤ 2 ≤ 2 · 5/4 = 5/2`. -/
example :
    e.toBasis.orientation.hilbertSchmidtDistortion e.toBasis.orientation
        (toLin e.toBasis e.toBasis (diagonal ![(2 : ℝ), 1])) = ENNReal.ofReal (5 / 4) ∧
      e.toBasis.orientation.outerDistortion e.toBasis.orientation
        (toLin e.toBasis e.toBasis (diagonal ![(2 : ℝ), 1])) = 2 := by
  have hJ : e.toBasis.orientation.orientedJacobian e.toBasis.orientation
      (toLin e.toBasis e.toBasis (diagonal ![(2 : ℝ), 1])) = 2 := by simp
  have hσ := singularValues_toLin_diagonal_fin_two e (d₀ := (2 : ℝ)) (d₁ := 1) (by norm_num)
  constructor
  · rw [Orientation.hilbertSchmidtDistortion_of_pos _ _ (by rw [hJ]; norm_num), hJ,
      frobenius_apply_eq_sqrt_sum_range_sq_singularValues, finrank_eq_card_basis e.toBasis,
      Fintype.card_fin, hσ]
    norm_num [Finset.sum_range_succ, Real.sq_sqrt]
  · rw [Orientation.outerDistortion_of_pos _ _ (by rw [hJ]; norm_num), hJ,
      norm_toContinuousLinearMap_eq_singularValues_zero, hσ]
    norm_num

/-- `diag(-1, 1)` has `q_S = ∞`, and the zero map has `q_S = 0`. -/
example :
    e.toBasis.orientation.hilbertSchmidtDistortion e.toBasis.orientation
        (toLin e.toBasis e.toBasis (diagonal ![(-1 : ℝ), 1])) = ⊤ ∧
      e.toBasis.orientation.hilbertSchmidtDistortion e.toBasis.orientation (0 : E →ₗ[ℝ] E) = 0 :=
  ⟨Orientation.hilbertSchmidtDistortion_of_nonpos _ _ (by simp) (by simp),
    Orientation.hilbertSchmidtDistortion_zero _ _ two_pos⟩

end TauCeti.HilbertSchmidtDistortionChecks
