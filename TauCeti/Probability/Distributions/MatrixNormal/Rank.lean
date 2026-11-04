/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.MatrixNormal.PDF

import TauCeti.Analysis.Matrix.Sqrt
import TauCeti.LinearAlgebra.Matrix.PosDef.Rank
import TauCeti.MeasureTheory.Measure.Matrix

/-!
# Almost-sure rank of matrix normal laws

A matrix normal law with positive-definite row and column covariances has a density and therefore
has maximal rank almost surely. When the column covariance is the identity, the same conclusion
for a positive-semidefinite row covariance follows after factoring its square root through its
exact rank.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace TauCeti.Probability

/-- A matrix normal law with positive-definite row and column covariances has maximal rank almost
surely. -/
theorem ae_rank_eq_min_matrixNormalMeasure_of_posDef
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {U : Matrix m m ℝ} {V : Matrix n n ℝ} (hU : U.PosDef) (hV : V.PosDef) :
    ∀ᵐ X ∂matrixNormalMeasure (0 : Matrix m n ℝ) U V,
      X.rank = min (Fintype.card m) (Fintype.card n) := by
  have hac : matrixNormalMeasure (0 : Matrix m n ℝ) U V ≪ volume := by
    rw [matrixNormalMeasure_eq_withDensity 0 hU hV]
    exact withDensity_absolutelyContinuous volume (matrixNormalPDF 0 U V)
  exact Measure.ae_rank_eq_min_matrix _ hac

/-- A matrix normal law with identity column covariance has rank equal to the smaller of the row
covariance rank and the number of columns almost surely. -/
theorem ae_rank_eq_min_matrixNormalMeasure_right_one
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {U : Matrix m m ℝ} (hU : U.PosSemidef) :
    ∀ᵐ X ∂matrixNormalMeasure (0 : Matrix m n ℝ) U 1,
      X.rank = min U.rank (Fintype.card n) := by
  classical
  obtain ⟨L, R, hfac⟩ := (CFC.sqrt U).exists_eq_mul_fin_rank
  have hL : L.rank = Fintype.card (Fin (CFC.sqrt U).rank) :=
    Matrix.rank_left_factor_eq (by simp) hfac
  have hR : R.rank = Fintype.card (Fin (CFC.sqrt U).rank) := by
    apply le_antisymm R.rank_le_card_height
    calc
      Fintype.card (Fin (CFC.sqrt U).rank) = (CFC.sqrt U).rank := Fintype.card_fin _
      _ = (L * R).rank := congrArg Matrix.rank hfac
      _ ≤ R.rank := Matrix.rank_mul_le_right L R
  have hRR : (R * Rᵀ).PosDef := by
    simpa only [Matrix.mul_one] using
      ((Matrix.PosDef.one.mul_mul_transpose_same_iff_rank_eq_card R).2 hR)
  have hmax :
      ∀ᵐ X : Matrix (Fin (CFC.sqrt U).rank) n ℝ
        ∂matrixNormalMeasure 0 (R * Rᵀ) 1,
        X.rank = min (Fintype.card (Fin (CFC.sqrt U).rank)) (Fintype.card n) :=
    ae_rank_eq_min_matrixNormalMeasure_of_posDef hRR (Matrix.PosDef.one (n := n))
  have hmap := map_mul_mul_add_matrixNormalMeasure
    (0 : Matrix (Fin (CFC.sqrt U).rank) n ℝ) hRR.posSemidef Matrix.PosSemidef.one
    L (1 : Matrix n n ℝ) 0
  have hcov : L * (R * Rᵀ) * Lᵀ = U := by
    calc
      L * (R * Rᵀ) * Lᵀ = (L * R) * (L * R)ᵀ := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = CFC.sqrt U * (CFC.sqrt U)ᵀ := by rw [← hfac]
      _ = U := hU.sqrt_mul_transpose_sqrt
  simp only [Matrix.mul_zero, add_zero, Matrix.mul_one, Matrix.transpose_one] at hmap
  rw [hcov] at hmap
  rw [← hmap]
  refine (ae_map_iff (by fun_prop) (Matrix.measurableSet_setOfPred_rank_eq _)).2 ?_
  filter_upwards [hmax] with X hX
  rw [Matrix.rank_mul_eq_right_of_rank_eq_card L X hL, hX, hU.rank_sqrt]
  simp

end TauCeti.Probability
