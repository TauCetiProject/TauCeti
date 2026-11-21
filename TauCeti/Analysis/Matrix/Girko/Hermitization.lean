/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import TauCeti.Analysis.Matrix.SingularValues
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
import TauCeti.LinearAlgebra.Matrix.Charpoly.Roots

/-!
# The finite-dimensional Girko identity

For a complex square matrix, away from its eigenvalues, its empirical logarithmic potential is
the normalized logarithm of the norm of the shifted determinant, with normalization by the matrix
dimension. The same quantity is the average logarithm of its singular values.

This module proves the finite-dimensional identity only; distributional Laplacians and
potential-convergence results are separate developments.
-/

public section

noncomputable section

open MeasureTheory

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The empirical logarithmic potential of a complex square matrix. The kernel uses Lean's
totalized convention `Real.log 0 = 0`; away from the eigenvalues it agrees with the classical
logarithmic potential. -/
def empiricalLogPotential (A : Matrix ι ι ℂ)
    (z : ℂ) : ℝ :=
  ∫ w, Real.log ‖z - w‖ ∂(A.eigenvalueMeasure : Measure ℂ)

/-- Away from the eigenvalues, the empirical logarithmic potential is `1 / card ι` times the
logarithm of the norm of the shifted determinant. -/
theorem empiricalLogPotential_eq_log_norm_det
    (A : Matrix ι ι ℂ) (z : ℂ)
    (hdet : (A - scalar ι z).det ≠ 0) :
    A.empiricalLogPotential z =
      (Fintype.card ι : ℝ)⁻¹ * Real.log ‖(A - scalar ι z).det‖ := by
  classical
  rw [empiricalLogPotential, integral_eigenvalueMeasure]
  rw [smul_eq_mul]
  have hshift : Polynomial.aeval A (Polynomial.X - Polynomial.C z) = A - scalar ι z := by
    simp [algebraMap_eq_diagonal, scalar_apply]
  have hroots : (A - scalar ι z).det =
      (A.charpoly.roots.map fun w : ℂ => w - z).prod := by
    rw [← hshift, Matrix.det_aeval_eq_prod_roots_charpoly]
    simp_rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hnorm :
      ‖(A - scalar ι z).det‖ =
        (A.charpoly.roots.map fun w : ℂ => ‖z - w‖).prod := by
    rw [hroots, Multiset.norm_prod_map]
    simp only [norm_sub_rev]
  have hlog :
      Real.log ‖(A - scalar ι z).det‖ =
        (A.charpoly.roots.map fun w : ℂ => Real.log ‖z - w‖).sum := by
    rw [hnorm, Real.log_multiset_prod]
    · simp only [Multiset.map_map, Function.comp_def]
    intro x hx hx0
    subst x
    exact (norm_ne_zero_iff.mpr hdet) (hnorm.trans (Multiset.prod_eq_zero hx))
  rw [hlog]

/-- Girko's finite-dimensional hermitization identity away from the eigenvalues: the logarithmic
potential is the average logarithm of the singular values. -/
theorem empiricalLogPotential_eq_sum_log_singularValues
    (A : Matrix ι ι ℂ) (z : ℂ)
    (hdet : (A - scalar ι z).det ≠ 0) :
    A.empiricalLogPotential z =
      (Fintype.card ι : ℝ)⁻¹ *
        ∑ i : Fin (Fintype.card ι),
          Real.log ((toEuclideanLin (A - scalar ι z)).singularValues i) := by
  have hnormdet :
      ‖(A - scalar ι z).det‖ =
        ∏ i : Fin (Fintype.card ι),
          (toEuclideanLin (A - scalar ι z)).singularValues i := by
    simpa only [LinearMap.normDet_eq_norm_det, LinearMap.det_toLpLin,
      finrank_euclideanSpace, Fin.prod_univ_eq_prod_range] using
        (LinearMap.normDet_eq_prod_singularValues (toEuclideanLin (A - scalar ι z)))
  rw [empiricalLogPotential_eq_log_norm_det A z hdet, hnormdet]
  have hprod : ∏ i : Fin (Fintype.card ι),
      (toEuclideanLin (A - scalar ι z)).singularValues i ≠ 0 := by
    rw [← hnormdet]
    exact norm_ne_zero_iff.mpr hdet
  have hne (i : Fin (Fintype.card ι)) :
      (toEuclideanLin (A - scalar ι z)).singularValues i ≠ 0 :=
    (Finset.prod_ne_zero_iff).mp hprod i (Finset.mem_univ _)
  rw [Real.log_prod (fun i _ => hne i)]

end Matrix

end
