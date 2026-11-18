/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic

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

/-- The empirical logarithmic potential of a complex square matrix, evaluated where its
logarithmic kernel is finite on the empirical spectrum. -/
def empiricalLogPotential (A : Matrix ι ι ℂ)
    (z : ℂ) : ℝ :=
  ∫ w, Real.log ‖z - w‖ ∂(A.eigenvalueMeasure : Measure ℂ)

/-- The empirical logarithmic potential is the integral of the logarithmic kernel against the
empirical eigenvalue measure. -/
theorem empiricalLogPotential_def (A : Matrix ι ι ℂ)
    (z : ℂ) :
    A.empiricalLogPotential z =
      ∫ w, Real.log ‖z - w‖ ∂(A.eigenvalueMeasure : Measure ℂ) := by
  rw [empiricalLogPotential]

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
  have hroots : (A - scalar ι z).det =
      (A.charpoly.roots.map fun w : ℂ => w - z).prod := by
    rw [Matrix.det_eq_prod_roots_charpoly, Matrix.charpoly_sub_scalar]
    have hcomp :
        (A.charpoly.comp (Polynomial.X + Polynomial.C z)).roots =
          A.charpoly.roots.map (fun w : ℂ => w - z) := by
      simpa using
        (Polynomial.roots_comp_C_mul_X_add_C A.charpoly (1 : ℂ) z isUnit_one)
    exact congrArg Multiset.prod hcomp
  have hroot_ne : ∀ w ∈ A.charpoly.roots, w - z ≠ 0 := by
    have hprod_ne : (A.charpoly.roots.map fun w : ℂ => w - z).prod ≠ 0 := by
      rw [← hroots]
      exact hdet
    intro w hw hzero
    apply hprod_ne
    rw [Multiset.prod_eq_zero_iff]
    exact Multiset.mem_map.mpr ⟨w, hw, hzero⟩
  have hnorm :
      ‖(A - scalar ι z).det‖ =
        (A.charpoly.roots.map fun w : ℂ => ‖z - w‖).prod := by
    rw [hroots, Multiset.norm_prod, Multiset.map_map]
    simp only [Function.comp_def, norm_sub_rev]
  have hlog :
      Real.log ‖(A - scalar ι z).det‖ =
        (A.charpoly.roots.map fun w : ℂ => Real.log ‖z - w‖).sum := by
    rw [hnorm, Real.log_multiset_prod]
    · simp only [Multiset.map_map, Function.comp_def]
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hx
    exact norm_ne_zero_iff.mpr (by
      intro h
      apply hroot_ne w hw
      exact sub_eq_zero.mpr ((sub_eq_zero.mp h).symm))
  rw [hlog]

/-- Girko's finite-dimensional hermitization identity away from the eigenvalues:
the logarithmic potential equals both the normalized log determinant and the average log
singular value. -/
theorem empiricalLogPotential_eq_log_det_eq_sum_log_singularValues
    (A : Matrix ι ι ℂ) (z : ℂ)
    (hdet : (A - scalar ι z).det ≠ 0) :
    A.empiricalLogPotential z =
      (Fintype.card ι : ℝ)⁻¹ *
          Real.log ‖(A - scalar ι z).det‖ ∧
      A.empiricalLogPotential z =
        (Fintype.card ι : ℝ)⁻¹ *
          ∑ i : Fin (Fintype.card ι),
            Real.log ((toEuclideanLin (A - scalar ι z)).singularValues i) := by
  have hnormdet :
      ‖(A - scalar ι z).det‖ =
        ∏ i : Fin (Fintype.card ι),
          (toEuclideanLin (A - scalar ι z)).singularValues i := by
    have hdet' : (toEuclideanLin (A - scalar ι z)).det = (A - scalar ι z).det := by
      rw [toEuclideanLin_eq_toLin_orthonormal]
      rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun ι ℂ).toBasis]
      simp [LinearMap.toMatrix_toLin]
    have hnorm : (toEuclideanLin (A - scalar ι z)).normDet =
        ‖(A - scalar ι z).det‖ := by
      rw [LinearMap.normDet_eq_norm_det, hdet']
    have hprod : (toEuclideanLin (A - scalar ι z)).normDet =
        ∏ i : Fin (Fintype.card ι),
          (toEuclideanLin (A - scalar ι z)).singularValues i := by
      simpa only [finrank_euclideanSpace, Fin.prod_univ_eq_prod_range] using
        (LinearMap.normDet_eq_prod_singularValues (toEuclideanLin (A - scalar ι z)))
    exact hnorm.symm.trans hprod
  refine ⟨empiricalLogPotential_eq_log_norm_det A z hdet, ?_⟩
  rw [empiricalLogPotential_eq_log_norm_det A z hdet, hnormdet]
  have hprod : ∏ i : Fin (Fintype.card ι),
      (toEuclideanLin (A - scalar ι z)).singularValues i ≠ 0 := by
    rw [← hnormdet]
    exact norm_ne_zero_iff.mpr hdet
  have hne (i : Fin (Fintype.card ι)) :
      (toEuclideanLin (A - scalar ι z)).singularValues i ≠ 0 :=
    (Finset.prod_ne_zero_iff).mp hprod i (Finset.mem_univ _)
  have hpos (i : Fin (Fintype.card ι)) :
      0 < (toEuclideanLin (A - scalar ι z)).singularValues i :=
    lt_of_le_of_ne (LinearMap.singularValues_nonneg _ i) (Ne.symm (hne i))
  rw [Real.log_prod (fun i _ => (ne_of_gt (hpos i)))]

end Matrix

end
