/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic
public import TauCeti.Analysis.Matrix.SpectralMeasure.SingularValues

/-!
# The finite-dimensional Girko identity

For a complex square matrix, away from its eigenvalues, its empirical logarithmic potential is
the normalized logarithm of the determinant of the shifted matrix. The same quantity is the
average logarithm of its singular values.

This module proves the finite-dimensional identity only; distributional Laplacians and
potential-convergence results are separate developments.
-/

public section

noncomputable section

open MeasureTheory

namespace Matrix

variable {n : ℕ}

/-- The empirical logarithmic potential of a complex square matrix, evaluated where its
logarithmic kernel is finite on the empirical spectrum. -/
def empiricalLogPotential [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) : ℝ :=
  ∫ w, Real.log ‖z - w‖ ∂(A.eigenvalueMeasure : Measure ℂ)

/-- The norm of the determinant is the product of the singular values. -/
theorem norm_det_eq_prod_singularValues [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A.det‖ = ∏ i : Fin n, (toEuclideanLin A).singularValues i := by
  have hdet : (toEuclideanLin A).det = A.det := by
    rw [toEuclideanLin_eq_toLin_orthonormal]
    rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis]
    simp [LinearMap.toMatrix_toLin]
  have hnorm : (toEuclideanLin A).normDet = ‖A.det‖ := by
    rw [LinearMap.normDet_eq_norm_det, hdet]
  have hprod : (toEuclideanLin A).normDet =
      ∏ i : Fin n, (toEuclideanLin A).singularValues i := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin,
      Fin.prod_univ_eq_prod_range] using
        (LinearMap.normDet_eq_prod_singularValues (toEuclideanLin A))
  exact hnorm.symm.trans hprod

/-- Away from the eigenvalues, the empirical logarithmic potential is the logarithm of the
shifted determinant. -/
theorem empiricalLogPotential_eq_log_norm_det [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    (hdet : (A - scalar (Fin n) z).det ≠ 0) :
    A.empiricalLogPotential z =
      (Fintype.card (Fin n) : ℝ)⁻¹ * Real.log ‖(A - scalar (Fin n) z).det‖ := by
  classical
  rw [empiricalLogPotential, integral_eigenvalueMeasure]
  rw [smul_eq_mul, Fintype.card_fin]
  have hroots : (A - scalar (Fin n) z).det =
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
      ‖(A - scalar (Fin n) z).det‖ =
        (A.charpoly.roots.map fun w : ℂ => ‖z - w‖).prod := by
    rw [hroots]
    induction A.charpoly.roots using Multiset.induction_on with
    | empty => simp
    | cons w roots ih => simp [norm_sub_rev, ih]
  have hlog :
      Real.log ‖(A - scalar (Fin n) z).det‖ =
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
    [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ)
    (hdet : (A - scalar (Fin n) z).det ≠ 0) :
    A.empiricalLogPotential z =
      (Fintype.card (Fin n) : ℝ)⁻¹ *
          Real.log ‖(A - scalar (Fin n) z).det‖ ∧
      A.empiricalLogPotential z =
        (Fintype.card (Fin n) : ℝ)⁻¹ *
          ∑ i : Fin n, Real.log ((toEuclideanLin (A - scalar (Fin n) z)).singularValues i) := by
  refine ⟨empiricalLogPotential_eq_log_norm_det A z hdet, ?_⟩
  rw [empiricalLogPotential_eq_log_norm_det A z hdet, norm_det_eq_prod_singularValues]
  have hne (i : Fin n) :
      (toEuclideanLin (A - scalar (Fin n) z)).singularValues i ≠ 0 := by
    intro hzero
    have hprod :
        ∏ j : Fin n, (toEuclideanLin (A - scalar (Fin n) z)).singularValues j = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i) hzero
    have hdet0 : ‖(A - scalar (Fin n) z).det‖ = 0 :=
      (norm_det_eq_prod_singularValues (A - scalar (Fin n) z)).trans hprod
    exact hdet (norm_eq_zero.mp hdet0)
  have hpos (i : Fin n) :
      0 < (toEuclideanLin (A - scalar (Fin n) z)).singularValues i :=
    lt_of_le_of_ne (LinearMap.singularValues_nonneg _ i) (Ne.symm (hne i))
  rw [Real.log_prod (fun i _ => (ne_of_gt (hpos i)))]

end Matrix

end
