/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import TauCeti.Analysis.Matrix.SpectralMeasure.Basic

/-!
# The finite-dimensional Girko identity

For a complex square matrix `A`, away from its eigenvalues, the logarithmic potential of its
empirical eigenvalue measure at `z` is the normalized logarithm of the norm of the determinant
of `A - zI`. The same quantity is the average logarithm of the singular values of `A - zI`.

This module proves the finite-dimensional identity only; distributional Laplacians and
potential-convergence results are separate developments.

## References

* T. Tao, *Topics in Random Matrix Theory*, American Mathematical Society (2012), §2.8.3;
  see p. 229 for the log-determinant/singular-value formula and equation (2.179) for its
  distributional Laplacian context.
-/

public section

noncomputable section

open MeasureTheory

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Girko's finite-dimensional hermitization identity away from the eigenvalues: the logarithmic
potential is the average logarithm of the singular values of `A - zI`. -/
theorem logarithmicPotential_eigenvalueMeasure_eq_inv_card_mul_sum_log_singularValues
    (A : Matrix ι ι ℂ) (z : ℂ)
    (hdet : (A - scalar ι z).det ≠ 0) :
    (A.eigenvalueMeasure : Measure ℂ).logarithmicPotential z =
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
  rw [logarithmicPotential_eigenvalueMeasure_eq_inv_card_mul_log_norm_det A z hdet, hnormdet]
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
