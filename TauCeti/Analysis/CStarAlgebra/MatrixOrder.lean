/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.Matrix.Order
import TauCeti.Analysis.CStarAlgebra.CStarMatrix

/-!
# Spectral order on scalar and Hilbert-space operator matrices

The spectral order on `CStarMatrix n n ℂ` agrees with the positive-semidefinite order
on ordinary complex matrices: the algebraic star equivalence between the two carriers
preserves and reflects order, independently of their different norm instances.

More generally, for a complex Hilbert space `H`, an operator matrix
`M : CStarMatrix n n (H →L[ℂ] H)` is positive in the spectral order if and only if all of its
vector quadratic forms `∑ i, ∑ j, ⟪ξ i, M i j (ξ j)⟫_ℂ` are nonnegative in `ℂ`. By complex
polarization, nonnegativity of these scalar pairings already forces `M` to be self-adjoint.
-/

public section

open scoped MatrixOrder ComplexOrder InnerProductSpace

namespace CStarMatrix

/-- Positivity in the matrix C⋆-algebra is ordinary positive semidefiniteness. -/
theorem nonneg_iff_posSemidef {n : Type*} [Fintype n]
    {M : CStarMatrix n n ℂ} : 0 ≤ M ↔ (ofMatrix.symm M).PosSemidef := by
  classical
  rw [← Matrix.nonneg_iff_posSemidef]
  simpa only [map_zero, ← ofMatrix_eq_ofMatrixStarAlgEquiv, Equiv.apply_symm_apply] using
    (map_le_map_iff (ofMatrixStarAlgEquiv (n := n) (A := ℂ))
      (a := 0) (b := ofMatrix.symm M))

/-- An operator matrix over a complex Hilbert space is positive in the spectral order if and only
if all of its vector quadratic forms are nonnegative in `ℂ`. -/
theorem nonneg_iff_forall_sum_inner_nonneg {n H : Type*} [Fintype n]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {M : CStarMatrix n n (H →L[ℂ] H)} :
    0 ≤ M ↔ ∀ ξ : n → H, 0 ≤ ∑ i, ∑ j, ⟪ξ i, M i j (ξ j)⟫_ℂ := by
  refine ⟨fun hM ξ => ?_, fun hξ => nonneg_iff_forall_sum_nonneg.mpr fun X => ?_⟩
  · obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM
    have hrew : (∑ i, ∑ j, ⟪ξ i, (star R * R) i j (ξ j)⟫_ℂ) =
        ∑ l, ⟪∑ i, R l i (ξ i), ∑ j, R l j (ξ j)⟫_ℂ := by
      calc (∑ i, ∑ j, ⟪ξ i, (star R * R) i j (ξ j)⟫_ℂ)
          = ∑ i, ∑ j, ∑ l, ⟪R l i (ξ i), R l j (ξ j)⟫_ℂ := by
            simp_rw [CStarMatrix.mul_apply, CStarMatrix.star_apply, sum_apply,
              ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
              ContinuousLinearMap.star_eq_adjoint, inner_sum,
              ContinuousLinearMap.adjoint_inner_right]
        _ = ∑ i, ∑ l, ∑ j, ⟪R l i (ξ i), R l j (ξ j)⟫_ℂ :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ l, ∑ i, ∑ j, ⟪R l i (ξ i), R l j (ξ j)⟫_ℂ := Finset.sum_comm
        _ = ∑ l, ⟪∑ i, R l i (ξ i), ∑ j, R l j (ξ j)⟫_ℂ := by
            simp_rw [sum_inner, inner_sum]
    rw [hrew]
    exact Finset.sum_nonneg fun l _ =>
      ContinuousLinearMap.isPositive_one.inner_nonneg_right _
  · rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
    intro v
    have hv : 0 ≤ ⟪v, (∑ i, ∑ j, star (X i) * M i j * X j) v⟫_ℂ := by
      simpa only [sum_apply, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.star_eq_adjoint, inner_sum,
        ContinuousLinearMap.adjoint_inner_right] using hξ fun i => X i v
    have hv' : 0 ≤ ⟪(∑ i, ∑ j, star (X i) * M i j * X j) v, v⟫_ℂ := by
      rw [← inner_conj_symm, ← Complex.star_def]
      exact star_nonneg_iff.mpr hv
    exact ⟨(Complex.eq_re_of_ofReal_le hv').symm, (RCLike.nonneg_iff.mp hv').1⟩

end CStarMatrix
