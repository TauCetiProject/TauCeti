/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.GroupTheory.Perm.Fin

/-!
# Expansion and reindexing of the permanent

The permanent expands along any column by deleting that column and each possible row.
The minors use the order-preserving maps `Fin.succAbove`. Independent equivalences of the
row and column indices preserve the permanent. These identities support iterated Gaussian
covariance contractions.

The column expansion adapts Mathlib's `Matrix.det_succ_column_zero`, `Matrix.det_succ_row`,
and `Matrix.det_succ_column` in `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`,
with the alternating signs omitted.
-/

public section

namespace Matrix

/-- Independent equivalences of the row and column indices preserve the permanent. -/
@[simp]
theorem permanent_submatrix_equiv {R α β : Type*} [CommSemiring R] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (A : Matrix β β R) (e₁ e₂ : α ≃ β) :
    (A.submatrix e₁ e₂).permanent = A.permanent := by
  unfold Matrix.permanent
  refine Fintype.sum_equiv (Equiv.equivCongr e₂ e₁) _ _ fun σ ↦ ?_
  refine Fintype.prod_equiv e₂ _ _ fun i ↦ ?_
  simp [Equiv.equivCongr]

/-- Expand the permanent along an arbitrary column using order-preserving minors.
No alternating signs occur. -/
theorem permanent_succ_column {R : Type*} [CommSemiring R] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (k : Fin (n + 1)) :
    A.permanent = ∑ j, A j k * (A.submatrix j.succAbove k.succAbove).permanent := by
  classical
  have hzero (B : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
      B.permanent = ∑ j, B j 0 * (B.submatrix j.succAbove Fin.succ).permanent := by
    calc
      _ = ∑ j, B j 0 *
          (B.submatrix (fun i ↦ Equiv.swap 0 j i.succ) Fin.succ).permanent := by
        simp only [permanent, Finset.univ_perm_fin_succ, Finset.sum_map,
          Function.Embedding.coeFn_mk, Fintype.sum_prod_type, Fin.prod_univ_succ,
          Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
          Finset.mul_sum, submatrix_apply]
      _ = _ := by
        refine Finset.sum_congr rfl fun j _ ↦ congrArg (B j 0 * ·) ?_
        refine Fin.cases ?_ (fun i ↦ ?_) j
        · simp
        · simpa only [submatrix_submatrix, Function.comp_def, Fin.succAbove_cycleRange,
            id_eq] using permanent_permute_cols i.cycleRange
              (B.submatrix i.succ.succAbove Fin.succ)
  rw [← permanent_permute_rows k.cycleRange.symm A, hzero]
  simp only [submatrix_apply, id_eq, Fin.cycleRange_symm_zero, submatrix_submatrix,
    Function.comp_def, Fin.cycleRange_symm_succ]

end Matrix
