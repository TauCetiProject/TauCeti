/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.GroupTheory.Perm.Fin

/-!
# Expansion of the permanent along a column

The permanent expands along its first column by deleting that column and each possible row.
The deleted row is exchanged with row zero before taking the remaining rows. This convention
matches the decomposition of permutations in `Equiv.Perm.decomposeFin` and is useful when
iterating Gaussian covariance contractions.
-/

public section

namespace Matrix

/-- Expand the permanent along column zero. Each minor first exchanges the selected row
with row zero, then deletes row and column zero. No alternating signs occur. -/
theorem permanent_fin_succ {R : Type*} [CommSemiring R] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    A.permanent = ∑ j, A j 0 *
      (A.submatrix (fun i ↦ Equiv.swap 0 j i.succ) Fin.succ).permanent := by
  classical
  simp only [permanent, Finset.univ_perm_fin_succ, Finset.sum_map,
    Function.Embedding.coeFn_mk, Fintype.sum_prod_type, Fin.prod_univ_succ,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Finset.mul_sum, submatrix_apply]

/-- Reindexing both axes by the same equivalence preserves the permanent. -/
theorem permanent_submatrix_equiv {R α β : Type*} [CommSemiring R] [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (A : Matrix β β R) (e : α ≃ β) :
    (A.submatrix e e).permanent = A.permanent := by
  unfold Matrix.permanent
  refine Fintype.sum_equiv (Equiv.permCongr e) _ _ fun σ ↦ ?_
  refine Fintype.prod_equiv e _ _ fun i ↦ ?_
  simp [Equiv.permCongr_apply]

end Matrix
