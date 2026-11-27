/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix

/-!
# Entrywise bounds for the norm of a C⋆-matrix

* `CStarMatrix.norm_le_sum_norm_entry`: `‖M‖ ≤ Σ j, Σ i, ‖M i j‖`.
* `CStarMatrix.norm_le_card_mul_of_forall_norm_entry_le`: if every entry of `M` has norm at most
  `ε`, then `‖M‖ ≤ card m * card n * ε`.
-/

public section

namespace CStarMatrix

open WithCStarModule

variable {m n A : Type*} [Fintype m] [Fintype n] [NonUnitalCStarAlgebra A] [PartialOrder A]
  [StarOrderedRing A]

/-- The norm of a matrix over a C⋆-algebra is at most the sum of the norms of its entries. The
statement and proof are the first step of the private `CStarMatrix.antilipschitzWith_toMatrixAux`
in `Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean`. -/
theorem norm_le_sum_norm_entry (M : CStarMatrix m n A) : ‖M‖ ≤ ∑ j, ∑ i, ‖M i j‖ := by
  rw [norm_def]
  refine (toCLM M).opNorm_le_bound (by positivity) fun v => ?_
  simp only [toCLM_apply_eq_sum, Finset.sum_mul]
  refine (pi_norm_le_sum_norm _).trans ?_
  gcongr with j _
  refine (norm_sum_le _ _).trans ?_
  gcongr with i _
  refine (norm_mul_le _ _).trans ?_
  rw [mul_comm]
  gcongr
  exact norm_apply_le_norm v i

/-- If every entry of a matrix has norm at most `ε`, its norm is at most `card m * card n * ε`. -/
theorem norm_le_card_mul_of_forall_norm_entry_le (M : CStarMatrix m n A) {ε : ℝ}
    (h : ∀ i j, ‖M i j‖ ≤ ε) : ‖M‖ ≤ Fintype.card m * Fintype.card n * ε := by
  refine (norm_le_sum_norm_entry M).trans ?_
  calc ∑ j, ∑ i, ‖M i j‖ ≤ ∑ _j : n, ∑ _i : m, ε := by gcongr with j _ i _; exact h i j
    _ = _ := by simp [Finset.card_univ]; ring

end CStarMatrix
