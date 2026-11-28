/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.EntrywiseOpNorm

/-!
# Uniform entry bounds for the Euclidean operator norm

The finite Schur test turns a uniform bound on the entries of a square matrix into an
operator norm bound linear in its dimension.
-/

public section

open scoped Matrix.Norms.L2Operator

namespace Matrix

/-- An `n × n` matrix with entries of norm at most `R` has Euclidean operator norm at most
`n * R`. For empty matrices this is also valid when `R` is negative. -/
theorem l2_opNorm_le_card_mul_of_norm_apply_le {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]
    [DecidableEq n] (A : Matrix n n 𝕜) {R : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ R) :
    ‖A‖ ≤ (Fintype.card n : ℝ) * R := by
  rcases isEmpty_or_nonempty n with h | ⟨⟨i⟩⟩
  · rw [Subsingleton.elim A 0, norm_zero, Fintype.card_of_isEmpty, Nat.cast_zero, zero_mul]
  have hR := (norm_nonneg (A i i)).trans (hA i i)
  have hs (a : n → ℝ) (ha : ∀ i, a i ≤ R) : ∑ i, a i ≤ (Fintype.card n : ℝ) * R :=
    (Finset.sum_le_sum fun i _ ↦ ha i).trans_eq (by simp)
  simpa only [← sq, Real.sqrt_sq (mul_nonneg (Nat.cast_nonneg _) hR)] using
    A.l2_opNorm_le_sqrt_mul_of_row_col_sum_le (fun i ↦ hs _ (hA i)) (fun j ↦ hs _ (hA · j))

end Matrix
