/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.HardThreshold
public import TauCeti.Probability.RandomMatrix.Wigner.Basic

/-!
# Discarded entries of a truncated Wigner corner

Truncating the upper entries of a zero-diagonal Wigner corner at an unnormalized cutoff discards
exactly the normalized entries above that cutoff divided by the square root of the dimension. The
discarded matrix is therefore the entrywise hard threshold of the corner, whose operator norm is
controlled by the hard-threshold bounds for Hermitian matrices.
-/

public section

open Set
open scoped NNReal

namespace TauCeti.Probability

variable {Ω : Type*} {ξ : StrictUpper → Ω → ℂ}

/-- The discarded part of a zero-diagonal Wigner corner is exactly the entrywise
hard threshold at the cutoff divided by the square root of the dimension. -/
theorem wignerMatrix_zero_sub_indicator_eq_hardThreshold {n : ℕ}
    (r : ℝ≥0) (ω : Ω) :
    wignerMatrix ξ (fun _ _ ↦ 0) n ω -
      wignerMatrix (fun ij ↦ {ω' | ‖ξ ij ω'‖ ≤ r}.indicator (ξ ij)) (fun _ _ ↦ 0) n ω =
    (wignerMatrix ξ (fun _ _ ↦ 0) n ω).hardThreshold (r / Real.sqrt n) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.hardThreshold_apply]
  simp only [wignerMatrix_sub, Matrix.hardThreshold_apply,
    div_lt_norm_wignerMatrix_apply_iff _ _ _ hij]
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · simp only [wignerMatrix_apply_of_lt _ _ _ h, min_eq_left h.le, max_eq_right h.le,
      indicator_apply, mem_ofPred_eq, ← not_lt, ite_not]
    split_ifs <;> simp
  · simp only [wignerMatrix_apply_of_gt _ _ _ h, min_eq_right h.le, max_eq_left h.le,
      indicator_apply, mem_ofPred_eq, ← not_lt, ite_not]
    split_ifs <;> simp

end TauCeti.Probability
