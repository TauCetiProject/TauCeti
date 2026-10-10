/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Partial sums of a family with at most one nonzero term

If a family `u` in a seminormed group has at most one nonzero term, then every finite partial sum
is either the whole sum or zero, so it differs from `∑' i, u i` by at most `‖∑' i, u i‖ₑ`
(`Set.Subsingleton.enorm_sum_sub_tsum_le`). Such a uniform bound on the partial sums is what
dominated convergence needs to pass from pointwise to `Lᵖ` convergence of a sum of functions with
pairwise disjoint supports.
-/

public section

/-- If a family has at most one nonzero term, each finite partial sum differs from the sum by at
most the extended norm of the sum. -/
theorem Set.Subsingleton.enorm_sum_sub_tsum_le {κ E : Type*} [SeminormedAddCommGroup E]
    {u : κ → E} (hu : (Function.support u).Subsingleton) (s : Finset κ) :
    ‖∑ i ∈ s, u i - ∑' i, u i‖ₑ ≤ ‖∑' i, u i‖ₑ := by
  rcases hu.eq_empty_or_singleton with h | ⟨i, h⟩
  · simp [Function.support_eq_empty_iff.1 h]
  · have hi (j : κ) (hj : j ≠ i) : u j = 0 :=
      Function.notMem_support.1 fun h' => hj (by simpa [h] using h')
    rw [tsum_eq_single i hi]
    by_cases his : i ∈ s
    · simp [Finset.sum_eq_single_of_mem i his fun j _ => hi j, enorm_eq_nnnorm]
    · rw [Finset.sum_eq_zero fun j hj => hi j fun h => his (h ▸ hj), zero_sub, enorm_neg]
