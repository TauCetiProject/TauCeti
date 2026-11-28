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

For families `f` and `y` in seminormed groups with `∑ i, ‖f i‖ * ‖y i‖` summable, the extended sum
`∑' i, ‖f i‖ₑ * ‖y i‖ₑ` is the extended real `ENNReal.ofReal (∑' i, ‖f i‖ * ‖y i‖)`
(`TauCeti.tsum_enorm_mul_enorm_eq_ofReal`).

A family whose finite partial sums are not Cauchy, for instance a non-summable family in a complete
space, has pairwise disjoint finite blocks whose sums all have norm at least some fixed `ε > 0`
(`TauCeti.exists_pairwise_disjoint_le_norm_sum_of_not_cauchySeq`). Each block is chosen disjoint
from the union of the previous ones, through Mathlib's `exists_seq_of_forall_finset_exists'`.
-/

public section

/-- If a family has at most one nonzero term, each finite partial sum differs from the sum by at
most the extended norm of the sum. -/
theorem Set.Subsingleton.enorm_sum_sub_tsum_le {κ E : Type*} [SeminormedAddCommGroup E]
    {u : κ → E} (hu : (Function.support u).Subsingleton) (s : Finset κ) :
    ‖∑ i ∈ s, u i - ∑' i, u i‖ₑ ≤ ‖∑' i, u i‖ₑ := by
  classical
  rcases hu.eq_empty_or_singleton with h | ⟨i, h⟩
  · simp [Function.support_eq_empty_iff.1 h]
  have hi : ∀ j ≠ i, u j = 0 := Function.support_subset_iff'.1 h.subset
  rw [tsum_eq_single i hi, Finset.sum_eq_ite i fun j _ => hi j]
  split_ifs <;> simp

namespace TauCeti

/-- If `∑ i, ‖f i‖ * ‖y i‖` is summable, the extended sum `∑' i, ‖f i‖ₑ * ‖y i‖ₑ` is its real sum
viewed as an extended real. -/
theorem tsum_enorm_mul_enorm_eq_ofReal {ι G H : Type*} [SeminormedAddGroup G]
    [SeminormedAddGroup H] {f : ι → G} {y : ι → H}
    (hfy : Summable fun i ↦ ‖f i‖ * ‖y i‖) :
    ∑' i, ‖f i‖ₑ * ‖y i‖ₑ = ENNReal.ofReal (∑' i, ‖f i‖ * ‖y i‖) := by
  simp [ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hfy, ENNReal.ofReal_mul]

open Function in
/-- A family whose finite partial sums are not Cauchy has pairwise disjoint finite blocks whose
sums all have norm at least some fixed `ε > 0`. -/
theorem exists_pairwise_disjoint_le_norm_sum_of_not_cauchySeq {ι E : Type*}
    [SeminormedAddCommGroup E] {x : ι → E} (hx : ¬CauchySeq fun s : Finset ι ↦ ∑ i ∈ s, x i) :
    ∃ ε > 0, ∃ t : ℕ → Finset ι, Pairwise (Disjoint on t) ∧ ∀ k, ε ≤ ‖∑ i ∈ t k, x i‖ := by
  classical
  rw [cauchySeq_finset_iff_vanishing_norm] at hx
  push Not at hx
  obtain ⟨ε, hε, hT⟩ := hx
  -- Each new block avoids the union of the finitely many blocks chosen before it.
  obtain ⟨t, htε, ht⟩ := exists_seq_of_forall_finset_exists'
    (fun t : Finset ι ↦ ε ≤ ‖∑ i ∈ t, x i‖) Disjoint fun s _ ↦ by
      obtain ⟨t, hts, htε⟩ := hT (s.biUnion id)
      exact ⟨t, htε, (Finset.disjoint_biUnion_left s id t).1 hts.symm⟩
  exact ⟨ε, hε, t, ht, htε⟩

end TauCeti
