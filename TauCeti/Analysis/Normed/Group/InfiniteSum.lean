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

For an absolutely summable sequence `r`, the sum of any injective subfamily `l ↦ r (φ l)` indexed
at or beyond `N` is bounded in norm by the tail `∑' k, ‖r (k + N)‖`
(`TauCeti.norm_tsum_comp_le_tsum_norm_add`).
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

/-- The sum of an injective subfamily of an absolutely summable sequence, indexed at or beyond `N`,
is bounded in norm by the tail of the sequence from `N` on. -/
theorem norm_tsum_comp_le_tsum_norm_add {E : Type*} [SeminormedAddCommGroup E] {r : ℕ → E}
    (hr : Summable fun k ↦ ‖r k‖) {φ : ℕ → ℕ} (hφ : Function.Injective φ) {N : ℕ}
    (hN : ∀ l, N ≤ φ l) :
    ‖∑' l, r (φ l)‖ ≤ ∑' k, ‖r (k + N)‖ := by
  have hrφ : Summable fun l ↦ ‖r (φ l)‖ := hr.comp_injective hφ
  have hinj : Function.Injective fun l ↦ φ l - N := fun l l' h ↦
    hφ (by have := hN l; have := hN l'; simp only at h; omega)
  refine (norm_tsum_le_tsum_norm hrφ).trans (hrφ.tsum_le_tsum_of_inj _ hinj
    (fun _ _ ↦ norm_nonneg _) (fun l ↦ by rw [Nat.sub_add_cancel (hN l)]) ?_)
  exact (summable_nat_add_iff (f := fun k ↦ ‖r k‖) N).2 hr

end TauCeti
