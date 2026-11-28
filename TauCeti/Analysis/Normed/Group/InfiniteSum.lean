/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import TauCeti.Topology.Algebra.InfiniteSum.Constructions

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

`TauCeti.tsum_norm_sum_elim_const_ofLex` evaluates the norm sum of a summable family extended by a
constant finite branch over `ι ⊕ₗ κ`, and `TauCeti.sum_subtype_norm_le_tsum` bounds the sum of
norms over a finite subset by the total norm sum.
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

/-- Norm sum of an absolutely summable family extended by a constant finite branch over `ι ⊕ₗ κ`. -/
theorem tsum_norm_sum_elim_const_ofLex {ι κ E : Type*} [Fintype κ] [SeminormedAddCommGroup E]
    {f : ι → E} (hf : Summable fun a ↦ ‖f a‖) (c : E) :
    (∑' a : ι ⊕ₗ κ, ‖Sum.elim f (fun _ ↦ c) (ofLex a)‖) =
      (∑' a, ‖f a‖) + (Fintype.card κ : ℝ) * ‖c‖ := by
  have hcongr : (fun a : ι ⊕ₗ κ ↦ ‖Sum.elim f (fun _ ↦ c) (ofLex a)‖) =
      fun a ↦ Sum.elim (fun i ↦ ‖f i‖) (fun _ ↦ ‖c‖) (ofLex a) := by ext a; cases ofLex a <;> rfl
  rw [hcongr, hf.tsum_sumLex_elim_const, nsmul_eq_mul]

/-- For a family with summable norms, the sum of norms over any finite subtype is at most the total
norm sum. -/
theorem sum_subtype_norm_le_tsum {E ι : Type*} [SeminormedAddCommGroup E] {p : ι → E}
    (hp : Summable fun a ↦ ‖p a‖) (s : Finset ι) : ∑ a : s, ‖p a‖ ≤ ∑' a, ‖p a‖ := by
  rw [Finset.univ_eq_attach, s.sum_attach fun a ↦ ‖p a‖]
  exact hp.sum_le_tsum s fun _ _ ↦ norm_nonneg _

end TauCeti
