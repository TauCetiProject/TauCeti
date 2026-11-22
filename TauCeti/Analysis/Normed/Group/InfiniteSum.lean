/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Partial sums and series approximations in seminormed groups

If a family `u` in a seminormed group has at most one nonzero term, then every finite partial sum
is either the whole sum or zero, so it differs from `∑' i, u i` by at most `‖∑' i, u i‖ₑ`
(`Set.Subsingleton.enorm_sum_sub_tsum_le`). Such a uniform bound on the partial sums is what
dominated convergence needs to pass from pointwise to `Lᵖ` convergence of a sum of functions with
pairwise disjoint supports.

For families `f` and `y` in seminormed groups with `∑ i, ‖f i‖ * ‖y i‖` summable, the extended sum
`∑' i, ‖f i‖ₑ * ‖y i‖ₑ` is the extended real `ENNReal.ofReal (∑' i, ‖f i‖ * ‖y i‖)`
(`TauCeti.tsum_enorm_mul_enorm_eq_ofReal`).

Every point `u` in the target of an additive homomorphism `f : V →+ W` with dense range is the sum
of a series `∑ n, f (v n)` whose image norms have sum less than any prescribed `c > ‖u‖`
(`DenseRange.exists_hasSum_norm_lt`).
-/

public section

open Filter Topology

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

/-- Every point `u` in the target of an additive homomorphism `f : V →+ W` with dense range is the
sum of a series `∑ n, f (v n)` whose image norms have sum less than any prescribed bound `c > ‖u‖`.
-/
theorem DenseRange.exists_hasSum_norm_lt {V W : Type*} [AddGroup V]
    [SeminormedAddCommGroup W] {f : V →+ W} (hf : DenseRange f) (u : W) {c : ℝ}
    (hu : ‖u‖ < c) :
    ∃ v : ℕ → V, HasSum (fun n ↦ f (v n)) u ∧ Summable (fun n ↦ ‖f (v n)‖) ∧
      ∑' n, ‖f (v n)‖ < c := by
  set ε := (c - ‖u‖) / 2 with hε_def
  have : 0 < ε := by rw [hε_def]; linarith
  have hmem : u ∈ closure (f.range : Set W) := by
    rw [AddMonoidHom.coe_range]
    exact hf u
  obtain ⟨w, hw_lim, hw_mem, hw₀, hw⟩ := controlled_sum_of_mem_closure hmem
    (b := fun n ↦ ε / 2 / 2 ^ n) fun n ↦ by positivity
  choose v hv using hw_mem
  have hfw (n : ℕ) : f (v n) = w n := hv n
  set g : ℕ → ℝ := fun n ↦ (if n = 0 then ‖u‖ else 0) + ε / 2 / 2 ^ n with hg_def
  have hg : HasSum g (‖u‖ + ε) := (hasSum_ite_eq 0 ‖u‖).add (hasSum_geometric_two' ε)
  have hle (n : ℕ) : ‖f (v n)‖ ≤ g n := by
    rw [hfw n]
    rcases n with _ | n
    · have h := norm_le_norm_add_norm_sub' (w 0) u
      rw [neg_add_eq_sub, norm_sub_rev] at hw₀
      simp only [hg_def, ite_true]
      linarith
    · simpa [hg_def] using (hw (n + 1) n.succ_pos).le
  have hvs : Summable fun n ↦ ‖f (v n)‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle hg.summable
  refine ⟨v, ?_, hvs, ?_⟩
  · refine (hasSum_iff_tendsto_nat_of_summable_norm hvs).2 ?_
    simpa only [hfw] using (tendsto_add_atTop_iff_nat 1).1 hw_lim
  · calc ∑' n, ‖f (v n)‖ ≤ ‖u‖ + ε := hasSum_le hle hvs.hasSum hg
      _ < c := by rw [hε_def]; linarith

namespace TauCeti

/-- If `∑ i, ‖f i‖ * ‖y i‖` is summable, the extended sum `∑' i, ‖f i‖ₑ * ‖y i‖ₑ` is its real sum
viewed as an extended real. -/
theorem tsum_enorm_mul_enorm_eq_ofReal {ι G H : Type*} [SeminormedAddGroup G]
    [SeminormedAddGroup H] {f : ι → G} {y : ι → H}
    (hfy : Summable fun i ↦ ‖f i‖ * ‖y i‖) :
    ∑' i, ‖f i‖ₑ * ‖y i‖ₑ = ENNReal.ofReal (∑' i, ‖f i‖ * ‖y i‖) := by
  simp [ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hfy, ENNReal.ofReal_mul]

end TauCeti
