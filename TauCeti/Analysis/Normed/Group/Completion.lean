/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Completion
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Absolutely convergent series in the completion of a seminormed group

Every point `u` of the completion of a seminormed group `V` is the sum of a series of points of
`V` whose norms have sum less than any prescribed `c > ‖u‖`. The series is obtained from a
sequence of successive approximations of `u` from the dense image of `V`, by taking consecutive
differences, as provided by `controlled_sum_of_mem_closure_range`. Applied to the completion of an
algebraic tensor product, this is the step that turns finite decompositions of algebraic tensors
into series decompositions of completed tensors.

## Main results

* `UniformSpace.Completion.exists_hasSum_coe_of_norm_lt`: if `‖u‖ < c`, then `u = ∑ n, v n` for
  some `v : ℕ → V` with `∑ n, ‖v n‖ < c`.
-/

public section

open Filter Topology

namespace UniformSpace.Completion

variable {V : Type*} [SeminormedAddCommGroup V]

/-- Every point `u` of the completion of a seminormed group `V` is the sum of a series of points
of `V` whose norms have sum less than any prescribed bound `c > ‖u‖`. -/
theorem exists_hasSum_coe_of_norm_lt (u : Completion V) {c : ℝ} (hu : ‖u‖ < c) :
    ∃ v : ℕ → V, HasSum (fun n ↦ (v n : Completion V)) u ∧ Summable (fun n ↦ ‖v n‖) ∧
      ∑' n, ‖v n‖ < c := by
  set ε := (c - ‖u‖) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  -- Mathlib's successive approximation of `u` from the dense range of `V`, with geometric errors.
  have hmem : u ∈ closure ((toCompl : V →+ Completion V).range : Set (Completion V)) := by
    rw [AddMonoidHom.coe_range]
    exact denseRange_coe u
  obtain ⟨v, hv_lim, hv₀, hv⟩ := controlled_sum_of_mem_closure_range hmem
    (f := fun n ↦ ε / 2 / 2 ^ n) fun n ↦ by positivity
  simp only [toCompl_apply] at hv_lim hv₀ hv
  -- Bound for the norms of the terms.
  set g : ℕ → ℝ := fun n ↦ (if n = 0 then ‖u‖ else 0) + ε / 2 / 2 ^ n with hg_def
  have hg : HasSum g (‖u‖ + ε) := (hasSum_ite_eq 0 ‖u‖).add (hasSum_geometric_two' ε)
  have hle (n : ℕ) : ‖v n‖ ≤ g n := by
    rcases n with _ | n
    · have h := norm_le_norm_add_norm_sub' (v 0 : Completion V) u
      rw [norm_coe] at h
      rw [neg_add_eq_sub, norm_sub_rev] at hv₀
      simp only [hg_def, ite_true]
      linarith
    · simpa [hg_def, norm_coe] using (hv (n + 1) n.succ_pos).le
  have hvs : Summable fun n ↦ ‖v n‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle hg.summable
  refine ⟨v, ?_, hvs, ?_⟩
  · refine (hasSum_iff_tendsto_nat_of_summable_norm (by simpa using hvs)).2 ?_
    exact (tendsto_add_atTop_iff_nat 1).1 hv_lim
  · calc ∑' n, ‖v n‖ ≤ ‖u‖ + ε := hasSum_le hle hvs.hasSum hg
      _ < c := by rw [hε_def]; linarith

end UniformSpace.Completion
