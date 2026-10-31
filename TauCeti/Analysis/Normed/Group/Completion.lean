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
differences. Applied to the completion of an algebraic tensor product, this is the step that turns
finite decompositions of algebraic tensors into series decompositions of completed tensors.

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
  set ε := (c - ‖u‖) / 8 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  -- Successive approximations `a n` of `u` with errors `η n = ε / 2 / 2 ^ n`.
  set η : ℕ → ℝ := fun n ↦ ε / 2 / 2 ^ n with hη_def
  have hη_pos (n : ℕ) : 0 < η n := by positivity
  have hη_succ (n : ℕ) : η n = 2 * η (n + 1) := by
    simp only [hη_def, pow_succ]; field_simp
  choose a ha using fun n ↦ denseRange_coe.exists_dist_lt u (hη_pos n)
  -- The series of consecutive differences of the approximations.
  set v : ℕ → V := fun n ↦ a n - if n = 0 then 0 else a (n - 1) with hv_def
  have hv_sum (n : ℕ) : ∑ i ∈ Finset.range (n + 1), v i = a n := by
    induction n with
    | zero => simp [hv_def]
    | succ n ih => rw [Finset.sum_range_succ, ih]; simp [hv_def]
  -- Bound for the norms of the terms.
  set g : ℕ → ℝ := fun n ↦ (if n = 0 then ‖u‖ else 0) + 4 * η n with hg_def
  have hg : HasSum g (‖u‖ + 4 * ε) :=
    (hasSum_ite_eq 0 ‖u‖).add ((hasSum_geometric_two' ε).mul_left 4)
  have hva (n : ℕ) : ‖(a n : Completion V) - u‖ < η n := by
    rw [← dist_eq_norm, dist_comm]; exact ha n
  have hle (n : ℕ) : ‖v n‖ ≤ g n := by
    rcases n with _ | n
    · have h := norm_le_norm_add_norm_sub' (a 0 : Completion V) u
      simp only [norm_coe] at h
      have := hva 0
      simp only [hv_def, hg_def, ite_true, sub_zero]
      linarith [hη_pos 0]
    · have h := norm_sub_le_norm_sub_add_norm_sub (a (n + 1) : Completion V) u (a n)
      rw [← coe_sub, norm_coe, norm_sub_rev u] at h
      have h₁ := hva (n + 1)
      have h₂ := hva n
      simp only [hv_def, hg_def, Nat.add_one_ne_zero, ite_false, add_tsub_cancel_right, zero_add]
      linarith [hη_succ n, hη_pos (n + 1)]
  have hvs : Summable fun n ↦ ‖v n‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle hg.summable
  refine ⟨v, ?_, hvs, ?_⟩
  · refine (hasSum_iff_tendsto_nat_of_summable_norm (by simpa using hvs)).2 ?_
    refine (tendsto_add_atTop_iff_nat 1).1 ?_
    simp_rw [← toCompl_apply, ← map_sum (toCompl : V →+ Completion V), hv_sum, toCompl_apply]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ (hva n).le) ?_
    exact tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  · calc ∑' n, ‖v n‖ ≤ ‖u‖ + 4 * ε := hasSum_le hle hvs.hasSum hg
      _ < c := by rw [hε_def]; linarith

end UniformSpace.Completion
