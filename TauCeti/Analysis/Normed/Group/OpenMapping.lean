/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Open additive maps with bounded lifts

An additive map between seminormed groups is open if every element has a preimage
whose norm is bounded by a fixed multiple of its norm. Neither continuity nor completeness is
required. This criterion turns
norm-controlled lifts into quotient-topology comparisons.
-/

public section

namespace TauCeti

/-- An additive map between seminormed groups with uniformly norm-bounded lifts is open. -/
theorem isOpenMap_of_exists_norm_le {E F 𝓕 : Type*}
    [SeminormedAddGroup E] [SeminormedAddGroup F] [FunLike 𝓕 E F]
    [AddMonoidHomClass 𝓕 E F] (f : 𝓕) {K : ℝ}
    (h : ∀ y, ∃ x, f x = y ∧ ‖x‖ ≤ K * ‖y‖) : IsOpenMap f := by
  let L := max K 1
  have hL : 0 < L := lt_max_of_lt_right one_pos
  intro U hU
  rw [Metric.isOpen_iff] at hU ⊢
  rintro _ ⟨x, hxU, rfl⟩
  obtain ⟨r, hr, hrU⟩ := hU x hxU
  refine ⟨r / L, div_pos hr hL, fun y hy => ?_⟩
  obtain ⟨z, hz, hzn⟩ := h (-f x + y)
  refine ⟨x + z, hrU ?_, by rw [map_add, hz, add_neg_cancel_left]⟩
  have hy' : ‖-f x + y‖ < r / L := by
    rw [← dist_eq_norm_neg_add]
    exact Metric.mem_ball'.1 hy
  rw [Metric.mem_ball', dist_eq_norm_neg_add, neg_add_cancel_left]
  calc ‖z‖ ≤ L * ‖-f x + y‖ :=
      hzn.trans (mul_le_mul_of_nonneg_right (le_max_left K 1) (norm_nonneg _))
    _ < r := by simpa only [mul_comm] using (lt_div_iff₀ hL).mp hy'

end TauCeti
