/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.Algebra.Group.Neighborhood

/-!
# Open additive maps with bounded lifts

An additive map between seminormed groups is open if every element has a preimage
whose norm is bounded by a fixed multiple of its norm, provided the domain is a topological
additive group. Neither continuity nor completeness is required. This criterion turns
norm-controlled lifts into quotient-topology comparisons.
-/

public section

namespace TauCeti

/-- An additive map between seminormed groups with uniformly norm-bounded lifts
is open when its domain is a topological additive group. -/
theorem isOpenMap_of_exists_norm_le {E F 𝓕 : Type*}
    [SeminormedAddGroup E] [IsTopologicalAddGroup E] [SeminormedAddGroup F] [FunLike 𝓕 E F]
    [AddMonoidHomClass 𝓕 E F] (f : 𝓕) {K : ℝ}
    (h : ∀ y, ∃ x, f x = y ∧ ‖x‖ ≤ K * ‖y‖) : IsOpenMap f := by
  let L := max K 1
  have hL : 0 < L := lt_max_of_lt_right one_pos
  apply IsTopologicalAddGroup.isOpenMap_iff_nhds_zero.mpr
  refine (Metric.nhds_basis_ball.le_basis_iff
    (Metric.nhds_basis_ball.map f)).mpr ?_
  intro ε hε
  refine ⟨ε / L, div_pos hε hL, ?_⟩
  intro y hy
  obtain ⟨x, hx, hxn⟩ := h y
  refine ⟨x, ?_, hx⟩
  have hy' : ‖y‖ < ε / L := by
    simpa only [Metric.mem_ball, dist_zero_right] using hy
  have hx' : ‖x‖ < ε := calc
    ‖x‖ ≤ L * ‖y‖ :=
      hxn.trans (mul_le_mul_of_nonneg_right (le_max_left K 1) (norm_nonneg y))
    _ < ε := by
      simpa only [mul_comm] using (lt_div_iff₀ hL).mp hy'
  simpa only [Metric.mem_ball, dist_zero_right] using hx'

end TauCeti
