/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Normed.Module.Convex
import TauCeti.Topology.Frontier

/-!
# Distance to the frontier of a set

In a real seminormed space, the distance from any point `x ∈ closure s` to `frontier s` equals its
distance to `sᶜ`, both in `ℝ≥0∞` (`TauCeti.infEDist_frontier_eq_infEDist_compl`) and in `ℝ`
(`TauCeti.infDist_frontier_eq_infDist_compl`).

One inequality holds topologically because `frontier s ⊆ closure sᶜ`. For the reverse inequality,
when `x ∈ s` and `y ∈ sᶜ`, the segment `segment ℝ x y` is preconnected and straddles `s`, so
`IsPreconnected.inter_frontier_nonempty` yields a point `p ∈ segment ℝ x y ∩ frontier s`, which is
no farther from `x` than `y` by `segment_subset_closedBall_left`; when `x ∈ closure s \ s`, `x`
already belongs to both `frontier s` and `sᶜ`. Because the argument compares infima directly along
segments rather than choosing a nearest complement point, neither completeness nor finite
dimensionality is required, unlike `exists_mem_frontier_infDist_compl_eq_dist`.

This identity converts boundary-distance statements (such as preservation of distance to
`frontier Ω` under holomorphic hulls in `TauCeti/Analysis/Complex/Runge/Hull.lean`) into
complement-distance statements amenable to separation by `(w - ζ)⁻¹` with `ζ ∈ Ωᶜ`.

## Main results

* `TauCeti.infEDist_frontier_eq_infEDist_compl`: for `x ∈ closure s`,
  `infEDist x (frontier s) = infEDist x sᶜ`.
* `TauCeti.infDist_frontier_eq_infDist_compl`: for `x ∈ closure s`,
  `infDist x (frontier s) = infDist x sᶜ`.
-/

public section

namespace TauCeti

open Metric Set

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {x : E}

/-- For any point `x ∈ closure s` in a real seminormed space, the extended distance from `x` to
`frontier s` equals its extended distance to `sᶜ`. -/
theorem infEDist_frontier_eq_infEDist_compl (hx : x ∈ closure s) :
    infEDist x (frontier s) = infEDist x sᶜ := by
  refine le_antisymm ?_ ?_
  · by_cases hxs : x ∈ s
    · refine le_infEDist.mpr fun y hy => ?_
      obtain ⟨p, hp_seg, hp_fr⟩ :=
        (convex_segment x y).isPreconnected.inter_frontier_nonempty
          ⟨x, left_mem_segment ℝ x y, hxs⟩ ⟨y, right_mem_segment ℝ x y, hy⟩
      refine (infEDist_le_edist_of_mem hp_fr).trans ?_
      rw [edist_dist, edist_dist]
      exact ENNReal.ofReal_le_ofReal
        (dist_comm p x ▸ mem_closedBall.mp (segment_subset_closedBall_left x y hp_seg))
    · have hx_fr : x ∈ frontier s := by
        rw [frontier_eq_closure_inter_closure]
        exact ⟨hx, subset_closure (mem_compl hxs)⟩
      simp [infEDist_zero_of_mem hx_fr]
  · rw [← infEDist_closure]
    exact infEDist_anti fun _ hw => by
      rw [frontier_eq_closure_inter_closure] at hw
      exact hw.2

/-- For any point `x ∈ closure s` in a real seminormed space, the real distance from `x` to
`frontier s` equals its real distance to `sᶜ`. -/
theorem infDist_frontier_eq_infDist_compl (hx : x ∈ closure s) :
    infDist x (frontier s) = infDist x sᶜ := by
  rw [infDist, infDist, infEDist_frontier_eq_infEDist_compl hx]

end TauCeti
