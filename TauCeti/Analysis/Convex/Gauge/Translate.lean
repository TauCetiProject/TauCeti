/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Gauge
public import TauCeti.Analysis.LocallyConvex.Bounded
public import TauCeti.Topology.Algebra.Group.Neighborhood

/-!
# The gauge centred at a point

The gauge of a set `s` centred at a point `p` is the gauge of the translate
`(p + ·) ⁻¹' s = {v | p + v ∈ s}`, evaluated at `x - p`. This file transports the basic
properties of Mathlib's gauge, which is centred at `0`, to an arbitrary centre `p`, using the
translation lemmas `TauCeti.preimage_add_mem_nhds_zero` and `TauCeti.frontier_preimage_add` from
`TauCeti.Topology.Algebra.Group.Neighborhood`:

* `TauCeti.gauge_preimage_add_sub_pos_iff`: for a bounded neighbourhood of `p` the gauge centred
  at `p` is positive exactly off `p`, using `Bornology.IsVonNBounded.preimage_add` from
  `TauCeti.Analysis.LocallyConvex.Bounded`;
* `TauCeti.gauge_preimage_add_sub_eq_one_iff_mem_frontier`: for a convex neighbourhood of `p` the
  gauge centred at `p` takes the value one exactly on the frontier;
* `TauCeti.le_gauge_preimage_add_of_subset_closedBall`: if `s ⊆ closedBall p R`, the gauge
  centred at `p` is at least `‖x - p‖ / R`;
* `Convex.lipschitzWith_gauge_preimage_add`: if `ball p r ⊆ s` for a convex `s`, the gauge
  centred at `p` is `r⁻¹`-Lipschitz.
-/

public section

open Set Metric Topology Bornology
open scoped NNReal

namespace TauCeti

section TopologicalVectorSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {s : Set E} {p x : E}

/-- The gauge of a von Neumann bounded neighbourhood `s` of `p`, centred at `p`, is positive
exactly off `p`. -/
theorem gauge_preimage_add_sub_pos_iff [T1Space E] (hp : s ∈ 𝓝 p) (hb : IsVonNBounded ℝ s) :
    0 < gauge ((p + ·) ⁻¹' s) (x - p) ↔ x ≠ p := by
  rw [gauge_pos (absorbent_nhds_zero (preimage_add_mem_nhds_zero hp))
    (hb.preimage_add p), sub_ne_zero]

/-- A point lies on the frontier of a convex neighbourhood `s` of `p` exactly when the gauge of `s`
centred at `p` takes the value one there. -/
theorem gauge_preimage_add_sub_eq_one_iff_mem_frontier (hs : Convex ℝ s) (hp : s ∈ 𝓝 p) :
    gauge ((p + ·) ⁻¹' s) (x - p) = 1 ↔ x ∈ frontier s := by
  rw [gauge_eq_one_iff_mem_frontier (hs.translate_preimage_right p)
    (preimage_add_mem_nhds_zero hp), frontier_preimage_add]
  simp

end TopologicalVectorSpace

/-- If a neighbourhood `s` of `p` lies in `closedBall p R`, the gauge of `s` centred at `p` is at
least `‖x - p‖ / R`. -/
theorem le_gauge_preimage_add_of_subset_closedBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set E} {p x : E} {R : ℝ} (hp : s ∈ 𝓝 p) (hR : s ⊆ closedBall p R) :
    ‖x - p‖ / R ≤ gauge ((p + ·) ⁻¹' s) (x - p) :=
  le_gauge_of_subset_closedBall (absorbent_nhds_zero (preimage_add_mem_nhds_zero hp))
    (by simpa using hR (mem_of_mem_nhds hp)) fun v hv ↦ by
      simpa [dist_eq_norm] using hR hv

end TauCeti

/-- If `ball p r ⊆ s` for a convex `s` and `r > 0`, the gauge of `s` centred at `p` is
`r⁻¹`-Lipschitz. -/
theorem Convex.lipschitzWith_gauge_preimage_add {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set E} {p : E} {r : ℝ≥0} (hs : Convex ℝ s) (hr : 0 < r)
    (hball : ball p r ⊆ s) : LipschitzWith r⁻¹ (gauge ((p + ·) ⁻¹' s)) :=
  (hs.translate_preimage_right p).lipschitzWith_gauge hr fun v hv ↦
    hball (by simpa [mem_ball, dist_eq_norm] using hv)
