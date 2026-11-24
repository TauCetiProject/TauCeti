/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Gauge

/-!
# The gauge centred at a point

The gauge of a set `s` centred at a point `p` is the gauge of the translate
`(p + ·) ⁻¹' s = {v | p + v ∈ s}`, evaluated at `x - p`. This file transports the basic
properties of Mathlib's gauge, which is centred at `0`, to an arbitrary centre `p`:

* `TauCeti.preimage_add_mem_nhds_zero`, `TauCeti.isVonNBounded_preimage_add`,
  `TauCeti.frontier_preimage_add`: translating a neighbourhood of `p`, a von Neumann bounded set
  and a frontier by `p`;
* `TauCeti.gauge_preimage_add_sub_pos_iff`: for a bounded neighbourhood of `p` the gauge centred
  at `p` is positive exactly off `p`;
* `TauCeti.gauge_preimage_add_sub_eq_one_iff_mem_frontier`: for a convex neighbourhood of `p` the
  gauge centred at `p` takes the value one exactly on the frontier;
* `Convex.lipschitzWith_gauge_preimage_add`: if `ball p r ⊆ s` for a convex `s`, the gauge
  centred at `p` is `r⁻¹`-Lipschitz.
-/

public section

open Set Metric Topology Bornology
open scoped NNReal

namespace TauCeti

section TopologicalAddGroup

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] {s : Set E}
  {p : E}

/-- The translate of a neighbourhood of `p` by `p` is a neighbourhood of `0`. -/
theorem preimage_add_mem_nhds_zero (hp : s ∈ 𝓝 p) : (p + ·) ⁻¹' s ∈ 𝓝 (0 : E) :=
  (continuous_const_add p).continuousAt.preimage_mem_nhds (by simpa using hp)

/-- The frontier of the translate of `s` by `p` is the translate of the frontier of `s`. -/
theorem frontier_preimage_add (s : Set E) (p : E) :
    frontier ((p + ·) ⁻¹' s) = (p + ·) ⁻¹' frontier s :=
  ((Homeomorph.addLeft p).preimage_frontier s).symm

end TopologicalAddGroup

section TopologicalVectorSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {s : Set E} {p x : E}

/-- The translate of a von Neumann bounded set is von Neumann bounded. -/
theorem isVonNBounded_preimage_add (hb : IsVonNBounded ℝ s) (p : E) :
    IsVonNBounded ℝ ((p + ·) ⁻¹' s) := by
  simpa [← image_vadd, image_add_left] using hb.vadd (-p)

/-- The gauge of a von Neumann bounded neighbourhood `s` of `p`, centred at `p`, is positive
exactly off `p`. -/
theorem gauge_preimage_add_sub_pos_iff [T1Space E] (hp : s ∈ 𝓝 p) (hb : IsVonNBounded ℝ s) :
    0 < gauge ((p + ·) ⁻¹' s) (x - p) ↔ x ≠ p := by
  rw [gauge_pos (absorbent_nhds_zero (preimage_add_mem_nhds_zero hp))
    (isVonNBounded_preimage_add hb p), sub_ne_zero]

/-- A point lies on the frontier of a convex neighbourhood `s` of `p` exactly when the gauge of `s`
centred at `p` takes the value one there. -/
theorem gauge_preimage_add_sub_eq_one_iff_mem_frontier (hs : Convex ℝ s) (hp : s ∈ 𝓝 p) :
    gauge ((p + ·) ⁻¹' s) (x - p) = 1 ↔ x ∈ frontier s := by
  rw [gauge_eq_one_iff_mem_frontier (hs.translate_preimage_right p)
    (preimage_add_mem_nhds_zero hp), frontier_preimage_add]
  simp

end TopologicalVectorSpace

end TauCeti

/-- If `ball p r ⊆ s` for a convex `s` and `r > 0`, the gauge of `s` centred at `p` is
`r⁻¹`-Lipschitz. -/
theorem Convex.lipschitzWith_gauge_preimage_add {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] {s : Set E} {p : E} {r : ℝ≥0} (hs : Convex ℝ s) (hr : 0 < r)
    (hball : ball p r ⊆ s) : LipschitzWith r⁻¹ (gauge ((p + ·) ⁻¹' s)) :=
  (hs.translate_preimage_right p).lipschitzWith_gauge hr fun v hv ↦
    hball (by simpa [mem_ball, dist_eq_norm] using hv)
