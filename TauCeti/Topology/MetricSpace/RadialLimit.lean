/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# A radial limit and shrinking sphere images determine a puncture limit

If the images of small spheres about a point have diameter tending to zero, convergence
along one radius determines convergence along every approach to the point. Boundedness of
those images is explicit: the real-valued diameter of an unbounded set has junk value zero.

This is the metric step in continuous removal of isolated singularities, separating radial
convergence from the estimates controlling angular oscillation. It works in any real normed
source and any pseudo-metric target.
-/

public section

namespace TauCeti

open Bornology Filter Metric Set Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace F]

/-- Convergence along one unit radius and vanishing diameters of bounded sphere images imply
convergence at the puncture. No continuity of the map or value at the puncture is required. -/
theorem tendsto_nhdsNE_of_tendsto_radial_of_tendsto_diam_image_sphere
    {u : E → F} {a v : E} {q : F} (hv : ‖v‖ = 1)
    (hr : Tendsto (fun t : ℝ ↦ u (a + t • v)) (𝓝[>] 0) (𝓝 q))
    (hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsBounded (u '' sphere a t))
    (hd : Tendsto (fun t ↦ diam (u '' sphere a t)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto u (𝓝[≠] a) (𝓝 q) := by
  have hρ := tendsto_norm_sub_self_nhdsNE a
  have hrad := (tendsto_iff_dist_tendsto_zero.mp hr).comp hρ
  have hdiam := hd.comp hρ
  apply tendsto_iff_dist_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) ?_
    (by simpa only [zero_add] using hdiam.add hrad)
  filter_upwards [hρ.eventually hb] with x hx
  have hxs : x ∈ sphere a ‖x - a‖ := by simp
  have hrs : a + ‖x - a‖ • v ∈ sphere a ‖x - a‖ := by
    simp [norm_smul, hv]
  exact (dist_triangle _ _ _).trans
    (add_le_add (dist_le_diam_of_mem hx (mem_image_of_mem u hxs)
      (mem_image_of_mem u hrs)) le_rfl)

end TauCeti
