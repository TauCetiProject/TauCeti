/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# A radial limit and shrinking sphere images determine a puncture limit

If the images of small spheres about a point have diameter tending to zero, convergence
along one radius determines convergence along every approach to the point. Boundedness of
those images is explicit: the real-valued diameter of an unbounded set has junk value zero.

This is the metric step in continuous removal of isolated singularities, separating radial
convergence from the estimates controlling angular oscillation. The general form,
`TauCeti.tendsto_nhdsNE_of_tendsto_comp_of_tendsto_diam_image_sphere`, works in any metric
source and any pseudo-metric target, along any path meeting every small sphere; the radial form
`TauCeti.tendsto_nhdsNE_of_tendsto_radial_of_tendsto_diam_image_sphere` specialises it to a ray
in a real normed space.
-/

public section

namespace TauCeti

open Bornology Filter Metric Set Topology

variable {E F : Type*} [PseudoMetricSpace F]

/-- Convergence along any path meeting every small sphere about a point and vanishing diameters
of bounded sphere images imply convergence at the puncture. No continuity of the map, the path,
or value at the puncture is required. -/
theorem tendsto_nhdsNE_of_tendsto_comp_of_tendsto_diam_image_sphere [MetricSpace E]
    {u : E → F} {a : E} {c : ℝ → E} {q : F}
    (hc : ∀ᶠ t in 𝓝[>] (0 : ℝ), c t ∈ sphere a t)
    (hr : Tendsto (fun t ↦ u (c t)) (𝓝[>] 0) (𝓝 q))
    (hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsBounded (u '' sphere a t))
    (hd : Tendsto (fun t ↦ diam (u '' sphere a t)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto u (𝓝[≠] a) (𝓝 q) := by
  have hρ : Tendsto (dist · a) (𝓝[≠] a) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_nhdsWithin_of_tendsto_nhds
      ((continuous_id.dist continuous_const).tendsto' a 0 (dist_self a)),
      eventually_mem_nhdsWithin.mono fun _ ↦ dist_pos.mpr⟩
  refine tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero' (.of_forall fun _ ↦ dist_nonneg) ?_
    (by simpa using (hd.comp hρ).add ((tendsto_iff_dist_tendsto_zero.mp hr).comp hρ))
  filter_upwards [hρ.eventually hb, hρ.eventually hc] with x hx hcx
  exact (dist_triangle _ _ _).trans <| add_le_add_left
    (dist_le_diam_of_mem hx (mem_image_of_mem u (mem_sphere.mpr rfl)) (mem_image_of_mem u hcx)) _

/-- Convergence along one radius and vanishing diameters of bounded sphere images imply
convergence at the puncture. No continuity of the map or value at the puncture is required. -/
theorem tendsto_nhdsNE_of_tendsto_radial_of_tendsto_diam_image_sphere
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → F} {a v : E} {q : F} (hv : v ≠ 0)
    (hr : Tendsto (fun t : ℝ ↦ u (a + t • v)) (𝓝[>] 0) (𝓝 q))
    (hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsBounded (u '' sphere a t))
    (hd : Tendsto (fun t ↦ diam (u '' sphere a t)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto u (𝓝[≠] a) (𝓝 q) := by
  have hs : Tendsto (fun t : ℝ ↦ t / ‖v‖) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_nhdsWithin_of_tendsto_nhds
      (by simpa using (continuous_id.div_const ‖v‖).tendsto 0),
      eventually_mem_nhdsWithin.mono fun _ ht ↦ div_pos ht (norm_pos_iff.mpr hv)⟩
  refine tendsto_nhdsNE_of_tendsto_comp_of_tendsto_diam_image_sphere
    (c := fun t ↦ a + (t / ‖v‖) • v) ?_ (hr.comp hs) hb hd
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp [norm_smul, abs_of_pos (mem_Ioi.mp ht), hv]

end TauCeti
