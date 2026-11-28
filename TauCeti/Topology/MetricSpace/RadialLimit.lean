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
`TauCeti.tendsto_nhdsWithin_diff_of_tendsto_comp_of_tendsto_diam_image_inter_sphere`, works in any
metric source and any pseudo-metric target, for approach within any set `s`, along any path in `s`
meeting every small sphere; only the parts of the spheres inside `s` enter. Its radial form
`TauCeti.tendsto_nhdsWithin_diff_of_tendsto_radial_of_tendsto_diam_image_inter_sphere` specialises
it to a ray in `s` in a real normed space. Taking `s` to be the whole space gives
`TauCeti.tendsto_nhdsNE_of_tendsto_comp_of_tendsto_diam_image_sphere` and
`TauCeti.tendsto_nhdsNE_of_tendsto_radial_of_tendsto_diam_image_sphere`. Approach within a closed
half-plane is the case needed at a boundary puncture, where the spheres are replaced by
half-circles.
-/

public section

namespace TauCeti

open Bornology Filter Metric Set Topology

variable {E F : Type*} [PseudoMetricSpace F]

/-- Convergence along any path in `s` meeting every small sphere about a point, and vanishing
diameters of the bounded images of the parts of those spheres inside `s`, imply convergence at the
point within `s`. No continuity of the map, the path, or value at the point is required. -/
theorem tendsto_nhdsWithin_diff_of_tendsto_comp_of_tendsto_diam_image_inter_sphere
    [MetricSpace E] {u : E → F} {s : Set E} {a : E} {c : ℝ → E} {q : F}
    (hc : ∀ᶠ t in 𝓝[>] (0 : ℝ), c t ∈ s ∩ sphere a t)
    (hr : Tendsto (fun t ↦ u (c t)) (𝓝[>] 0) (𝓝 q))
    (hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsBounded (u '' (s ∩ sphere a t)))
    (hd : Tendsto (fun t ↦ diam (u '' (s ∩ sphere a t))) (𝓝[>] 0) (𝓝 0)) :
    Tendsto u (𝓝[s \ {a}] a) (𝓝 q) := by
  have hρ : Tendsto (dist · a) (𝓝[s \ {a}] a) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_nhdsWithin_of_tendsto_nhds
      ((continuous_id.dist continuous_const).tendsto' a 0 (dist_self a)),
      eventually_mem_nhdsWithin.mono fun _ hx ↦ dist_pos.mpr hx.2⟩
  refine tendsto_iff_dist_tendsto_zero.mpr <| squeeze_zero' (.of_forall fun _ ↦ dist_nonneg) ?_
    (by simpa using (hd.comp hρ).add ((tendsto_iff_dist_tendsto_zero.mp hr).comp hρ))
  filter_upwards [self_mem_nhdsWithin, hρ.eventually hb, hρ.eventually hc] with x hxs hx hcx
  exact (dist_triangle _ _ _).trans <| add_le_add_left (dist_le_diam_of_mem hx
    (mem_image_of_mem u ⟨hxs.1, mem_sphere.mpr rfl⟩) (mem_image_of_mem u hcx)) _

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
  simpa [compl_eq_univ_sdiff] using
    tendsto_nhdsWithin_diff_of_tendsto_comp_of_tendsto_diam_image_inter_sphere (s := univ)
      (by simpa using hc) hr (by simpa using hb) (by simpa using hd)

/-- Convergence along one radius lying in `s` near the point, and vanishing diameters of the
bounded images of the parts of small spheres inside `s`, imply convergence at the point within
`s`. No continuity of the map or value at the point is required. -/
theorem tendsto_nhdsWithin_diff_of_tendsto_radial_of_tendsto_diam_image_inter_sphere
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → F} {s : Set E} {a v : E} {q : F} (hv : v ≠ 0)
    (hs : ∀ᶠ t in 𝓝[>] (0 : ℝ), a + t • v ∈ s)
    (hr : Tendsto (fun t : ℝ ↦ u (a + t • v)) (𝓝[>] 0) (𝓝 q))
    (hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsBounded (u '' (s ∩ sphere a t)))
    (hd : Tendsto (fun t ↦ diam (u '' (s ∩ sphere a t))) (𝓝[>] 0) (𝓝 0)) :
    Tendsto u (𝓝[s \ {a}] a) (𝓝 q) := by
  have hscale : Tendsto (fun t : ℝ ↦ t / ‖v‖) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_nhdsWithin_of_tendsto_nhds
      (by simpa using (continuous_id.div_const ‖v‖).tendsto 0),
      eventually_mem_nhdsWithin.mono fun _ ht ↦ div_pos ht (norm_pos_iff.mpr hv)⟩
  refine tendsto_nhdsWithin_diff_of_tendsto_comp_of_tendsto_diam_image_inter_sphere
    (c := fun t ↦ a + (t / ‖v‖) • v) ?_ (hr.comp hscale) hb hd
  filter_upwards [self_mem_nhdsWithin, hscale.eventually hs] with t ht hts
  exact ⟨hts, by simp [norm_smul, abs_of_pos (mem_Ioi.mp ht), hv]⟩

/-- Convergence along one radius and vanishing diameters of bounded sphere images imply
convergence at the puncture. No continuity of the map or value at the puncture is required. -/
theorem tendsto_nhdsNE_of_tendsto_radial_of_tendsto_diam_image_sphere
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → F} {a v : E} {q : F} (hv : v ≠ 0)
    (hr : Tendsto (fun t : ℝ ↦ u (a + t • v)) (𝓝[>] 0) (𝓝 q))
    (hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsBounded (u '' sphere a t))
    (hd : Tendsto (fun t ↦ diam (u '' sphere a t)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto u (𝓝[≠] a) (𝓝 q) := by
  simpa [compl_eq_univ_sdiff] using
    tendsto_nhdsWithin_diff_of_tendsto_radial_of_tendsto_diam_image_inter_sphere (s := univ) hv
      (.of_forall fun _ ↦ mem_univ _) hr (by simpa using hb) (by simpa using hd)

end TauCeti
