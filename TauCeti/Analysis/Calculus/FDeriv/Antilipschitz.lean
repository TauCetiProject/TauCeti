/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import TauCeti.Topology.MetricSpace.Antilipschitz

/-!
# Quantitative embeddings of compact convex sets

An injective map with continuous derivative on a compact convex set is bounded below on chords
if its derivatives are uniformly bounded below on the directions of those chords. The bound
can deteriorate between distant points, but remains positive. Only directions parallel to the
set matter, so the result applies to lower-dimensional simplices in barycentric coordinates.

This is the separation estimate used to preserve injectivity under small Lipschitz errors in
secant approximations; compare Munkres, *Elementary Differential Topology*, Chapter II, §9.
-/

public section

open Set Metric

namespace IsCompact

/-- An injective map on a compact convex set whose continuous derivative is uniformly bounded
below on chord directions is antilipschitz on that set. The derivative
need only exist within the set, and need not be injective on the whole ambient space. -/
theorem exists_antilipschitzWith_of_hasFDerivWithinAt
    {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set V}
    (hs : IsCompact s) (hconv : Convex ℝ s) {F : V → E} {F' : V → V →L[ℝ] E}
    (hF : ∀ x ∈ s, HasFDerivWithinAt F (F' x) s x) (hF' : ContinuousOn F' s)
    (hinj : InjOn F s) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ s, c * ‖y - z‖ ≤ ‖F' x (y - z)‖) :
    ∃ K > 0, AntilipschitzWith K (s.domRestrict F) := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hs.uniformContinuousOn_of_continuous hF') (c / 2) (by positivity)
  suffices hlocal : ∀ x ∈ s, ∀ y ∈ s,
      dist x y < δ → c / 2 * dist x y ≤ dist (F x) (F y) by
    exact hs.exists_antilipschitzWith_of_locally
      (fun x hx => (hF x hx).continuousWithinAt) hinj (half_pos hc) hδ hlocal
  intro x hx y hy hxy
  let T := s ∩ closedBall x (dist x y)
  have hderiv : ∀ z ∈ T, HasFDerivWithinAt F (F' z) T z :=
    fun z hz => (hF z hz.1).mono inter_subset_left
  have hnear : ∀ z ∈ T, ‖F' z - F' x‖ ≤ c / 2 := by
    intro z hz
    rw [← dist_eq_norm]
    exact (hclose z hz.1 x hx ((mem_closedBall.mp hz.2).trans_lt hxy)).le
  have hest := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' hderiv hnear
    (hconv.inter (convex_closedBall x (dist x y)))
      (by exact ⟨hx, by simp⟩) (by exact ⟨hy, by simp [dist_comm]⟩)
  have hlower := hbound x hx y hy x hx
  have htriangle := norm_sub_norm_le (F' x (y - x)) (F y - F x)
  rw [norm_sub_rev (F' x (y - x))] at htriangle
  simp only [dist_eq_norm, norm_sub_rev x y, norm_sub_rev (F x) (F y)]
  nlinarith

end IsCompact
