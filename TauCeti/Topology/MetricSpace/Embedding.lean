/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Local images of open sets under inducing maps

An open neighborhood in the source of an inducing map agrees, near the image of each of its
points, with the full range of the map.
-/

public section

open Set

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]

/-- Near the image of a point in an open set, the range of an inducing map agrees with the image
of that open set. -/
theorem exists_ball_inter_range_eq_ball_inter_image_of_isInducing
    (f : X → Y) (hf : Topology.IsInducing f) {s : Set X} (hs : IsOpen s)
    {x : X} (hx : x ∈ s) :
    ∃ ε : ℝ, 0 < ε ∧
      Metric.ball (f x) ε ∩ range f = Metric.ball (f x) ε ∩ f '' s := by
  obtain ⟨u, hu, hsu⟩ := hf.image_eq_isOpen_inter_range hs
  have hxu : f x ∈ u := by
    have h : f x ∈ f '' s := ⟨x, hx, rfl⟩
    rw [hsu] at h
    exact h.1
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu _ hxu
  refine ⟨ε, hε, ?_⟩
  rw [hsu]
  ext w
  constructor
  · rintro ⟨hw, hr⟩
    exact ⟨hw, hball hw, hr⟩
  · rintro ⟨hw, _, hr⟩
    exact ⟨hw, hr⟩

end TauCeti
