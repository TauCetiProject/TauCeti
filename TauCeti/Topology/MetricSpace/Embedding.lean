/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Local images of neighborhoods under inducing maps

The image of a neighborhood in the source of an inducing map agrees, on a small ball around
the image of its base point, with the full range of the map.
-/

public section

open Set Topology

namespace Topology.IsInducing

variable {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]

/-- Near the image of a point, the range of an inducing map agrees with the image of any
neighborhood of that point. -/
theorem exists_ball_inter_range_eq_ball_inter_image {f : X → Y} (hf : IsInducing f)
    {s : Set X} {x : X} (hs : s ∈ 𝓝 x) :
    ∃ ε : ℝ, 0 < ε ∧
      Metric.ball (f x) ε ∩ range f = Metric.ball (f x) ε ∩ f '' s := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp (hf.image_mem_nhdsWithin hs)
  exact ⟨ε, hε, (subset_inter inter_subset_left hsub).antisymm
    (inter_subset_inter_right _ (image_subset_range f s))⟩

end Topology.IsInducing
