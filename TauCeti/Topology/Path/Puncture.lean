/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path

/-!
# Puncturing a path at a simple point

Removing a point of a path splits its range into the image of the parameters before and the image
of the parameters after, provided the point is visited only once. Each piece is preconnected, so
attaching a preconnected set which meets both pieces and misses the removed point reconnects them.

This is how a closed curve assembled from a path and a connecting set is seen to stay preconnected
when a point of the path is removed, without asking that the curve be a Jordan curve: the
connecting set may meet the path in any way away from the removed point, and the endpoints of the
path may coincide.

## Main result

* `Path.isPreconnected_range_union_sdiff_singleton` -- the range of a path together with a
  preconnected set meeting the path both before and after a point visited only once by the path,
  and missing that point, stays preconnected when the point is removed.
-/

public section

open Set

namespace Path

variable {X : Type*} [TopologicalSpace X] {x y : X}

/-- **Puncturing a path at a simple point.** Let `γ` be a path that visits `γ t` only at the
parameter `t`, and let `C` be a preconnected set that misses `γ t` but meets the path both at a
parameter before `t` and at a parameter after `t`. Then `(range γ ∪ C) \ {γ t}` is preconnected.

The typical `C` contains both endpoints of `γ`, which are then visited at the parameters `0 < t`
and `t < 1`. -/
theorem isPreconnected_range_union_sdiff_singleton (γ : Path x y) {t : unitInterval}
    (hγt : ∀ s, γ s = γ t → s = t) {C : Set X} (hC : IsPreconnected C)
    (hlt : ∃ s < t, γ s ∈ C) (hgt : ∃ s, t < s ∧ γ s ∈ C) (htC : γ t ∉ C) :
    IsPreconnected ((range γ ∪ C) \ {γ t}) := by
  obtain ⟨a, hat, haC⟩ := hlt
  obtain ⟨b, htb, hbC⟩ := hgt
  have hA : IsPreconnected (γ '' Iio t) := isPreconnected_Iio.image _ γ.continuous.continuousOn
  have hB : IsPreconnected (γ '' Ioi t) := isPreconnected_Ioi.image _ γ.continuous.continuousOn
  -- the punctured range splits at the parameter `t` into the pieces before and after `t`
  have hset : (range γ ∪ C) \ {γ t} = (γ '' Iio t ∪ C) ∪ γ '' Ioi t := by
    ext z
    simp only [mem_sdiff, mem_union, mem_range, mem_image, mem_singleton_iff, mem_Iio, mem_Ioi]
    grind
  rw [hset]
  exact (hA.union (γ a) (mem_image_of_mem γ hat) haC hC).union (γ b) (mem_union_right _ hbC)
    (mem_image_of_mem γ htb) hB

end Path
