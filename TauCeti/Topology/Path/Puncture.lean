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
of the parameters after, provided the point is visited only once. Each piece is preconnected, the
first containing the source and the second the target, so attaching a preconnected set through
both endpoints which misses the removed point reconnects them.

This is how a closed curve assembled from a path and a connecting set is seen to stay preconnected
when a point of the path is removed, without asking that the curve be a Jordan curve: the
connecting set may meet the path at its endpoints in any way, and the endpoints may coincide.

## Main result

* `Path.isPreconnected_range_union_sdiff_singleton` -- the range of a path together with a
  preconnected set through its endpoints stays preconnected when a point visited only once by the
  path, and missed by the set, is removed.
-/

public section

open Set

namespace Path

variable {X : Type*} [TopologicalSpace X] {x y : X}

/-- **Puncturing a path at a simple point.** Let `γ` be a path from `x` to `y` that visits `γ t`
only at the parameter `t`, and let `C` be a preconnected set containing `x` and `y` but not `γ t`.
Then `(range γ ∪ C) \ {γ t}` is preconnected: the parameters before `t` and those after `t` give
two preconnected pieces through `x` and through `y`, and `C` joins them. -/
theorem isPreconnected_range_union_sdiff_singleton (γ : Path x y) {t : unitInterval}
    (hγt : ∀ s, γ s = γ t → s = t) {C : Set X} (hC : IsPreconnected C) (hx : x ∈ C)
    (hy : y ∈ C) (htC : γ t ∉ C) :
    IsPreconnected ((range γ ∪ C) \ {γ t}) := by
  -- the parameter `t` is interior, since both endpoints lie in `C`
  have ht0 : (0 : ℝ) < t := lt_of_le_of_ne t.2.1 fun h => htC (by
    rw [show t = 0 from Subtype.ext h.symm, γ.source]; exact hx)
  have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 fun h => htC (by
    rw [show t = 1 from Subtype.ext h, γ.target]; exact hy)
  have hγt' (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (h : γ.extend s = γ t) : s = t :=
    congrArg Subtype.val (hγt ⟨s, hs⟩ (by rwa [← γ.extend_extends']))
  have hcont := γ.continuous_extend.continuousOn (s := univ)
  have hA : IsPreconnected (γ.extend '' Ico 0 t) :=
    isPreconnected_Ico.image _ (hcont.mono (subset_univ _))
  have hB : IsPreconnected (γ.extend '' Ioc (t : ℝ) 1) :=
    isPreconnected_Ioc.image _ (hcont.mono (subset_univ _))
  have hxA : x ∈ γ.extend '' Ico 0 t := ⟨0, ⟨le_rfl, ht0⟩, γ.extend_zero⟩
  have hyB : y ∈ γ.extend '' Ioc (t : ℝ) 1 := ⟨1, ⟨ht1, le_rfl⟩, γ.extend_one⟩
  -- the punctured range splits at the parameter `t` into the pieces through `x` and through `y`
  have hset : (range γ ∪ C) \ {γ t} = (γ.extend '' Ico 0 t ∪ C) ∪ γ.extend '' Ioc (t : ℝ) 1 := by
    rw [← γ.image_extend_of_subset (subset_refl (Icc (0 : ℝ) 1))]
    ext z
    simp only [mem_sdiff, mem_union, mem_image, mem_singleton_iff, mem_Ico, mem_Ioc, mem_Icc]
    constructor
    · rintro ⟨hz | hzC, hzt⟩
      · obtain ⟨s, hs, rfl⟩ := hz
        rcases lt_trichotomy s t with hst | hst | hst
        · exact Or.inl (Or.inl ⟨s, ⟨hs.1, hst⟩, rfl⟩)
        · exact absurd (by rw [hst, γ.extend_extends']) hzt
        · exact Or.inr ⟨s, ⟨hst, hs.2⟩, rfl⟩
      · exact Or.inl (Or.inr hzC)
    · rintro ((⟨s, hs, rfl⟩ | hzC) | ⟨s, hs, rfl⟩)
      · exact ⟨Or.inl ⟨s, ⟨hs.1, hs.2.le.trans ht1.le⟩, rfl⟩,
          fun h => hs.2.ne (hγt' s ⟨hs.1, hs.2.le.trans ht1.le⟩ h)⟩
      · exact ⟨Or.inr hzC, fun h => htC (h ▸ hzC)⟩
      · exact ⟨Or.inl ⟨s, ⟨ht0.le.trans hs.1.le, hs.2⟩, rfl⟩,
          fun h => hs.1.ne' (hγt' s ⟨ht0.le.trans hs.1.le, hs.2⟩ h)⟩
  rw [hset]
  exact (hA.union x hxA hx hC).union y (mem_union_right _ hy) hyB hB

end Path
