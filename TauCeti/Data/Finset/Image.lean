/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Image

/-!
# Images of filtered finsets

* `Finset.image_filter_mem_subset`: the image under `f` of the elements of `s` that `f` maps into
  `t` lies in `t`.
* `Finset.disjoint_of_disjoint_image_of_image_subset`: if `f` maps `s` away from `u` and `t` into
  `u`, then `s` and `t` are disjoint.
* `Finset.image_filter_mem_union_eq`: the elements of `s` that `f` maps into `u`, together with a
  set `t` mapping onto `u ∩ v`, map onto `u` when `u ⊆ f(s) ∪ v`.
-/

public section

namespace Finset

variable {α β : Type*} [DecidableEq β]

/-- The image under `f` of the elements of `s` that `f` maps into `t` lies in `t`. -/
theorem image_filter_mem_subset (f : α → β) (s : Finset α) (t : Finset β) :
    {a ∈ s | f a ∈ t}.image f ⊆ t :=
  image_subset_iff.2 fun _ ha ↦ (mem_filter.1 ha).2

/-- If `f` maps `s` away from `u` and `t` into `u`, then `s` and `t` are disjoint. -/
theorem disjoint_of_disjoint_image_of_image_subset {f : α → β} {s t : Finset α} {u : Finset β}
    (hs : Disjoint (s.image f) u) (ht : t.image f ⊆ u) : Disjoint s t :=
  (disjoint_of_subset_right ht hs).of_image_finset

/-- The elements of `s` that `f` maps into `u`, together with a set `t` that `f` maps onto
`u ∩ v`, are mapped onto `u`, provided every element of `u` outside `v` is the image of an element
of `s`. -/
theorem image_filter_mem_union_eq [DecidableEq α] {f : α → β} {s t : Finset α} {u v : Finset β}
    (hu : u ⊆ s.image f ∪ v) (ht : t.image f = u ∩ v) : ({a ∈ s | f a ∈ u} ∪ t).image f = u := by
  refine (image_union _ _).trans <| subset_antisymm
    (union_subset (image_filter_mem_subset f s u) (ht.le.trans inter_subset_left)) fun b hb ↦ ?_
  rcases mem_union.1 (hu hb) with hbs | hbv
  · obtain ⟨a, ha, rfl⟩ := mem_image.1 hbs
    exact mem_union_left _ (mem_image_of_mem f (mem_filter.2 ⟨ha, hb⟩))
  · exact mem_union_right _ (ht ▸ mem_inter.2 ⟨hb, hbv⟩)

end Finset
