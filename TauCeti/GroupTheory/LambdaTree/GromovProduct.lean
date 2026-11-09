/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LambdaTree.Basic

/-!
# Branch points and Gromov products in `Λ`-trees

Let `X` be a `Λ`-tree, with metric `d`. For a base point `v` and two points `x` and `y`, the
segments `[v, x]` and `[v, y]` share an initial segment `[v, w]`, and the branch point `w` lies on
the segment `[x, y]`. Comparing lengths along these three segments gives
`d v x + d v y - d x y = 2 • d v w`. Thus the Gromov product
`(x · y)_v = (d v x + d v y - d x y) / 2`, which a priori lies only in the divisible hull of `Λ`,
is the element `d v w` of `Λ`.

The Gromov products of a `Λ`-tree are moreover `0`-hyperbolic:
`min ((x · y)_v, (y · z)_v) ≤ (x · z)_v`. Of the two branch points of `x` and `z` with `y`, the
one nearer to `v` lies on both `[v, x]` and `[v, z]`, hence on their common initial segment.

These are the properties of a `Λ`-tree which make the based length function `g ↦ d v (g • v)` of
an isometric action a Lyndon length function whose Gromov products lie in `Λ`. Along the way the
segments of a `Λ`-tree are characterised by the triangle equality: `u` lies on `[x, y]` if and
only if `d x u + d u y = d x y`.

## Main results

* `TauCeti.LambdaMetric.IsTree.exists_segment_inter_segment_eq`: `[v, x] ∩ [v, y] = [v, w]` for
  some `w ∈ [x, y]`.
* `TauCeti.LambdaMetric.IsTree.two_nsmul_dist_eq`: for such a branch point `w`,
  `2 • d v w = d v x + d v y - d x y`.
* `TauCeti.LambdaMetric.IsTree.even_dist_add_dist_sub_dist`: `d v x + d v y - d x y ∈ 2Λ`.
* `TauCeti.LambdaMetric.IsTree.mem_segment_iff`: `u ∈ [x, y]` if and only if
  `d x u + d u y = d x y`.
* `TauCeti.LambdaMetric.IsTree.min_dist_add_dist_sub_dist_le`: `Λ`-trees are `0`-hyperbolic.

## References

* I. Chiswell, *Introduction to Λ-trees*, World Scientific, 2001, §§1.2 and 2.1.
* O. Kharlampovich, A. Myasnikov, D. Serbin, *Actions, length functions, and non-Archimedean
  words*, Internat. J. Algebra Comput. 23 (2013), §4.2, Lemma 8.
-/

public section

namespace TauCeti.LambdaMetric

open Set

variable {Λ X : Type*} [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
  {d : LambdaMetric Λ X}

namespace IsTree

variable (hd : d.IsTree)
include hd

/-- In a `Λ`-tree, the segments `[v, x]` and `[v, y]` intersect in a segment `[v, w]` whose end
`w`, the point where they branch, lies on `[x, y]`. -/
theorem exists_segment_inter_segment_eq (v x y : X) :
    ∃ w ∈ hd.segment x y, hd.segment v x ∩ hd.segment v y = hd.segment v w := by
  have hσ := hd.isSegment_segment v x
  have hτ := hd.isSegment_segment v y
  -- By (T3) the intersection is a segment `[p, q]`. It lies in `[v, x]` and contains `v`, so `v`
  -- is one of its ends.
  obtain ⟨p, q, hρ⟩ := hd.exists_isSegment_inter hσ hτ
  have hpq : hd.segment p q = hd.segment v x ∩ hd.segment v y :=
    (hd.isSegment_iff_eq_segment.1 hρ).symm
  have hv : v ∈ hd.segment p q := hpq ▸ ⟨hd.left_mem_segment v x, hd.left_mem_segment v y⟩
  rw [hd.segment_eq_sep hσ hρ.left_mem.1 hρ.right_mem.1] at hv
  obtain ⟨-, hv⟩ := hv
  rw [d.refl, mem_uIcc] at hv
  obtain ⟨w, hw⟩ : ∃ w, hd.segment v x ∩ hd.segment v y = hd.segment v w := by
    rcases hv with ⟨h, -⟩ | ⟨h, -⟩
    · obtain rfl := d.eq_zero_iff.1 (le_antisymm h (d.nonneg v p))
      exact ⟨q, hpq.symm⟩
    · obtain rfl := d.eq_zero_iff.1 (le_antisymm h (d.nonneg v q))
      exact ⟨p, hpq.symm.trans (hd.segment_comm p v)⟩
  have hw' : w ∈ hd.segment v x ∩ hd.segment v y := hw ▸ hd.right_mem_segment v w
  refine ⟨w, ?_, hw⟩
  -- The parts `[w, x]` of `[v, x]` and `[w, y]` of `[v, y]` beyond `w` meet only in `w`.
  have hαβ : hd.segment w x ∩ hd.segment w y = {w} := by
    refine subset_antisymm (fun u hu => ?_) (by simp)
    have huw : u ∈ hd.segment v w := hw ▸
      ⟨hd.segment_subset hσ hw'.1 hσ.right_mem hu.1, hd.segment_subset hτ hw'.2 hτ.right_mem hu.2⟩
    have h₁ := (hd.isSegment_segment v w).dist_add_dist huw
    have h₂ := hu.1
    rw [hd.segment_eq_sep hσ hw'.1 hσ.right_mem] at h₂
    obtain ⟨-, h₂⟩ := h₂
    have h₃ := hσ.dist_add_dist hw'.1
    rw [mem_uIcc] at h₂
    have : d u w = 0 := by grind [d.nonneg w x, d.nonneg u w]
    exact mem_singleton_iff.2 (d.eq_zero_iff.1 this)
  -- By (T2) their union is a segment `γ`. In `γ`, `w` lies between `x` and `y`: otherwise `x` or
  -- `y` would lie on both parts, so would be `w`.
  obtain ⟨p', q', hγ⟩ := hd.exists_isSegment_union (hd.isSegment_segment w x).symm
    (hd.isSegment_segment w y) hαβ
  have hwγ : w ∈ hd.segment w x ∪ hd.segment w y := .inl (hd.left_mem_segment w x)
  have hxγ : x ∈ hd.segment w x ∪ hd.segment w y := .inl (hd.right_mem_segment w x)
  have hyγ : y ∈ hd.segment w x ∪ hd.segment w y := .inr (hd.right_mem_segment w y)
  have hα := hd.segment_eq_sep hγ hwγ hxγ
  have hβ := hd.segment_eq_sep hγ hwγ hyγ
  rw [hd.segment_eq_sep hγ hxγ hyγ]
  refine ⟨hwγ, ?_⟩
  by_contra hmid
  have hx : d p' x ∉ uIcc (d p' w) (d p' y) := fun h => hmid <| by
    have : x ∈ hd.segment w x ∩ hd.segment w y := ⟨hd.right_mem_segment w x, hβ ▸ ⟨hxγ, h⟩⟩
    rw [hαβ, mem_singleton_iff] at this
    rw [this]
    exact left_mem_uIcc
  have hy : d p' y ∉ uIcc (d p' w) (d p' x) := fun h => hmid <| by
    have : y ∈ hd.segment w x ∩ hd.segment w y := ⟨hα ▸ ⟨hyγ, h⟩, hd.right_mem_segment w y⟩
    rw [hαβ, mem_singleton_iff] at this
    rw [this]
    exact right_mem_uIcc
  simp only [mem_uIcc] at hmid hx hy
  grind

/-- If `[v, x]` and `[v, y]` branch at a point `w` of `[x, y]`, then `d v w` is the Gromov product
`(x · y)_v`: twice it is `d v x + d v y - d x y`. -/
theorem two_nsmul_dist_eq {v x y w : X} (hw : w ∈ hd.segment x y)
    (h : hd.segment v x ∩ hd.segment v y = hd.segment v w) :
    2 • d v w = d v x + d v y - d x y := by
  have hw' : w ∈ hd.segment v x ∩ hd.segment v y := h ▸ hd.right_mem_segment v w
  rw [two_nsmul, ← (hd.isSegment_segment v x).dist_add_dist hw'.1,
    ← (hd.isSegment_segment v y).dist_add_dist hw'.2,
    ← (hd.isSegment_segment x y).dist_add_dist hw, d.symm x w]
  grind

/-- In a `Λ`-tree, `d v x + d v y - d x y` lies in `2Λ`, so the Gromov product `(x · y)_v` lies in
`Λ`. -/
theorem even_dist_add_dist_sub_dist (v x y : X) : Even (d v x + d v y - d x y) := by
  obtain ⟨w, hw, h⟩ := hd.exists_segment_inter_segment_eq v x y
  exact ⟨d v w, by rw [← hd.two_nsmul_dist_eq hw h, two_nsmul]⟩

/-- In a `Λ`-tree, a point lies on the segment `[x, y]` if and only if it satisfies the triangle
equality `d x u + d u y = d x y`. -/
theorem mem_segment_iff {x y u : X} : u ∈ hd.segment x y ↔ d x u + d u y = d x y := by
  refine ⟨(hd.isSegment_segment x y).dist_add_dist, fun h => ?_⟩
  -- The branch point `w` of `[u, x]` and `[u, y]` lies on `[x, y]`, and
  -- `d x u + d u y = d x y + 2 • d u w`.
  obtain ⟨w, hw, hinter⟩ := hd.exists_segment_inter_segment_eq u x y
  have h₁ := hd.two_nsmul_dist_eq hw hinter
  rw [d.symm u x, h, two_nsmul, sub_self] at h₁
  have : d u w = 0 := by grind [d.nonneg u w]
  rwa [d.eq_zero_iff.1 this]

/-- `Λ`-trees are `0`-hyperbolic: the Gromov products satisfy
`min ((x · y)_v, (y · z)_v) ≤ (x · z)_v`, stated here for their doubles. -/
theorem min_dist_add_dist_sub_dist_le (v x y z : X) :
    min (d v x + d v y - d x y) (d v y + d v z - d y z) ≤ d v x + d v z - d x z := by
  obtain ⟨a, ha, hxy⟩ := hd.exists_segment_inter_segment_eq v x y
  obtain ⟨b, hb, hyz⟩ := hd.exists_segment_inter_segment_eq v y z
  obtain ⟨c, hc, hxz⟩ := hd.exists_segment_inter_segment_eq v x z
  rw [← hd.two_nsmul_dist_eq ha hxy, ← hd.two_nsmul_dist_eq hb hyz, ← hd.two_nsmul_dist_eq hc hxz]
  have ha' : a ∈ hd.segment v x ∩ hd.segment v y := hxy ▸ hd.right_mem_segment v a
  have hb' : b ∈ hd.segment v y ∩ hd.segment v z := hyz ▸ hd.right_mem_segment v b
  -- A point on both `[v, x]` and `[v, z]` lies on `[v, c]`, so is at most as far from `v` as `c`.
  have key {u : X} (hu : u ∈ hd.segment v x ∩ hd.segment v z) : 2 • d v u ≤ 2 • d v c := by
    rw [hxz] at hu
    exact nsmul_le_nsmul_right ((hd.isSegment_segment v c).dist_add_dist hu ▸
      le_add_of_nonneg_right (d.nonneg u c)) 2
  -- Of `a` and `b`, which both lie on `[v, y]`, the one nearer to `v` lies on `[v, a]` or `[v, b]`.
  have hσ := hd.isSegment_segment v y
  rcases le_total (d v a) (d v b) with hab | hba
  · have : a ∈ hd.segment v b := by
      rw [hd.segment_eq_sep hσ hσ.left_mem hb'.1, d.refl]
      exact ⟨ha'.2, mem_uIcc_of_le (d.nonneg v a) hab⟩
    have ha'' : a ∈ hd.segment v y ∩ hd.segment v z := hyz ▸ this
    exact min_le_left _ _ |>.trans (key ⟨ha'.1, ha''.2⟩)
  · have : b ∈ hd.segment v a := by
      rw [hd.segment_eq_sep hσ hσ.left_mem ha'.2, d.refl]
      exact ⟨hb'.1, mem_uIcc_of_le (d.nonneg v b) hba⟩
    have hb'' : b ∈ hd.segment v x ∩ hd.segment v y := hxy ▸ this
    exact min_le_right _ _ |>.trans (key ⟨hb''.1, hb'.2⟩)

end IsTree

end TauCeti.LambdaMetric
