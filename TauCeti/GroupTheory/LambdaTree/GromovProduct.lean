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
only if `d x u + d u y = d x y`, a point of `[x, y]` is determined by its distance to `x`, and the
distance between `u₁ ∈ [v, x]` and `u₂ ∈ [v, y]` is expressed in terms of their distances to `v`
and `(x · y)_v`.

Conversely, by Chiswell's characterisation of `Λ`-trees, a nonempty geodesic `Λ`-metric space is a
`Λ`-tree as soon as, at a single base point `v₀`, the quantities `d v₀ x + d v₀ y - d x y` are
even and satisfy `0`-hyperbolicity. Passing from one base point to all points gives the four-point
`0`-hyperbolicity inequality `d x y + d z w ≤ max (d x z + d y w) (d x w + d y z)`, which forces
every geodesic segment from `x` to `y` to coincide with `{u | d x u + d u y = d x y}` and yields
axioms (T2) and (T3).

## Main results

* `TauCeti.LambdaMetric.IsTree.exists_segment_inter_segment_eq`: `[v, x] ∩ [v, y] = [v, w]` for
  some `w ∈ [x, y]`.
* `TauCeti.LambdaMetric.IsTree.two_nsmul_dist_eq`: for such a branch point `w`,
  `2 • d v w = d v x + d v y - d x y`.
* `TauCeti.LambdaMetric.IsTree.even_dist_add_dist_sub_dist`: `d v x + d v y - d x y ∈ 2Λ`.
* `TauCeti.LambdaMetric.IsTree.mem_segment_iff`: `u ∈ [x, y]` if and only if
  `d x u + d u y = d x y`.
* `TauCeti.LambdaMetric.IsTree.eq_of_mem_segment_of_dist_eq`: a point of `[x, y]` is determined by
  its distance from `x`.
* `TauCeti.LambdaMetric.IsTree.dist_of_mem_segment`: formula for `d u₁ u₂` when `u₁ ∈ [v, x]` and
  `u₂ ∈ [v, y]`.
* `TauCeti.LambdaMetric.IsTree.min_dist_add_dist_sub_dist_le`,
  `TauCeti.LambdaMetric.IsTree.four_point`: `Λ`-trees are `0`-hyperbolic.
* `TauCeti.LambdaMetric.isTree_of_isGeodesic`, `TauCeti.LambdaMetric.isTree_iff_four_point`: a
  nonempty geodesic `Λ`-metric space is a `Λ`-tree if and only if its Gromov products lie in `Λ`
  and are `0`-hyperbolic.

## References

* I. Chiswell, *Introduction to Λ-trees*, World Scientific, 2001, §§1.2 and 2.1 (Lemma 1.2.5 and
  Theorem 2.1.6).
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

/-- In a `Λ`-tree, a point of the segment `[x, y]` is uniquely determined by its distance from
`x`. -/
theorem eq_of_mem_segment_of_dist_eq {x y u v : X} (hu : u ∈ hd.segment x y)
    (hv : v ∈ hd.segment x y) (h : d x u = d x v) : u = v := by
  have hdist := (hd.isSegment_segment x y).dist_eq_abs_sub hu hv
  rw [h, sub_self, abs_zero, d.eq_zero_iff] at hdist
  exact hdist

/-- In a `Λ`-tree, the distance between `u₁ ∈ [v, x]` and `u₂ ∈ [v, y]` depends only on their
distances from `v` and the doubled Gromov product `d v x + d v y - d x y`. -/
theorem dist_of_mem_segment {v x y u₁ u₂ : X} (hu₁ : u₁ ∈ hd.segment v x)
    (hu₂ : u₂ ∈ hd.segment v y) :
    d u₁ u₂ = d v u₁ + d v u₂ -
      min (2 • d v u₁) (min (2 • d v u₂) (d v x + d v y - d x y)) := by
  obtain ⟨w, hw, hinter⟩ := hd.exists_segment_inter_segment_eq v x y
  have hw' : w ∈ hd.segment v x ∩ hd.segment v y := hinter ▸ hd.right_mem_segment v w
  rw [← hd.two_nsmul_dist_eq hw hinter]
  have hσ := hd.isSegment_segment v x
  have hτ := hd.isSegment_segment v y
  -- Either `u₁` or `u₂` precedes the branch point `w`, so both lie on one segment, or both lie
  -- beyond `w` and the path between them passes through `w`.
  rcases le_total (d v u₁) (d v w) with h₁ | h₁
  · have hu₁w : u₁ ∈ hd.segment v w := by
      rw [hd.segment_eq_sep hσ hσ.left_mem hw'.1, d.refl]
      exact ⟨hu₁, mem_uIcc_of_le (d.nonneg v u₁) h₁⟩
    have hu₁y : u₁ ∈ hd.segment v y := (hinter ▸ hu₁w).2
    rw [hτ.dist_eq_abs_sub hu₁y hu₂, two_nsmul, two_nsmul, two_nsmul]
    rcases le_total (d v u₁) (d v u₂) with h₁₂ | h₁₂
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h₁₂)]
      grind
    · rw [abs_of_nonneg (sub_nonneg.2 h₁₂)]
      grind
  · rcases le_total (d v u₂) (d v w) with h₂ | h₂
    · have hu₂w : u₂ ∈ hd.segment v w := by
        rw [hd.segment_eq_sep hτ hτ.left_mem hw'.2, d.refl]
        exact ⟨hu₂, mem_uIcc_of_le (d.nonneg v u₂) h₂⟩
      have hu₂x : u₂ ∈ hd.segment v x := (hinter ▸ hu₂w).1
      rw [hσ.dist_eq_abs_sub hu₁ hu₂x, two_nsmul, two_nsmul, two_nsmul]
      rcases le_total (d v u₁) (d v u₂) with h₁₂ | h₁₂
      · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h₁₂)]
        grind
      · rw [abs_of_nonneg (sub_nonneg.2 h₁₂)]
        grind
    · have hwu₁ : d w u₁ = d v u₁ - d v w := by
        rw [hσ.dist_eq_abs_sub hw'.1 hu₁, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h₁)]
      have hwu₂ : d w u₂ = d v u₂ - d v w := by
        rw [hτ.dist_eq_abs_sub hw'.2 hu₂, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h₂)]
      have hwx := hσ.dist_add_dist hw'.1
      have hwy := hτ.dist_add_dist hw'.2
      have hu₁x := hσ.dist_add_dist hu₁
      have hu₂y := hτ.dist_add_dist hu₂
      have hxy := (hd.isSegment_segment x y).dist_add_dist hw
      have htri₁ := d.triangle u₁ w u₂
      have htri₂ := d.triangle x u₁ y
      have htri₃ := d.triangle u₁ u₂ y
      rw [d.symm x w] at hxy
      rw [d.symm x u₁] at htri₂
      rw [d.symm w u₁] at hwu₁
      rw [two_nsmul, two_nsmul, two_nsmul]
      grind

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

/-- The four-point `0`-hyperbolicity inequality in a `Λ`-tree: of the three sums of opposite
distances among four points, the largest two are equal. -/
theorem four_point (x y z w : X) :
    d x y + d z w ≤ max (d x z + d y w) (d x w + d y z) := by
  have h := hd.min_dist_add_dist_sub_dist_le w x z y
  rw [d.symm w x, d.symm w z, d.symm w y, d.symm z y] at h
  grind

end IsTree

/-! ### Characterisation of `Λ`-trees by `0`-hyperbolicity -/

/-- If `d v₀ x + d v₀ y - d x y` is even for a single base point `v₀` and all `x, y`, then
`d v x + d v y - d x y` is even for every base point `v`. -/
theorem even_dist_add_dist_sub_dist_of_base {v₀ : X}
    (heven : ∀ x y : X, Even (d v₀ x + d v₀ y - d x y)) (v x y : X) :
    Even (d v x + d v y - d x y) := by
  obtain ⟨a, ha⟩ := heven x y
  obtain ⟨b, hb⟩ := heven v x
  obtain ⟨c, hc⟩ := heven v y
  exact ⟨d v₀ v + a - b - c, by grind⟩

/-- `0`-hyperbolicity of the Gromov products at a single base point `v₀` implies the four-point
`0`-hyperbolicity inequality everywhere (Chiswell, Lemma 1.2.5). -/
theorem four_point_of_min_dist_add_dist_sub_dist_le {v₀ : X}
    (hhyp : ∀ x y z : X,
      min (d v₀ x + d v₀ y - d x y) (d v₀ y + d v₀ z - d y z) ≤ d v₀ x + d v₀ z - d x z)
    (x y z w : X) :
    d x y + d z w ≤ max (d x z + d y w) (d x w + d y z) := by
  have h₁ := hhyp x z y
  have h₂ := hhyp x w y
  have h₃ := hhyp z x w
  have h₄ := hhyp z y w
  rw [d.symm z y] at h₁ h₄
  rw [d.symm w y] at h₂
  rw [d.symm z x] at h₃
  grind

/-- In a four-point `0`-hyperbolic `Λ`-metric space, every segment from `x` to `y` is the set of
points satisfying the triangle equality `d x u + d u y = d x y`. -/
private theorem eq_setOf_dist_add_dist_of_four_point
    (hfour : ∀ x y z w : X, d x y + d z w ≤ max (d x z + d y w) (d x w + d y z))
    {σ : Set X} {x y : X} (hσ : d.IsSegment σ x y) :
    σ = {u : X | d x u + d u y = d x y} := by
  refine Subset.antisymm (fun u hu => hσ.dist_add_dist hu) fun u (hu : d x u + d u y = d x y) => ?_
  -- `σ` contains a point `w` at distance `d x u` from `x`; four-point `0`-hyperbolicity applied
  -- to `u, w, x, y` forces `d u w = 0`.
  obtain ⟨w, hw, hxw⟩ := hσ.exists_dist_eq hσ.left_mem hσ.right_mem (d.nonneg x u)
    (hu ▸ le_add_of_nonneg_right (d.nonneg u y))
  have hwy := hσ.dist_add_dist hw
  have h₄ := hfour u w x y
  rw [d.symm u x, d.symm w x] at h₄
  clear hfour
  have huw : d u w = 0 := by grind [d.nonneg u w]
  exact d.eq_zero_iff.1 huw ▸ hw

/-- Axiom (T3) for a geodesic four-point `0`-hyperbolic `Λ`-metric space whose doubled Gromov
products are even. -/
private theorem exists_isSegment_inter_of_four_point (hgeo : d.IsGeodesic)
    (heven : ∀ v x y : X, Even (d v x + d v y - d x y))
    (hfour : ∀ x y z w : X, d x y + d z w ≤ max (d x z + d y w) (d x w + d y z))
    {σ τ : Set X} {x y z : X} (hσ : d.IsSegment σ x y) (hτ : d.IsSegment τ x z) :
    ∃ p q, d.IsSegment (σ ∩ τ) p q := by
  obtain ⟨c, hc⟩ := heven x y z
  have hc₀ : 0 ≤ c := by
    have htri := d.triangle y x z
    rw [d.symm y x] at htri
    clear hfour heven
    grind
  have hcy : c ≤ d x y := by
    have htri := d.triangle x y z
    clear hfour heven
    grind
  obtain ⟨w, hwσ, hxw⟩ := hσ.exists_dist_eq hσ.left_mem hσ.right_mem hc₀ hcy
  obtain ⟨ρ, hρ⟩ := d.isGeodesic_iff.1 hgeo x w
  -- Four-point `0`-hyperbolicity for `w, z, x, y` places `w` on `[x, z]`, so `σ ∩ τ = [x, w]`.
  have hwτ : d x w + d w z = d x z := by
    have hwy := hσ.dist_add_dist hwσ
    have h₄ := hfour w z x y
    have htri := d.triangle x w z
    rw [d.symm w x, d.symm z y, d.symm z x] at h₄
    clear hfour heven
    grind
  refine ⟨x, w, ?_⟩
  suffices h : σ ∩ τ = ρ from h ▸ hρ
  rw [eq_setOf_dist_add_dist_of_four_point hfour hσ,
    eq_setOf_dist_add_dist_of_four_point hfour hτ,
    eq_setOf_dist_add_dist_of_four_point hfour hρ]
  ext u
  simp only [mem_inter_iff, mem_ofPred_eq]
  refine ⟨fun ⟨huy, _⟩ => ?_, fun huw => ?_⟩
  · have huσ : u ∈ σ := by
      rw [eq_setOf_dist_add_dist_of_four_point hfour hσ]
      exact huy
    have hxu : d x u ≤ d x w := by
      have htri := d.triangle y u z
      rw [d.symm y u] at htri
      clear hfour heven
      grind
    rw [hσ.dist_eq_abs_sub huσ hwσ, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hxu), add_sub_cancel]
  · have hwy := hσ.dist_add_dist hwσ
    have h₁ := d.triangle x u y
    have h₂ := d.triangle u w y
    have h₃ := d.triangle x u z
    have h₄ := d.triangle u w z
    clear hfour heven
    exact ⟨by grind, by grind⟩

/-- Axiom (T2) for a geodesic four-point `0`-hyperbolic `Λ`-metric space whose doubled Gromov
products are even. -/
private theorem exists_isSegment_union_of_four_point (hgeo : d.IsGeodesic)
    (heven : ∀ v x y : X, Even (d v x + d v y - d x y))
    (hfour : ∀ x y z w : X, d x y + d z w ≤ max (d x z + d y w) (d x w + d y z))
    {σ τ : Set X} {x y z : X} (hσ : d.IsSegment σ x y) (hτ : d.IsSegment τ y z)
    (hστ : σ ∩ τ = {y}) : ∃ p q, d.IsSegment (σ ∪ τ) p q := by
  obtain ⟨ρ, hρ⟩ := d.isGeodesic_iff.1 hgeo x z
  -- The intersection `σ ∩ τ = {y}` forces `(x · z)_y = 0`, so `y` lies between `x` and `z`.
  obtain ⟨c, hc⟩ := heven y x z
  have hxyz : d x y + d y z = d x z := by
    have hcy : c ≤ d y x := by
      have htri := d.triangle y x z
      clear hfour heven
      grind
    have hcpos : 0 ≤ c := by
      have htri := d.triangle x y z
      rw [d.symm x y] at htri
      clear hfour heven
      grind
    obtain ⟨w, hwσ, hyw⟩ := hσ.symm.exists_dist_eq hσ.symm.left_mem hσ.symm.right_mem hcpos hcy
    have hwτ : w ∈ τ := by
      rw [eq_setOf_dist_add_dist_of_four_point hfour hτ]
      have hwx := hσ.symm.dist_add_dist hwσ
      have h₄ := hfour w z y x
      have htri := d.triangle y w z
      rw [d.symm w y, d.symm z x, d.symm z y] at h₄
      clear hfour heven
      grind
    have hwy : w = y := mem_singleton_iff.1 (hστ ▸ ⟨hwσ, hwτ⟩)
    rw [← hyw, hwy, d.refl, add_zero, d.symm y x] at hc
    clear hfour heven
    grind
  refine ⟨x, z, ?_⟩
  suffices h : σ ∪ τ = ρ from h ▸ hρ
  rw [eq_setOf_dist_add_dist_of_four_point hfour hσ,
    eq_setOf_dist_add_dist_of_four_point hfour hτ,
    eq_setOf_dist_add_dist_of_four_point hfour hρ]
  ext u
  simp only [mem_union, mem_ofPred_eq]
  refine ⟨?_, fun huxz => ?_⟩
  · rintro (huxy | hyuz)
    · have h₁ := d.triangle x u z
      have h₂ := d.triangle u y z
      clear hfour heven
      grind
    · have h₁ := d.triangle x u z
      have h₂ := d.triangle x y u
      clear hfour heven
      grind
  · have h₄ := hfour u y x z
    rw [d.symm u x, d.symm y x] at h₄
    rcases le_max_iff.1 h₄ with h₁ | h₂
    · have htri := d.triangle y u z
      clear hfour heven
      exact .inr (by rw [d.symm y u] at htri ⊢; grind)
    · have htri := d.triangle x u y
      clear hfour heven
      exact .inl (by grind)

/-- A nonempty geodesic `Λ`-metric space whose doubled Gromov products are even and which satisfies
the four-point `0`-hyperbolicity inequality is a `Λ`-tree (Chiswell, Theorem 2.1.6). -/
theorem isTree_of_four_point [Nonempty X] (hgeo : d.IsGeodesic)
    (heven : ∀ v x y : X, Even (d v x + d v y - d x y))
    (hfour : ∀ x y z w : X, d x y + d z w ≤ max (d x z + d y w) (d x w + d y z)) :
    d.IsTree where
  nonempty := ‹_›
  isGeodesic := hgeo
  exists_isSegment_inter := exists_isSegment_inter_of_four_point hgeo heven hfour
  exists_isSegment_union := exists_isSegment_union_of_four_point hgeo heven hfour

/-- A geodesic `Λ`-metric space with a base point `v₀` at which the doubled Gromov products are
even and `0`-hyperbolic is a `Λ`-tree (Chiswell, Theorem 2.1.6). -/
theorem isTree_of_isGeodesic (v₀ : X) (hgeo : d.IsGeodesic)
    (heven : ∀ x y : X, Even (d v₀ x + d v₀ y - d x y))
    (hhyp : ∀ x y z : X,
      min (d v₀ x + d v₀ y - d x y) (d v₀ y + d v₀ z - d y z) ≤ d v₀ x + d v₀ z - d x z) :
    d.IsTree :=
  have : Nonempty X := ⟨v₀⟩
  isTree_of_four_point hgeo (even_dist_add_dist_sub_dist_of_base heven)
    (four_point_of_min_dist_add_dist_sub_dist_le hhyp)

/-- A `Λ`-metric space is a `Λ`-tree if and only if it is nonempty and geodesic, its doubled Gromov
products are even, and it satisfies the four-point `0`-hyperbolicity inequality. -/
theorem isTree_iff_four_point :
    d.IsTree ↔ Nonempty X ∧ d.IsGeodesic ∧ (∀ v x y : X, Even (d v x + d v y - d x y)) ∧
      ∀ x y z w : X, d x y + d z w ≤ max (d x z + d y w) (d x w + d y z) :=
  ⟨fun hd => ⟨hd.nonempty, hd.isGeodesic, hd.even_dist_add_dist_sub_dist, hd.four_point⟩,
    fun ⟨_, hgeo, heven, hfour⟩ => isTree_of_four_point hgeo heven hfour⟩

end TauCeti.LambdaMetric
