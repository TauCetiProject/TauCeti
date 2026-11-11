/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.LambdaTree.Basic

/-!
# Geodesic `0`-hyperbolic `Λ`-metric spaces are `Λ`-trees

Let `(X, d)` be a `Λ`-metric space and `v` a point of `X`. The *Gromov product* of `x` and `y`
based at `v` is `(x · y)_v = (d v x + d v y - d x y) / 2`; we work with its double
`d v x + d v y - d x y`, which lies in `Λ`. The space is *`0`-hyperbolic with respect to `v`* when
`min ((x · y)_v, (y · z)_v) ≤ (x · z)_v` for all `x`, `y`, `z`.

In a `Λ`-tree the Gromov products lie in `Λ` and are `0`-hyperbolic with respect to every base
point (`TauCeti.LambdaMetric.IsTree.even_dist_add_dist_sub_dist` and
`TauCeti.LambdaMetric.IsTree.min_dist_add_dist_sub_dist_le`). This file proves the converse: a
geodesic `Λ`-metric space which, for *one* base point `v`, is `0`-hyperbolic and has its Gromov
products in `Λ`, is a `Λ`-tree. This is the criterion by which the spaces built from a based
`0`-hyperbolic object, such as a Lyndon length function, are shown to be `Λ`-trees.

Both conditions pass from one base point to every base point. Given them, a point of a segment
from `x` to `y` at distance at most `(y · z)_x` from `x` lies on every segment from `x` to `z`,
which gives (T3), and two segments from `w` whose other ends `x`, `y` satisfy `(x · y)_w = 0` have
a segment as their union, which gives (T2).

## Main results

* `TauCeti.LambdaMetric.IsSegment.union`: two segments with a common endpoint `w`, such that
  `d u u' = d u w + d w u'` for `u` in the first and `u'` in the second, have a segment as union.
* `TauCeti.LambdaMetric.even_dist_add_dist_sub_dist_of_forall`: if the Gromov products based at
  one point lie in `Λ`, so do those based at any point.
* `TauCeti.LambdaMetric.min_dist_add_dist_sub_dist_le_of_forall`: `0`-hyperbolicity with respect
  to one base point implies `0`-hyperbolicity with respect to any base point.
* `TauCeti.LambdaMetric.IsGeodesic.isTree`: a geodesic `Λ`-metric space which is `0`-hyperbolic
  and has its Gromov products in `Λ`, for one base point, is a `Λ`-tree.

## References

* I. Chiswell, *Introduction to Λ-trees*, World Scientific, 2001, §1.2 (`0`-hyperbolic
  `Λ`-metric spaces and the change of base point) and §2.4 (the criterion).
-/

public section

namespace TauCeti.LambdaMetric

open Set

variable {Λ X : Type*} [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]
  {d : LambdaMetric Λ X}

/-- If the Gromov products based at one point `v` lie in `Λ`, then so do the Gromov products
based at any point `t`. -/
theorem even_dist_add_dist_sub_dist_of_forall {v : X}
    (h : ∀ x y, Even (d v x + d v y - d x y)) (t x y : X) : Even (d t x + d t y - d x y) := by
  obtain ⟨a, ha⟩ := h t x
  obtain ⟨b, hb⟩ := h t y
  obtain ⟨c, hc⟩ := h x y
  exact ⟨d v t - a - b + c, by grind⟩

/-- A `Λ`-metric space which is `0`-hyperbolic with respect to one base point `v` is
`0`-hyperbolic with respect to any base point `t`. -/
theorem min_dist_add_dist_sub_dist_le_of_forall {v : X}
    (h : ∀ x y z, min (d v x + d v y - d x y) (d v y + d v z - d y z) ≤ d v x + d v z - d x z)
    (t x y z : X) :
    min (d t x + d t y - d x y) (d t y + d t z - d y z) ≤ d t x + d t z - d x z := by
  grind [h x y z, h t x y, h y t z, h t z y, h x t y, h x t z, d.symm y t, d.symm x t, d.symm z t,
    d.symm z y]

/-- The map gluing a parametrisation `f` of a segment on `[a, b]` to a parametrisation `g` on
`[a', b']` of a segment starting where the first one ends, the second translated to start at
`b`, is isometric when the common endpoint lies between the points of the two segments. -/
private theorem isometricOn_ite {f g : Λ → X} {a b a' b' : Λ} (hab : a ≤ b) (hab' : a' ≤ b')
    (hf : d.IsometricOn f (Icc a b)) (hg : d.IsometricOn g (Icc a' b')) (hg0 : g a' = f b)
    (h : ∀ u ∈ f '' Icc a b, ∀ u' ∈ g '' Icc a' b', d u u' = d u (f b) + d (f b) u') :
    d.IsometricOn (fun t => if t ≤ b then f t else g (t - b + a')) (Icc a (b + (b' - a'))) := by
  have hmem {t : Λ} (ht : t ∈ Icc a (b + (b' - a'))) (hbt : b < t) : t - b + a' ∈ Icc a' b' :=
    ⟨by grind, by grind⟩
  have hmix {s t : Λ} (hs : s ∈ Icc a (b + (b' - a'))) (ht : t ∈ Icc a (b + (b' - a')))
      (hsb : s ≤ b) (hbt : b < t) : d (f s) (g (t - b + a')) = |s - t| := by
    have hs' : s ∈ Icc a b := ⟨hs.1, hsb⟩
    rw [h _ (mem_image_of_mem f hs') _ (mem_image_of_mem g (hmem ht hbt)),
      hf.dist_eq hs' ⟨hab, le_rfl⟩, ← hg0, hg.dist_eq ⟨le_rfl, hab'⟩ (hmem ht hbt),
      abs_of_nonpos (by grind), abs_of_nonpos (by grind), abs_of_nonpos (by grind)]
    grind
  refine d.isometricOn_iff.2 fun s hs t ht => ?_
  rcases le_or_gt s b with hsb | hsb <;> rcases le_or_gt t b with htb | htb
  · simpa only [hsb, htb, ite_true] using hf.dist_eq ⟨hs.1, hsb⟩ ⟨ht.1, htb⟩
  · simpa only [hsb, htb.not_ge, ite_true, ite_false] using hmix hs ht hsb htb
  · simpa only [hsb.not_ge, htb, ite_true, ite_false, d.symm (g _), abs_sub_comm s] using
      hmix ht hs htb hsb
  · simpa only [hsb.not_ge, htb.not_ge, ite_false, add_sub_add_right_eq_sub,
      sub_sub_sub_cancel_right] using hg.dist_eq (hmem hs hsb) (hmem ht htb)

/-- The image of the glued parametrisation is the union of the two segments. -/
private theorem image_ite {f g : Λ → X} {a b a' b' : Λ} (hab : a ≤ b) (hab' : a' ≤ b')
    (hg0 : g a' = f b) :
    (fun t => if t ≤ b then f t else g (t - b + a')) '' Icc a (b + (b' - a')) =
      f '' Icc a b ∪ g '' Icc a' b' := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    by_cases htb : t ≤ b
    · exact .inl ⟨t, ⟨ht.1, htb⟩, by simp [htb]⟩
    · exact .inr ⟨t - b + a', ⟨by grind, by grind⟩, by simp [htb]⟩
  · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
    · exact ⟨s, ⟨hs.1, by grind⟩, by simp [hs.2]⟩
    · rcases hs.1.eq_or_lt with rfl | h0
      · exact ⟨b, ⟨hab, by grind⟩, by simp [hg0]⟩
      · have : ¬s - a' + b ≤ b := by grind
        exact ⟨s - a' + b, ⟨by grind, by grind⟩, by simp [this]⟩

namespace IsSegment

variable {σ τ : Set X} {x y z w : X}

/-- Two segments with a common endpoint `w` such that `w` lies between any point of the first
and any point of the second have a segment as their union. -/
theorem union (hσ : d.IsSegment σ x w) (hτ : d.IsSegment τ w y)
    (h : ∀ u ∈ σ, ∀ u' ∈ τ, d u u' = d u w + d w u') : d.IsSegment (σ ∪ τ) x y := by
  obtain ⟨a, b, f, hab, rfl, rfl, hf, rfl⟩ := isSegment_iff_exists_Icc.1 hσ
  obtain ⟨a', b', g, hab', hg0, rfl, hg, rfl⟩ := isSegment_iff_exists_Icc.1 hτ
  refine isSegment_iff_exists_Icc.2 ⟨a, b + (b' - a'),
    fun t => if t ≤ b then f t else g (t - b + a'), by grind, by simp [hab], ?_,
    isometricOn_ite hab hab' hf hg hg0 h, image_ite hab hab' hg0⟩
  rcases hab'.eq_or_lt with rfl | h0
  · simp [← hg0]
  · simp [h0]

/-- In a `Λ`-metric space which is `0`-hyperbolic with respect to `w`, two segments from `w`
whose other endpoints `x` and `y` satisfy `d x y = d x w + d w y`, that is, have Gromov product
`0` based at `w`, have a segment as their union. -/
theorem union_of_dist_eq
    (hw : ∀ x y z, min (d w x + d w y - d x y) (d w y + d w z - d y z) ≤ d w x + d w z - d x z)
    (hσ : d.IsSegment σ x w) (hτ : d.IsSegment τ w y) (hxy : d x y = d x w + d w y) :
    d.IsSegment (σ ∪ τ) x y := by
  refine hσ.union hτ fun u hu u' hu' => ?_
  rcases eq_or_ne u w with rfl | huw
  · simp
  rcases eq_or_ne u' w with rfl | hu'w
  · simp
  have h₁ := hσ.dist_add_dist hu
  have h₂ := hτ.dist_add_dist hu'
  grind [hw x u y, hw u u' y, d.triangle u w u', d.pos_iff.2 huw, d.pos_iff.2 hu'w, d.symm w x,
    d.symm w u, d.symm w u', d.symm u x, d.symm u' y, d.symm u' w]

/-- In a `Λ`-metric space which is `0`-hyperbolic with respect to `x`, a point of a segment from
`x` to `y` whose distance from `x` is at most the Gromov product of `y` and `z` based at `x` lies
on every segment from `x` to `z`. -/
theorem mem_of_two_nsmul_dist_le
    (hx : ∀ y z t, min (d x y + d x z - d y z) (d x z + d x t - d z t) ≤ d x y + d x t - d y t)
    (hσ : d.IsSegment σ x y) (hτ : d.IsSegment τ x z) {u : X} (hu : u ∈ σ)
    (h : 2 • d x u ≤ d x y + d x z - d y z) : u ∈ τ := by
  rw [two_nsmul] at h
  obtain ⟨u', hu', hd⟩ := hτ.exists_dist_eq hτ.left_mem hτ.right_mem (d.nonneg x u)
    (by grind [d.triangle x z y, d.symm z y])
  have h₁ := hσ.dist_add_dist hu
  have h₂ := hτ.dist_add_dist hu'
  have : d u u' = 0 := by
    grind [hx u y z, hx u z u', d.nonneg u u', d.symm z u']
  rwa [d.eq_zero_iff.1 this]

/-- In a `Λ`-metric space which is `0`-hyperbolic with respect to `x`, two segments from `x`, to
`y` and to `z`, intersect in a segment from `x` when the Gromov product of `y` and `z` based at
`x` lies in `Λ`: the intersection is the part of either segment up to that distance from `x`. -/
theorem exists_isSegment_inter
    (hx : ∀ y z t, min (d x y + d x z - d y z) (d x z + d x t - d z t) ≤ d x y + d x t - d y t)
    (heven : Even (d x y + d x z - d y z)) (hσ : d.IsSegment σ x y) (hτ : d.IsSegment τ x z) :
    ∃ w, d.IsSegment (σ ∩ τ) x w := by
  obtain ⟨c, hc⟩ := heven
  have hc0 : 0 ≤ c := by grind [d.triangle y x z, d.symm y x]
  obtain ⟨w, hw, hwc⟩ := hσ.exists_dist_eq hσ.left_mem hσ.right_mem hc0
    (by grind [d.triangle x y z])
  refine ⟨w, ?_⟩
  convert hσ.isSegment_sep hσ.left_mem hw using 1
  ext u
  simp only [mem_inter_iff, mem_sep_iff, d.refl, hwc, uIcc_of_le hc0, mem_Icc]
  refine ⟨fun ⟨hu, hu'⟩ => ⟨hu, d.nonneg x u, ?_⟩, fun ⟨hu, _, hu'⟩ => ⟨hu, ?_⟩⟩
  · grind [hσ.dist_add_dist hu, hτ.dist_add_dist hu', d.triangle y u z, d.symm u y]
  · exact hσ.mem_of_two_nsmul_dist_le hx hτ hu (by rw [two_nsmul]; grind)

end IsSegment

/-- A geodesic `Λ`-metric space which, for some base point `v`, has its Gromov products
`(x · y)_v` in `Λ` and is `0`-hyperbolic, `min ((x · y)_v, (y · z)_v) ≤ (x · z)_v`, is a `Λ`-tree.
Both conditions are stated for the doubled Gromov products `d v x + d v y - d x y`. -/
theorem IsGeodesic.isTree (hd : d.IsGeodesic) (v : X)
    (heven : ∀ x y, Even (d v x + d v y - d x y))
    (hhyp : ∀ x y z,
      min (d v x + d v y - d x y) (d v y + d v z - d y z) ≤ d v x + d v z - d x z) :
    d.IsTree where
  nonempty := ⟨v⟩
  isGeodesic := hd
  exists_isSegment_union {σ τ x y z} hσ hτ hστ := by
    have hy := min_dist_add_dist_sub_dist_le_of_forall hhyp y
    -- The point of `σ` at distance `(x · z)_y` from `y` lies on `τ`, so it is `y`.
    obtain ⟨c, hc⟩ := even_dist_add_dist_sub_dist_of_forall heven y x z
    obtain ⟨w, hw, hwc⟩ := hσ.symm.exists_dist_eq hσ.right_mem hσ.left_mem (r := c)
      (by grind [d.triangle x y z, d.symm x y]) (by grind [d.triangle y x z])
    have hwτ : w ∈ τ := hσ.symm.mem_of_two_nsmul_dist_le hy hτ hw (by rw [hwc, two_nsmul, hc])
    have hwy : w = y := by
      rw [← mem_singleton_iff, ← hστ]
      exact ⟨hw, hwτ⟩
    rw [hwy, d.refl] at hwc
    exact ⟨x, z, hσ.union_of_dist_eq hy hτ (by grind [d.symm x y])⟩
  exists_isSegment_inter {σ τ x y z} hσ hτ :=
    ⟨x, hσ.exists_isSegment_inter (min_dist_add_dist_sub_dist_le_of_forall hhyp x)
      (even_dist_add_dist_sub_dist_of_forall heven x y z) hτ⟩

end TauCeti.LambdaMetric
