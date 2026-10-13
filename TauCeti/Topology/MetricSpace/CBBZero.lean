/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Geometry.Euclidean.Triangle
public import TauCeti.Analysis.Convex.Midpoint
public import TauCeti.Topology.MetricSpace.Length

/-!
# Spaces of nonnegative curvature in the sense of Alexandrov

A geodesic space has *curvature bounded below by `0`*, or is *CBB(0)*, when its geodesic triangles
are no thinner than their Euclidean comparison triangles. This file uses the two-point form of the
condition: every midpoint `m` of two points `x, y` satisfies the *reverse CN inequality*

`d(z, m)² ≥ (d(z, x)² + d(z, y)²) / 2 - d(x, y)² / 4` for every `z`.

In a Euclidean space this is an equality, Apollonius's theorem, so the inequality says that
distances to a midpoint are at least their Euclidean values. It is the inequality of
`TauCeti.IsCATZeroSpace` reversed; the lower and the upper curvature bound are separate classes.

The inequality propagates from midpoints to the whole of a geodesic segment. Along a geodesic
segment `γ` from `x` to `y` the function `t ↦ d(z, γ t)² - d(x, y)² t²` is concave, which gives the
*point-on-side comparison*: the distance from `z` to the point at time `t` is at least the
corresponding distance in the Euclidean comparison triangle. Testing this comparison against a
second geodesic segment shows that geodesics cannot branch.

## Main definitions

* `TauCeti.IsCBBZeroSpace X` — `X` is a geodesic space satisfying the reverse CN inequality at
  every midpoint.

## Main results

* `TauCeti.IsGeodesicSegment.concaveOn_dist_sq_sub` — along a geodesic segment `γ` from `x` to `y`
  in a CBB(0) space, `t ↦ d(z, γ t)² - d(x, y)² t²` is concave on `[0, 1]`.
* `TauCeti.IsGeodesicSegment.le_dist_sq` — the point-on-side comparison
  `(1 - t) d(z, x)² + t d(z, y)² - t (1 - t) d(x, y)² ≤ d(z, γ t)²`.
* `TauCeti.IsGeodesicSegment.eqOn_of_apply_eq` — geodesics do not branch: two geodesic segments
  from the same point that meet at a positive time agree from then on.
* `TauCeti.IsCBBZeroSpace.of_isometryEquiv` — the condition is invariant under isometries.
* `TauCeti.IsCBBZeroSpace.of_normedAddTorsor` and `TauCeti.instIsCBBZeroSpace` — real inner product
  spaces, and Euclidean affine spaces over them, are CBB(0).
* `TauCeti.not_isCBBZeroSpace_real_prod` — the plane `ℝ × ℝ` with its sup metric is a geodesic
  space that is not CBB(0), because its geodesics branch.

## References

* D. Burago, Yu. Burago and S. Ivanov, *A Course in Metric Geometry*, Graduate Studies in
  Mathematics 33, AMS, 2001, Chapter 4 and Chapter 10.
* S. Alexander, V. Kapovitch and A. Petrunin, *Alexandrov Geometry: Foundations*, Graduate Studies
  in Mathematics 236, AMS, 2024.
-/

public section

namespace TauCeti

open Set

/-- A *CBB(0) space*, or space of nonnegative curvature in the sense of Alexandrov: a geodesic
space in which every midpoint `m` of two points `x, y` satisfies the reverse CN inequality
`(d(z, x)² + d(z, y)²) / 2 - d(x, y)² / 4 ≤ d(z, m)²` for every `z`. The point-on-side comparison
along whole geodesic segments, the comparison-triangle form of the condition, follows:
`TauCeti.IsGeodesicSegment.le_dist_sq`. -/
class IsCBBZeroSpace (X : Type*) [PseudoMetricSpace X] : Prop extends IsGeodesicSpace X where
  /-- The reverse CN inequality at a midpoint `m` of `x` and `y`. -/
  le_dist_sq_of_dist_eq_half {x y m : X} (hx : dist x m = dist x y / 2)
    (hy : dist m y = dist x y / 2) (z : X) :
    (dist z x ^ 2 + dist z y ^ 2) / 2 - dist x y ^ 2 / 4 ≤ dist z m ^ 2

section PseudoMetricSpace

variable {X : Type*} [PseudoMetricSpace X] [IsCBBZeroSpace X] {γ : ℝ → X} {x y : X}

/-- **Semiconcavity of the squared distance in a CBB(0) space.** Along a geodesic segment `γ` from
`x` to `y`, the function `t ↦ d(z, γ t)² - d(x, y)² t²` is concave on `[0, 1]`. -/
theorem IsGeodesicSegment.concaveOn_dist_sq_sub (hγ : IsGeodesicSegment γ x y) (z : X) :
    ConcaveOn ℝ (Icc 0 1) fun t => dist z (γ t) ^ 2 - dist x y ^ 2 * t ^ 2 := by
  rw [← neg_convexOn_iff]
  have hcont : ContinuousOn (fun t => dist z (γ t)) (Icc 0 1) :=
    (continuous_const.dist continuous_id).comp_continuousOn hγ.continuousOn
  refine convexOn_of_midpoint (convex_Icc 0 1) ((hcont.pow 2).sub (by fun_prop)).neg
    fun s hs t ht => ?_
  have hm : midpoint ℝ s t = (s + t) / 2 := by
    rw [midpoint_eq_smul_add, smul_eq_mul, invOf_eq_inv, ← div_eq_inv_mul]
  -- `γ` at the parameter midpoint is a midpoint of `γ s` and `γ t`.
  have hcn := IsCBBZeroSpace.le_dist_sq_of_dist_eq_half
    (hγ.dist_apply_apply_midpoint hs ht) (hγ.dist_apply_midpoint_apply hs ht) z
  rw [hγ.dist_eq s hs t ht, mul_pow, sq_abs, hm] at hcn
  simp only [Pi.neg_apply, hm]
  linear_combination hcn

/-- **The point-on-side comparison in a CBB(0) space.** If `γ` is a geodesic segment from `x` to
`y`, then for every `z` and `t ∈ [0, 1]`,
`(1 - t) d(z, x)² + t d(z, y)² - t (1 - t) d(x, y)² ≤ d(z, γ t)²`: the distance from `z` to `γ t`
is at least the corresponding distance in the Euclidean comparison triangle. -/
theorem IsGeodesicSegment.le_dist_sq (hγ : IsGeodesicSegment γ x y) (z : X) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 - t * (1 - t) * dist x y ^ 2 ≤
      dist z (γ t) ^ 2 := by
  have h := (hγ.concaveOn_dist_sq_sub z).2 (left_mem_Icc.2 zero_le_one)
    (right_mem_Icc.2 zero_le_one) (sub_nonneg.2 ht.2) ht.1 (sub_add_cancel 1 t)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, hγ.source, hγ.target] at h
  linear_combination h

/-- A space isometric to a CBB(0) space is CBB(0). -/
theorem IsCBBZeroSpace.of_isometryEquiv {Y : Type*} [PseudoMetricSpace Y] (e : X ≃ᵢ Y) :
    IsCBBZeroSpace Y where
  toIsGeodesicSpace := IsGeodesicSpace.of_isometryEquiv e
  le_dist_sq_of_dist_eq_half {x y m} hx hy z := by
    simpa only [e.symm.dist_eq] using IsCBBZeroSpace.le_dist_sq_of_dist_eq_half (x := e.symm x)
      (y := e.symm y) (m := e.symm m) (by simpa only [e.symm.dist_eq] using hx)
      (by simpa only [e.symm.dist_eq] using hy) (e.symm z)

end PseudoMetricSpace

/-- **Geodesics do not branch in a CBB(0) space.** Two geodesic segments `γ` and `σ` starting at
the same point `x` that pass through the same point at a time `s ∈ (0, 1]` agree at every time in
`[s, 1]`; in particular they end at the same point. -/
theorem IsGeodesicSegment.eqOn_of_apply_eq {X : Type*} [MetricSpace X] [IsCBBZeroSpace X]
    {γ σ : ℝ → X} {x y y' : X} (hγ : IsGeodesicSegment γ x y) (hσ : IsGeodesicSegment σ x y')
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) (h : γ s = σ s) : EqOn γ σ (Icc s 1) := by
  intro t ht
  have hs' : s ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hs
  have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le.trans ht.1, ht.2⟩
  have htpos : 0 < t := hs.1.trans_le ht.1
  -- The two segments have the same speed, since they reach the same point at time `s`.
  have hℓ : dist x y' = dist x y := by
    have h1 := hγ.dist_source_apply hs'
    have h2 := hσ.dist_source_apply hs'
    rw [h] at h1
    exact mul_left_cancel₀ hs.1.ne' (h2.symm.trans h1)
  -- On the piece of `γ` from `x` to `γ t`, the point `γ s` sits at time `s / t`. Comparing it with
  -- `σ t`, which is as far from `x` as `γ t` and as far from `γ s = σ s` as the piece predicts,
  -- forces `σ t = γ t`.
  have hτ := hγ.comp_lineMap (left_mem_Icc.2 zero_le_one) ht'
  rw [hγ.source] at hτ
  set r := s / t with hr
  have hrI : r ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg hs.1.le htpos.le, (div_le_one htpos).2 ht.1⟩
  have hrpos : 0 < r := div_pos hs.1 htpos
  have hsr : s = r * t := by rw [hr, div_mul_cancel₀ s htpos.ne']
  have hτr : AffineMap.lineMap (0 : ℝ) t r = s := by
    rw [AffineMap.lineMap_apply_ring', hsr]
    ring
  have key := hτ.le_dist_sq (σ t) hrI
  rw [hτr, h, dist_comm (σ t) x, hσ.dist_source_apply ht', hγ.dist_source_apply ht',
    hσ.dist_eq t ht' s hs', hℓ, hsr] at key
  have habs : |t - r * t| ^ 2 = (t - r * t) ^ 2 := sq_abs _
  have hD : r * dist (σ t) (γ t) ^ 2 ≤ r * 0 := by linear_combination key + dist x y ^ 2 * habs
  have hD' := le_antisymm ((mul_le_mul_iff_of_pos_left hrpos).1 hD) (sq_nonneg _)
  exact (dist_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hD')).symm

/-- A Euclidean affine space, a metric torsor over a real inner product space, is CBB(0): the
reverse CN inequality is Apollonius's theorem. This is a theorem rather than an instance because
the acting space `V` cannot be found from the torsor; see `TauCeti.instIsCBBZeroSpace` for the case
of an inner product space acting on itself. -/
theorem IsCBBZeroSpace.of_normedAddTorsor {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] : IsCBBZeroSpace P where
  toIsGeodesicSpace := IsGeodesicSpace.of_normedAddTorsor (V := V)
  le_dist_sq_of_dist_eq_half {x y m} hx hy z := by
    obtain rfl := eq_midpoint_of_dist_eq_half hx hy
    have := EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
      z x y
    linarith

/-- A real inner product space is CBB(0). -/
instance instIsCBBZeroSpace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    IsCBBZeroSpace E :=
  IsCBBZeroSpace.of_normedAddTorsor (V := E)

/-- The plane `ℝ × ℝ` with its sup metric is a geodesic space that is not CBB(0). The horizontal
segment from `(0, 0)` to `(1, 0)` and the segment that leaves it at `(1 / 2, 0)` to rise towards
`(1, 1 / 2)` are both geodesic segments of length `1`, so they branch, contradicting
`TauCeti.IsGeodesicSegment.eqOn_of_apply_eq`. -/
theorem not_isCBBZeroSpace_real_prod : ¬ IsCBBZeroSpace (ℝ × ℝ) := by
  intro _
  have hγ : IsGeodesicSegment (fun t : ℝ => (t, (0 : ℝ))) 0 (1, 0) :=
    ⟨rfl, rfl, fun s _ t _ => by simp [Prod.dist_eq, Real.dist_eq]⟩
  have hσ : IsGeodesicSegment (fun t : ℝ => (t, max (t - 1 / 2) 0)) 0 (1, 1 / 2) := by
    refine ⟨by norm_num, by norm_num, fun s _ t _ => ?_⟩
    have hle : |max (s - 1 / 2) 0 - max (t - 1 / 2) 0| ≤ |s - t| := by
      simpa using abs_max_sub_max_le_abs (s - 1 / 2) (t - 1 / 2) 0
    norm_num [Prod.dist_eq, Real.dist_eq, max_eq_left hle]
  have h := hγ.eqOn_of_apply_eq hσ (s := 1 / 2) ⟨by norm_num, by norm_num⟩ (by norm_num)
    ⟨by norm_num, le_rfl⟩
  norm_num at h

end TauCeti
