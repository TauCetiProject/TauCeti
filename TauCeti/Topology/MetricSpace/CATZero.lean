/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.Convex.Strong
public import Mathlib.Geometry.Euclidean.Triangle
public import TauCeti.Analysis.Convex.Midpoint
public import TauCeti.Topology.MetricSpace.Length

/-!
# CAT(0) spaces

A geodesic space is CAT(0) when its geodesic triangles are no fatter than their Euclidean
comparison triangles. This file uses the equivalent two-point form of Bruhat and Tits: a geodesic
space is CAT(0) exactly when every midpoint `m` of two points `x, y` satisfies the *CN inequality*

`d(z, m)² ≤ (d(z, x)² + d(z, y)²) / 2 - d(x, y)² / 4` for every `z`.

In a Euclidean space this is an equality, Apollonius's theorem, so the inequality says that
distances to a midpoint are at most their Euclidean values. Completeness is not assumed; a complete
CAT(0) space is a Hadamard space.

The CN inequality propagates from midpoints to the whole of a geodesic segment: the squared
distance from a fixed point is strongly convex along every geodesic segment. This is the convexity
that makes barycenters of probability measures unique in CAT(0) spaces.

## Main definitions

* `TauCeti.IsCATZeroSpace X` — `X` is a geodesic space satisfying the CN inequality at every
  midpoint.

## Main results

* `TauCeti.IsGeodesicSegment.strongConvexOn_dist_sq` — along a geodesic segment `γ` from `x` to
  `y` in a CAT(0) space, `t ↦ d(z, γ t)²` is `2 d(x, y)²`-strongly convex on `[0, 1]`.
* `TauCeti.IsGeodesicSegment.dist_sq_le` — the resulting comparison inequality
  `d(z, γ t)² ≤ (1 - t) d(z, x)² + t d(z, y)² - t (1 - t) d(x, y)²`.
* `TauCeti.IsCATZeroSpace.of_normedAddTorsor` and `TauCeti.instIsCATZeroSpace` — real inner
  product spaces, and Euclidean affine spaces over them, are CAT(0).

## References

* M. R. Bridson and A. Haefliger, *Metric Spaces of Non-Positive Curvature*, Grundlehren der
  mathematischen Wissenschaften 319, Springer, 1999, Chapter II.1, Exercise 1.9(1).
* F. Bruhat and J. Tits, *Groupes réductifs sur un corps local*, Publ. Math. IHÉS 41 (1972),
  5--251, §3.2.
* K.-T. Sturm, *Probability measures on metric spaces of nonpositive curvature*, in *Heat
  Kernels and Analysis on Manifolds, Graphs, and Metric Spaces*, Contemp. Math. 338 (2003),
  357--390.
-/

public section

namespace TauCeti

open Set

/-- A *CAT(0) space*, in the Bruhat--Tits form: a geodesic space in which every midpoint `m` of two
points `x, y` satisfies the CN inequality `d(z, m)² ≤ (d(z, x)² + d(z, y)²) / 2 - d(x, y)² / 4`
for every `z`. For geodesic spaces this is equivalent to the comparison-triangle definition. -/
class IsCATZeroSpace (X : Type*) [PseudoMetricSpace X] : Prop extends IsGeodesicSpace X where
  /-- The CN inequality of Bruhat and Tits at a midpoint `m` of `x` and `y`. -/
  dist_sq_le_of_dist_eq_half {x y m : X} (hx : dist x m = dist x y / 2)
    (hy : dist m y = dist x y / 2) (z : X) :
    dist z m ^ 2 ≤ (dist z x ^ 2 + dist z y ^ 2) / 2 - dist x y ^ 2 / 4

variable {X : Type*} [PseudoMetricSpace X] [IsCATZeroSpace X] {γ : ℝ → X} {x y : X}

/-- **Strong convexity of the squared distance in a CAT(0) space.** Along a geodesic segment `γ`
from `x` to `y`, the squared distance `t ↦ d(z, γ t)²` from any point `z` is
`2 d(x, y)²`-strongly convex on `[0, 1]`. -/
theorem IsGeodesicSegment.strongConvexOn_dist_sq (hγ : IsGeodesicSegment γ x y) (z : X) :
    StrongConvexOn (Icc 0 1) (2 * dist x y ^ 2) fun t => dist z (γ t) ^ 2 := by
  rw [strongConvexOn_iff_convex]
  have hcont : ContinuousOn (fun t => dist z (γ t)) (Icc 0 1) :=
    (continuous_const.dist continuous_id).comp_continuousOn hγ.continuousOn
  refine convexOn_of_midpoint (convex_Icc 0 1) ((hcont.pow 2).sub (by fun_prop))
    fun s hs t ht => ?_
  have hm : midpoint ℝ s t = (s + t) / 2 := by
    rw [midpoint_eq_smul_add, smul_eq_mul, invOf_eq_inv, ← div_eq_inv_mul]
  have hmI : midpoint ℝ s t ∈ Icc (0 : ℝ) 1 := (convex_Icc 0 1).midpoint_mem hs ht
  -- `γ` at the parameter midpoint is a midpoint of `γ s` and `γ t`.
  have hst : dist (γ s) (γ t) = |s - t| * dist x y := hγ.dist_eq s hs t ht
  have hcn := IsCATZeroSpace.dist_sq_le_of_dist_eq_half
    (x := γ s) (y := γ t) (m := γ (midpoint ℝ s t))
    (by rw [hγ.dist_eq s hs _ hmI, hst, hm, show s - (s + t) / 2 = (s - t) / 2 by ring, abs_div,
      abs_two]; ring)
    (by rw [hγ.dist_eq _ hmI t ht, hst, hm, show (s + t) / 2 - t = (s - t) / 2 by ring, abs_div,
      abs_two]; ring) z
  rw [hst, mul_pow, sq_abs] at hcn
  simp only [Real.norm_eq_abs, sq_abs, hm] at hcn ⊢
  linarith

/-- **The CAT(0) comparison inequality along a geodesic segment.** If `γ` is a geodesic segment
from `x` to `y` in a CAT(0) space, then for every `z` and `t ∈ [0, 1]`,
`d(z, γ t)² ≤ (1 - t) d(z, x)² + t d(z, y)² - t (1 - t) d(x, y)²`. -/
theorem IsGeodesicSegment.dist_sq_le (hγ : IsGeodesicSegment γ x y) (z : X) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    dist z (γ t) ^ 2 ≤
      (1 - t) * dist z x ^ 2 + t * dist z y ^ 2 - t * (1 - t) * dist x y ^ 2 := by
  have h := (hγ.strongConvexOn_dist_sq z).2 (left_mem_Icc.2 zero_le_one)
    (right_mem_Icc.2 zero_le_one) (sub_nonneg.2 ht.2) ht.1 (sub_add_cancel 1 t)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_sub, norm_neg, norm_one, one_pow,
    hγ.source, hγ.target] at h
  linarith

/-- A Euclidean affine space, a metric torsor over a real inner product space, is CAT(0): the CN
inequality is Apollonius's theorem. This is a theorem rather than an instance because the acting
space `V` cannot be found from the torsor; see `TauCeti.instIsCATZeroSpace` for the case of an
inner product space acting on itself. -/
theorem IsCATZeroSpace.of_normedAddTorsor {V P : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P] : IsCATZeroSpace P where
  toIsGeodesicSpace := IsGeodesicSpace.of_normedAddTorsor (V := V)
  dist_sq_le_of_dist_eq_half {x y m} hx hy z := by
    obtain rfl := eq_midpoint_of_dist_eq_half hx hy
    have := EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
      z x y
    linarith

/-- A real inner product space is CAT(0). -/
instance instIsCATZeroSpace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    IsCATZeroSpace E :=
  IsCATZeroSpace.of_normedAddTorsor (V := E)

end TauCeti
