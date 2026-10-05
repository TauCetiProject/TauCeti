/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric

/-!
# Hyperbolic perpendicular bisectors and distance dominance

For two points `p` and `q` of the upper half-plane, the points equidistant from them in the
hyperbolic metric are cut out by the equation `q.im * |z - p|² = p.im * |z - q|²` in the plane.
For distinct centres, the perpendicular bisector has zero invariant area. This is proved in
`TauCeti.Analysis.Complex.UpperHalfPlane.Bisector.Geometry` by identifying the equidistant locus
with a geodesic line.

Likewise, the points at least as close to `p` as to `q` (the distance-dominance, or Voronoi,
region of `p` relative to `q`) are cut out by the weak inequality
`q.im * |z - p|² ≤ p.im * |z - q|²` in the plane. This is the planar form of the defining
inequalities of a Dirichlet domain.

These planar characterizations describe the equality and dominance regions that occur in
Dirichlet domains.

## Main results

* `TauCeti.UpperHalfPlane.dist_eq_dist_iff`: the planar equation of the hyperbolic perpendicular
  bisector.
* `TauCeti.UpperHalfPlane.dist_le_dist_iff`: the planar inequality for the region of points at
  least as close to `p` as to `q`.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §9.4.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §3.2.
-/

public section

open UpperHalfPlane

namespace TauCeti.UpperHalfPlane

/-- A point is hyperbolically equidistant from `p` and `q` exactly when
`q.im * |z - p|² = p.im * |z - q|²` in the plane. -/
theorem dist_eq_dist_iff {z p q : ℍ} :
    dist z p = dist z q ↔ q.im * dist (z : ℂ) p ^ 2 = p.im * dist (z : ℂ) q ^ 2 := by
  have hz := z.im_pos
  have hp := p.im_pos
  have hq := q.im_pos
  have hcosh : dist z p = dist z q ↔ Real.cosh (dist z p) = Real.cosh (dist z q) := by
    simp only [le_antisymm_iff, Real.cosh_le_cosh, abs_of_nonneg dist_nonneg]
  rw [hcosh, cosh_dist, cosh_dist, add_right_inj, div_eq_div_iff (by positivity) (by positivity)]
  constructor <;> intro h <;> nlinarith [h]

/-- A point is hyperbolically at least as close to `p` as to `q` exactly when
`q.im * |z - p|² ≤ p.im * |z - q|²` in the plane. This is the planar form of a defining
inequality of a Dirichlet domain; compare Beardon, §9.4, and Katok, §3.2. -/
theorem dist_le_dist_iff {z p q : ℍ} :
    dist z p ≤ dist z q ↔ q.im * dist (z : ℂ) p ^ 2 ≤ p.im * dist (z : ℂ) q ^ 2 := by
  have hz := z.im_pos
  have hp := p.im_pos
  have hq := q.im_pos
  have hcosh : dist z p ≤ dist z q ↔ Real.cosh (dist z p) ≤ Real.cosh (dist z q) := by
    rw [Real.cosh_le_cosh]
    simp only [abs_of_nonneg dist_nonneg]
  rw [hcosh, cosh_dist, cosh_dist, add_le_add_iff_left,
    div_le_div_iff₀ (by positivity : 0 < 2 * z.im * p.im)
      (by positivity : 0 < 2 * z.im * q.im)]
  constructor <;> intro h <;> nlinarith [h]

end TauCeti.UpperHalfPlane
