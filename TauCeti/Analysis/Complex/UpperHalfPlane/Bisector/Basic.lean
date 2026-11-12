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

A height estimate also excludes low competing centres from a sufficiently high horizontal strip.

These planar characterizations describe the equality and dominance regions that occur in
Dirichlet domains.

## Main results

* `TauCeti.UpperHalfPlane.dist_eq_dist_iff`: the planar equation of the hyperbolic perpendicular
  bisector.
* `TauCeti.UpperHalfPlane.dist_le_dist_iff`: the planar inequality for the region of points at
  least as close to `p` as to `q`.
* `TauCeti.UpperHalfPlane.dist_le_dist_of_im_le_half`: low centres impose no constraint high in
  a strip.
* `TauCeti.UpperHalfPlane.dist_lt_dist_of_im_lt_half`: strictly lower centres are strictly
  farther away high in a strip.

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
  have hcosh : dist z p ≤ dist z q ↔ Real.cosh (dist z p) ≤ Real.cosh (dist z q) := by
    rw [Real.cosh_le_cosh]
    simp only [abs_of_nonneg dist_nonneg]
  rw [hcosh, cosh_dist, cosh_dist, add_le_add_iff_left,
    div_le_div_iff₀ (by positivity : 0 < 2 * z.im * p.im)
      (by positivity : 0 < 2 * z.im * q.im)]
  constructor <;> intro h <;> nlinarith [h]

/-- In a strip of horizontal half-width `r` about `p`, above height `p.im + r`, the excess of
`p.im * |z - q|²` over `q.im * |z - p|²` is at least `z.im² * (p.im - 2 * q.im)`. -/
private theorem sq_im_mul_sub_le_of_mem_strip {z p q : ℍ} {r : ℝ}
    (hzre : |z.re - p.re| ≤ r) (hzim : p.im + r ≤ z.im) :
    z.im ^ 2 * (p.im - 2 * q.im) ≤ p.im * dist (z : ℂ) q ^ 2 - q.im * dist (z : ℂ) p ^ 2 := by
  have hr : 0 ≤ r := (abs_nonneg _).trans hzre
  have hsq : (z.re - p.re) ^ 2 ≤ r ^ 2 := (sq_le_sq).mpr (by simpa [abs_of_nonneg hr])
  have hheight : p.im ^ 2 + r ^ 2 ≤ z.im ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ p.im + r) hzim 2
    nlinarith [mul_nonneg p.im_pos.le hr]
  have hnum : (z.re - p.re) ^ 2 + z.im ^ 2 + p.im ^ 2 ≤ 2 * z.im ^ 2 := by
    linarith
  simp only [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, coe_re, coe_im]
  have h₁ := mul_le_mul_of_nonneg_left hnum q.im_pos.le
  have h₃ := mul_nonneg p.im_pos.le (sq_nonneg (z.re - q.re))
  have h₄ := mul_nonneg p.im_pos.le (sq_nonneg q.im)
  nlinarith [z.im_pos]

/-- In a strip of horizontal half-width `r` about `p`, points above height `p.im + r` are
at least as close to `p` as to any point whose height is at most `p.im / 2`. -/
theorem dist_le_dist_of_im_le_half {z p q : ℍ} {r : ℝ}
    (hzre : |z.re - p.re| ≤ r) (hzim : p.im + r ≤ z.im)
    (hq : q.im ≤ p.im / 2) : dist z p ≤ dist z q := by
  rw [dist_le_dist_iff]
  nlinarith [sq_im_mul_sub_le_of_mem_strip (q := q) hzre hzim, sq_nonneg z.im]

/-- In a strip of horizontal half-width `r` about `p`, points above height `p.im + r` are
strictly closer to `p` than to any point whose height is less than `p.im / 2`. -/
theorem dist_lt_dist_of_im_lt_half {z p q : ℍ} {r : ℝ}
    (hzre : |z.re - p.re| ≤ r) (hzim : p.im + r ≤ z.im)
    (hq : q.im < p.im / 2) : dist z p < dist z q := by
  rw [← not_le, dist_le_dist_iff, not_le]
  nlinarith [sq_im_mul_sub_le_of_mem_strip (q := q) hzre hzim, pow_pos z.im_pos 2]

end TauCeti.UpperHalfPlane
