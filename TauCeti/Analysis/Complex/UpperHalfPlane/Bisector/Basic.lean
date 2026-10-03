/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
public import Mathlib.Geometry.Euclidean.PerpBisector
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import TauCeti.Analysis.Complex.UpperHalfPlane.Measure

/-!
# Hyperbolic perpendicular bisectors and distance dominance

For two points `p` and `q` of the upper half-plane, the points equidistant from them in the
hyperbolic metric are cut out by the equation `q.im * |z - p|² = p.im * |z - q|²` in the plane.
When `p ≠ q` this is a Euclidean line (if `p.im = q.im`) or a Euclidean circle, so the hyperbolic
perpendicular bisector of `p` and `q` has zero invariant area.

Likewise, the points at least as close to `p` as to `q` (the distance-dominance, or Voronoi,
region of `p` relative to `q`) are cut out by the weak inequality
`q.im * |z - p|² ≤ p.im * |z - q|²` in the plane. This is the planar form of the defining
inequalities of a Dirichlet domain.

This is the measure-theoretic input making the Dirichlet domain of a Fuchsian group a
fundamental domain: distinct translates of a Dirichlet domain meet only along such bisectors.

## Main results

* `TauCeti.UpperHalfPlane.dist_eq_dist_iff`: the planar equation of the hyperbolic perpendicular
  bisector.
* `TauCeti.UpperHalfPlane.dist_le_dist_iff`: the planar inequality for the region of points at
  least as close to `p` as to `q`.
* `TauCeti.UpperHalfPlane.volume_setOf_dist_eq_dist`: the hyperbolic perpendicular bisector of two
  distinct points is a null set.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, Graduate Texts in Mathematics 91,
  Springer, 1983, §9.4.
* Svetlana Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics, University of Chicago
  Press, 1992, §3.2.
-/

public section

open MeasureTheory Metric Set UpperHalfPlane

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

/-- The planar locus `q.im * |w - p|² = p.im * |w - q|²` of two distinct points of `ℍ` is a
Lebesgue null set: it is a line when `p.im = q.im` and a circle otherwise. -/
private theorem volume_setOf_im_mul_dist_sq_eq {p q : ℍ} (hpq : p ≠ q) :
    volume {w : ℂ | q.im * dist w p ^ 2 = p.im * dist w q ^ 2} = 0 := by
  have hpq' : (p : ℂ) ≠ q := fun h ↦ hpq (UpperHalfPlane.ext h)
  by_cases him : p.im = q.im
  · -- Equal heights: the locus is the Euclidean perpendicular bisector.
    refine measure_mono_null (fun w hw ↦ ?_) <|
      Measure.addHaar_affineSubspace volume (AffineSubspace.perpBisector (p : ℂ) q)
        (by simpa using hpq')
    rw [mem_ofPred_eq, him, mul_right_inj' q.im_pos.ne'] at hw
    exact AffineSubspace.mem_perpBisector_iff_dist_eq.mpr <|
      (sq_eq_sq₀ dist_nonneg dist_nonneg).mp hw
  · -- Different heights: the locus lies on a Euclidean circle.
    have hba : q.im - p.im ≠ 0 := sub_ne_zero.mpr (Ne.symm him)
    set c : ℝ := (q.im * p.re - p.im * q.re) / (q.im - p.im)
    set K : ℝ := c ^ 2 -
      (q.im * (p.re ^ 2 + p.im ^ 2) - p.im * (q.re ^ 2 + q.im ^ 2)) / (q.im - p.im)
    refine measure_mono_null (fun w hw ↦ ?_) (Measure.addHaar_sphere volume (c : ℂ) √K)
    rw [mem_ofPred_eq, Complex.dist_eq_re_im, Complex.dist_eq_re_im,
      Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), coe_re, coe_im, coe_re,
      coe_im] at hw
    have hK : (w.re - c) ^ 2 + w.im ^ 2 = K := by
      simp only [c, K]
      field_simp
      linear_combination (q.im - p.im) * hw
    rw [mem_sphere, Complex.dist_eq_re_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero, hK]
/-- **Hyperbolic perpendicular bisectors are null.** The points of `ℍ` equidistant from two
distinct points have zero invariant area. -/
theorem volume_setOf_dist_eq_dist {p q : ℍ} (hpq : p ≠ q) :
    volume {z : ℍ | dist z p = dist z q} = 0 :=
  measure_mono_null (fun _ hz ↦ dist_eq_dist_iff.mp hz) <|
    volume_preimage_coe_null (volume_setOf_im_mul_dist_sq_eq hpq)

end TauCeti.UpperHalfPlane
