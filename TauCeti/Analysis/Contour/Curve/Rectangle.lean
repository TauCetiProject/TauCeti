/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Complex.ReImTopology
public import TauCeti.Analysis.Contour.Cycle.Polygon

/-!
# The boundary of a rectangle as a closed polygonal curve

For two complex numbers `z` and `w`, Mathlib's `Complex.Rectangle z w` is the closed axis-parallel
rectangle `[[z.re, w.re]] ×ℂ [[z.im, w.im]]` with opposite corners `z` and `w`. This file
parametrizes its boundary as a closed piecewise-`C¹` curve `Complex.rectBoundary z w` on the
parameter interval `[0, 4]`: it starts at `z` and runs, one unit of time per edge, through the
corners `w.re + z.im * I`, `w` and `z.re + w.im * I` back to `z`. When `z` is the lower left corner
this is the counterclockwise orientation, and the four edges are the bottom, right, top and left
edges in that order.

The curve is the boundary parametrization of the four-vertex polygon `Complex.rectPolygon z w`,
so it inherits the polygonal contour API. Its trace is exactly the topological frontier of the
rectangle, including in the degenerate cases, where the rectangle is a segment or a point and the
curve traverses it back and forth. Its contour integral splits into the four edge integrals in
the form used by Mathlib's Cauchy theorem for rectangles,
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`.

## Main definitions

* `Complex.rectPolygon z w`: the polygon with vertices `z`, `w.re + z.im * I`, `w`,
  `z.re + w.im * I`.
* `Complex.rectBoundary z w`: its boundary parametrization, a closed curve on `[0, 4]`.

## Main results

* `Complex.rectBoundary_of_mem_Icc_zero_one` and its three companions: the explicit edges.
* `Complex.isPiecewiseC1On_rectBoundary`: the curve is piecewise `C¹` on `[0, 4]`.
* `Complex.rectBoundary_four`: it is closed.
* `Complex.frontier_rectangle`, `Complex.interior_rectangle`: the frontier of a rectangle is the
  union of its four edges, and its interior is the open rectangle.
* `Complex.image_rectBoundary`: the trace of the curve is `frontier (Rectangle z w)`.
* `Complex.integral_rectBoundary`: its contour integral is the signed sum of the four edge
  integrals.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace Complex

/-- The rectangle with opposite corners `z` and `w` as a polygon with four vertices: `z`,
`w.re + z.im * I`, `w` and `z.re + w.im * I`, in that order. When `z` is the lower left corner the
vertices are listed counterclockwise. -/
def rectPolygon (z w : ℂ) : Polygon ℂ 4 :=
  ⟨![z, w.re + z.im * I, w, z.re + w.im * I]⟩

/-- The vertices of the rectangle polygon. -/
@[simp]
theorem rectPolygon_apply (z w : ℂ) (i : Fin 4) :
    rectPolygon z w i = ![z, w.re + z.im * I, w, z.re + w.im * I] i := (rfl)

/-- The boundary of the rectangle `Rectangle z w` as a closed polygonal curve on `[0, 4]`. It runs
along the edge from `z` to `w.re + z.im * I` on `[0, 1]`, to `w` on `[1, 2]`, to
`z.re + w.im * I` on `[2, 3]`, and back to `z` on `[3, 4]`; outside `[0, 4]` it continues
periodically. When `z` is the lower left corner the orientation is counterclockwise. -/
def rectBoundary (z w : ℂ) : ℝ → ℂ :=
  (rectPolygon z w).boundaryParam

/-- The rectangle boundary is the boundary parametrization of the rectangle polygon. -/
theorem rectBoundary_def (z w : ℂ) :
    rectBoundary z w = (rectPolygon z w).boundaryParam := (rfl)

variable {z w : ℂ}

/-- The rectangle boundary starts at the corner `z`. -/
@[simp]
theorem rectBoundary_zero (z w : ℂ) : rectBoundary z w 0 = z := by
  simpa [rectBoundary_def] using (rectPolygon z w).boundaryParam_natCast 0

/-- After one unit of time the rectangle boundary reaches the corner `w.re + z.im * I`. -/
@[simp]
theorem rectBoundary_one (z w : ℂ) : rectBoundary z w 1 = w.re + z.im * I := by
  simpa [rectBoundary_def] using (rectPolygon z w).boundaryParam_natCast 1

/-- After two units of time the rectangle boundary reaches the opposite corner `w`. -/
@[simp]
theorem rectBoundary_two (z w : ℂ) : rectBoundary z w 2 = w := by
  simpa [rectBoundary_def] using (rectPolygon z w).boundaryParam_natCast 2

/-- After three units of time the rectangle boundary reaches the corner `z.re + w.im * I`. -/
@[simp]
theorem rectBoundary_three (z w : ℂ) : rectBoundary z w 3 = z.re + w.im * I := by
  simpa [rectBoundary_def] using (rectPolygon z w).boundaryParam_natCast 3

/-- The rectangle boundary has period `4`. -/
theorem periodic_rectBoundary (z w : ℂ) : Function.Periodic (rectBoundary z w) 4 := by
  simpa [rectBoundary_def] using (rectPolygon z w).periodic_boundaryParam

/-- The rectangle boundary is closed: after four units of time it is back at `z`. -/
@[simp]
theorem rectBoundary_four (z w : ℂ) : rectBoundary z w 4 = z := by
  simpa using periodic_rectBoundary z w 0

/-- On the cell `[i, i + 1]` the rectangle boundary runs along the edge from vertex `i` to the
next vertex. -/
private theorem rectBoundary_eq_lineMap (i : Fin 4) {t : ℝ}
    (ht : t ∈ Icc ((i : ℕ) : ℝ) ((i : ℕ) + 1)) :
    rectBoundary z w t = AffineMap.lineMap (rectPolygon z w i)
      (rectPolygon z w (finRotate 4 i)) (t - (i : ℕ)) := by
  have h := (rectPolygon z w).boundaryParam_natCast_add i (s := t - (i : ℕ))
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  rwa [add_sub_cancel] at h

/-- On `[0, 1]` the rectangle boundary runs along the bottom edge, from `z` to
`w.re + z.im * I`. -/
theorem rectBoundary_of_mem_Icc_zero_one {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    rectBoundary z w t = (z.re + t * (w.re - z.re) : ℝ) + z.im * I := by
  rw [rectBoundary_eq_lineMap 0 (by simpa using ht), AffineMap.lineMap_apply_module']
  apply Complex.ext <;> simp [finRotate_apply]
  ring

/-- On `[1, 2]` the rectangle boundary runs along the right edge, from `w.re + z.im * I` to `w`. -/
theorem rectBoundary_of_mem_Icc_one_two {t : ℝ} (ht : t ∈ Icc (1 : ℝ) 2) :
    rectBoundary z w t = w.re + (z.im + (t - 1) * (w.im - z.im) : ℝ) * I := by
  rw [rectBoundary_eq_lineMap 1 (by norm_num; exact ht), AffineMap.lineMap_apply_module']
  apply Complex.ext <;> simp [finRotate_apply]
  ring

/-- On `[2, 3]` the rectangle boundary runs along the top edge, from `w` to `z.re + w.im * I`. -/
theorem rectBoundary_of_mem_Icc_two_three {t : ℝ} (ht : t ∈ Icc (2 : ℝ) 3) :
    rectBoundary z w t = (w.re + (t - 2) * (z.re - w.re) : ℝ) + w.im * I := by
  rw [rectBoundary_eq_lineMap 2 (by norm_num; exact ht), AffineMap.lineMap_apply_module']
  apply Complex.ext <;> simp [finRotate_apply]
  ring

/-- On `[3, 4]` the rectangle boundary runs along the left edge, from `z.re + w.im * I` back
to `z`. -/
theorem rectBoundary_of_mem_Icc_three_four {t : ℝ} (ht : t ∈ Icc (3 : ℝ) 4) :
    rectBoundary z w t = z.re + (w.im + (t - 3) * (z.im - w.im) : ℝ) * I := by
  rw [rectBoundary_eq_lineMap 3 (by norm_num; exact ht), AffineMap.lineMap_apply_module']
  apply Complex.ext <;> simp [finRotate_apply]
  ring

/-- The rectangle boundary is piecewise `C¹` on `[0, 4]`. -/
theorem isPiecewiseC1On_rectBoundary (z w : ℂ) :
    TauCeti.IsPiecewiseC1On (rectBoundary z w) 0 4 := by
  simpa [rectBoundary_def] using
    (rectPolygon z w).isPolygonalOnInterval_boundaryParam.isPiecewiseC1On

/-- A horizontal segment is a real interval times a point. -/
theorem segment_eq_reProdIm_of_im_eq {u v : ℂ} (h : u.im = v.im) :
    segment ℝ u v = [[u.re, v.re]] ×ℂ {u.im} := by
  ext p
  simp only [segment_eq_image_lineMap, mem_image, mem_reProdIm, mem_singleton_iff,
    ← segment_eq_uIcc]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, ht, ?_⟩, ?_⟩ <;> simp [AffineMap.lineMap_apply_module', h]
  · rintro ⟨⟨t, ht, hre⟩, him⟩
    refine ⟨t, ht, Complex.ext ?_ ?_⟩
    · simpa [AffineMap.lineMap_apply_module'] using hre
    · simp [AffineMap.lineMap_apply_module', him, h]

/-- A vertical segment is a point times a real interval. -/
theorem segment_eq_reProdIm_of_re_eq {u v : ℂ} (h : u.re = v.re) :
    segment ℝ u v = {u.re} ×ℂ [[u.im, v.im]] := by
  ext p
  simp only [segment_eq_image_lineMap, mem_image, mem_reProdIm, mem_singleton_iff,
    ← segment_eq_uIcc]
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨?_, ⟨t, ht, ?_⟩⟩ <;> simp [AffineMap.lineMap_apply_module', h]
  · rintro ⟨hre, ⟨t, ht, him⟩⟩
    refine ⟨t, ht, Complex.ext ?_ ?_⟩
    · simp [AffineMap.lineMap_apply_module', hre, h]
    · simpa [AffineMap.lineMap_apply_module'] using him

/-- The frontier of the rectangle with opposite corners `z` and `w` is the union of its four edges:
the bottom and top edges `[[z.re, w.re]] ×ℂ {z.im, w.im}` and the left and right edges
`{z.re, w.re} ×ℂ [[z.im, w.im]]`. In the degenerate cases this is the whole rectangle. -/
theorem frontier_rectangle (z w : ℂ) :
    frontier (Rectangle z w) = [[z.re, w.re]] ×ℂ {z.im, w.im} ∪ {z.re, w.re} ×ℂ [[z.im, w.im]] := by
  have hfr (a b : ℝ) : frontier [[a, b]] = {a, b} := by
    rcases le_total a b with h | h
    · rw [uIcc_of_le h, frontier_Icc h]
    · rw [uIcc_of_ge h, frontier_Icc h, pair_comm]
  rw [Rectangle, frontier_reProdIm, closure_uIcc, closure_uIcc, hfr, hfr]

/-- When `z` is the lower left corner, the interior of the rectangle with opposite corners `z` and
`w` is the open rectangle `Ioo z.re w.re ×ℂ Ioo z.im w.im`. -/
theorem interior_rectangle (hre : z.re ≤ w.re) (him : z.im ≤ w.im) :
    interior (Rectangle z w) = Ioo z.re w.re ×ℂ Ioo z.im w.im := by
  rw [Rectangle, interior_reProdIm, uIcc_of_le hre, uIcc_of_le him, interior_Icc, interior_Icc]

/-- The trace of the rectangle boundary over `[0, 4]` is the frontier of the rectangle. -/
theorem image_rectBoundary (z w : ℂ) :
    rectBoundary z w '' Icc 0 4 = frontier (Rectangle z w) := by
  have h := (rectPolygon z w).image_boundaryParam
  rw [Nat.cast_ofNat, uIcc_of_le (by norm_num)] at h
  rw [rectBoundary_def, h, frontier_rectangle]
  have e0 := segment_eq_reProdIm_of_im_eq (u := z) (v := w.re + z.im * I) (by simp)
  have e1 := segment_eq_reProdIm_of_re_eq (u := w.re + z.im * I) (v := w) (by simp)
  have e2 := segment_eq_reProdIm_of_im_eq (u := w) (v := z.re + w.im * I) (by simp)
  have e3 := segment_eq_reProdIm_of_re_eq (u := z.re + w.im * I) (v := z) (by simp)
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add] at e0 e1 e2 e3
  ext p
  simp only [Polygon.boundary, Polygon.edgeSet, affineSegment_eq_segment, mem_iUnion,
    Fin.exists_fin_succ, Fin.exists_fin_zero, rectPolygon_apply, finRotate_apply]
  simp [e0, e1, e2, e3, mem_reProdIm, uIcc_comm w.re z.re, uIcc_comm w.im z.im]
  tauto

/-- The boundary of the rectangle polygon is the frontier of the rectangle. -/
theorem boundary_rectPolygon (z w : ℂ) :
    (rectPolygon z w).boundary ℝ = frontier (Rectangle z w) := by
  rw [← (rectPolygon z w).image_boundaryParam, Nat.cast_ofNat, uIcc_of_le (by norm_num),
    ← rectBoundary_def, image_rectBoundary]

/-- The rectangle boundary over `[0, 4]` lies on the frontier of the rectangle. -/
theorem rectBoundary_mem_frontier {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 4) :
    rectBoundary z w t ∈ frontier (Rectangle z w) :=
  image_rectBoundary z w ▸ mem_image_of_mem _ ht

/-- The closed rectangle is closed. -/
theorem isClosed_rectangle (z w : ℂ) : IsClosed (Rectangle z w) :=
  isClosed_uIcc.reProdIm isClosed_uIcc

/-- The closed rectangle is convex. -/
theorem convex_rectangle (z w : ℂ) : Convex ℝ (Rectangle z w) := by
  rw [rectangle_eq_convexHull]
  exact convex_convexHull ℝ _

/-- The rectangle boundary over `[0, 4]` stays in the closed rectangle. -/
theorem rectBoundary_mem_rectangle {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 4) :
    rectBoundary z w t ∈ Rectangle z w :=
  (isClosed_rectangle z w).frontier_subset (rectBoundary_mem_frontier ht)

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The contour integral of `f` along a horizontal segment from `u` to `v`, parametrized over
`[0, 1]`, is the integral of `f` over the real parts. -/
private theorem smul_integral_lineMap_of_im_eq (f : ℂ → E) {u v : ℂ} (h : u.im = v.im) :
    (v - u) • ∫ t in (0 : ℝ)..1, f (AffineMap.lineMap u v t) =
      ∫ x : ℝ in u.re..v.re, f (x + u.im * I) := by
  have hv : v - u = ((v.re - u.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [h]
  have hcov := intervalIntegral.smul_integral_comp_add_mul (a := 0) (b := 1)
    (fun x : ℝ ↦ f (x + u.im * I)) (v.re - u.re) u.re
  rw [mul_zero, add_zero, mul_one, add_sub_cancel] at hcov
  rw [hv, coe_smul, ← hcov]
  refine congrArg _ (intervalIntegral.integral_congr fun t _ ↦ congrArg f ?_)
  rw [AffineMap.lineMap_apply_module']
  apply Complex.ext <;> simp [h]
  ring

/-- The contour integral of `f` along a vertical segment from `u` to `v`, parametrized over
`[0, 1]`, is `I` times the integral of `f` over the imaginary parts. -/
private theorem smul_integral_lineMap_of_re_eq (f : ℂ → E) {u v : ℂ} (h : u.re = v.re) :
    (v - u) • ∫ t in (0 : ℝ)..1, f (AffineMap.lineMap u v t) =
      I • ∫ y : ℝ in u.im..v.im, f (u.re + y * I) := by
  have hv : v - u = I * ((v.im - u.im : ℝ) : ℂ) := by apply Complex.ext <;> simp [h]
  have hcov := intervalIntegral.smul_integral_comp_add_mul (a := 0) (b := 1)
    (fun y : ℝ ↦ f (u.re + y * I)) (v.im - u.im) u.im
  rw [mul_zero, add_zero, mul_one, add_sub_cancel] at hcov
  rw [hv, mul_smul, coe_smul, ← hcov]
  refine congrArg _ (congrArg _ (intervalIntegral.integral_congr fun t _ ↦ congrArg f ?_))
  rw [AffineMap.lineMap_apply_module']
  apply Complex.ext <;> simp [h]
  ring

/-- **The contour integral along the rectangle boundary** of a function continuous on the frontier
of the rectangle is the signed sum of its four edge integrals: the bottom and right edges with a
plus sign, the top and left edges with a minus sign. This is the expression that Mathlib's Cauchy
theorem for rectangles, `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`, shows to
vanish for a function holomorphic on the rectangle. -/
theorem integral_rectBoundary {f : ℂ → E} (hf : ContinuousOn f (frontier (Rectangle z w))) :
    ∫ t in (0 : ℝ)..4, deriv (rectBoundary z w) t • f (rectBoundary z w t) =
      (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
        I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
        I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I)) := by
  have hpoly := (rectPolygon z w).integral_contourCycle (boundary_rectPolygon z w ▸ hf)
  rw [Polygon.contourCycle_def, Polygon.contourCurve_def, TauCeti.Contour.Cycle.integral_of_raw,
    Nat.cast_ofNat, ← rectBoundary_def] at hpoly
  -- The four edges are alternately horizontal and vertical segments.
  rw [hpoly, Fin.sum_univ_four]
  simp only [Polygon.edgePath]
  rw [smul_integral_lineMap_of_im_eq f, smul_integral_lineMap_of_re_eq f,
    smul_integral_lineMap_of_im_eq f, smul_integral_lineMap_of_re_eq f]
  · simp only [rectPolygon_apply, finRotate_apply]
    simp [intervalIntegral.integral_symm z.re w.re, intervalIntegral.integral_symm z.im w.im]
    abel
  all_goals simp [finRotate_apply]

end Integral

end Complex
