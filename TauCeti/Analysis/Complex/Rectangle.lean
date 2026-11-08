/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Convex
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Axis-parallel segments and rectangles in the complex plane

This file collects elementary facts about Mathlib's closed rectangle `Complex.Rectangle z w`
(`[[z.re, w.re]] ×ℂ [[z.im, w.im]]`) and about horizontal and vertical segments, the edges of such
rectangles.

## Main results

* `Complex.segment_eq_reProdIm_of_im_eq`, `Complex.segment_eq_reProdIm_of_re_eq`: horizontal and
  vertical segments as `×ℂ` products.
* `Complex.frontier_rectangle`, `Complex.interior_rectangle`: the frontier of a rectangle is the
  union of its four edges, and its interior is the open rectangle.
* `Complex.mem_Ioo_reProdIm_of_mem_rectangle`: a point of the rectangle off its frontier lies in
  the open rectangle.
* `Complex.isClosed_rectangle`, `Complex.convex_rectangle`.
* `Complex.smul_integral_lineMap_of_im_eq`, `Complex.smul_integral_lineMap_of_re_eq`: the contour
  integral along a horizontal or vertical segment, parametrized over `[0, 1]`, as a real interval
  integral over the real or imaginary parts.
-/

public section

open Set MeasureTheory
open scoped Interval

namespace Complex

variable {z w : ℂ}

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

/-- A point of the closed rectangle that is not on its frontier lies in the open rectangle. -/
theorem mem_Ioo_reProdIm_of_mem_rectangle (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    {s : ℂ} (hs : s ∈ Rectangle z w) (hfr : s ∉ frontier (Rectangle z w)) :
    s ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im := by
  rw [← interior_rectangle hre him, ← self_sdiff_frontier]
  exact ⟨hs, hfr⟩

/-- The closed rectangle is closed. -/
theorem isClosed_rectangle (z w : ℂ) : IsClosed (Rectangle z w) :=
  isClosed_uIcc.reProdIm isClosed_uIcc

/-- The closed rectangle is convex. -/
theorem convex_rectangle (z w : ℂ) : Convex ℝ (Rectangle z w) := by
  rw [rectangle_eq_convexHull]
  exact convex_convexHull ℝ _

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The contour integral of `f` along a horizontal segment from `u` to `v`, parametrized over
`[0, 1]`, is the integral of `f` over the real parts. -/
theorem smul_integral_lineMap_of_im_eq (f : ℂ → E) {u v : ℂ} (h : u.im = v.im) :
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
theorem smul_integral_lineMap_of_re_eq (f : ℂ → E) {u v : ℂ} (h : u.re = v.re) :
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

end Integral

end Complex
