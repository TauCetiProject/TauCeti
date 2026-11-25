/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Convex
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.InnerProductSpace.Convex

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
* `Complex.interior_rectangle_nonempty`: a rectangle with sides of positive length has nonempty
  interior.
* `Complex.mem_rectangle_iff`: membership in a rectangle given by its lower left and upper right
  corners.
* `Complex.mem_Ioo_reProdIm_of_mem_rectangle`: a point of the rectangle off its frontier lies in
  the open rectangle.
* `Complex.notMem_frontier_rectangle_of_mem_Ioo`: conversely, a point of the open rectangle is
  not on its frontier.
* `Complex.isClosed_rectangle`, `Complex.isCompact_rectangle`, `Complex.convex_rectangle`.
* `Complex.frontier_rectangle_subset_sdiff`: the frontier of a rectangle avoids every set contained
  in the open rectangle.
* `Complex.rectangle_ne_closedBall`: a rectangle with distinct opposite corners is not a closed
  disc.
* `Complex.dist_le_of_mem_rectangle`: two points of `Rectangle z w` are at distance at most
  `dist z w`.
* `Complex.smul_integral_lineMap_of_im_eq`, `Complex.smul_integral_lineMap_of_re_eq`: the contour
  integral along a horizontal or vertical segment, parametrized over `[0, 1]`, as a real interval
  integral over the real or imaginary parts.
-/

public section

open Set MeasureTheory Metric
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

/-- A rectangle whose opposite corners differ in both coordinates has nonempty interior. -/
theorem interior_rectangle_nonempty (hre : z.re ≠ w.re) (him : z.im ≠ w.im) :
    (interior (Rectangle z w)).Nonempty := by
  rw [Rectangle, interior_reProdIm, reProdIm_nonempty, uIcc, uIcc, interior_Icc, interior_Icc,
    nonempty_Ioo, nonempty_Ioo]
  exact ⟨inf_lt_sup.2 hre, inf_lt_sup.2 him⟩

/-- When `z` is the lower left corner, membership in the rectangle with opposite corners `z` and
`w` is a pair of bounds on the real and imaginary parts. -/
theorem mem_rectangle_iff (hre : z.re ≤ w.re) (him : z.im ≤ w.im) {s : ℂ} :
    s ∈ Rectangle z w ↔ (z.re ≤ s.re ∧ s.re ≤ w.re) ∧ (z.im ≤ s.im ∧ s.im ≤ w.im) := by
  rw [Rectangle, mem_reProdIm, uIcc_of_le hre, uIcc_of_le him, mem_Icc, mem_Icc]

/-- A point of the closed rectangle that is not on its frontier lies in the open rectangle. -/
theorem mem_Ioo_reProdIm_of_mem_rectangle (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    {s : ℂ} (hs : s ∈ Rectangle z w) (hfr : s ∉ frontier (Rectangle z w)) :
    s ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im := by
  rw [← interior_rectangle hre him, ← self_sdiff_frontier]
  exact ⟨hs, hfr⟩

/-- A point of the open rectangle `Ioo z.re w.re ×ℂ Ioo z.im w.im` is not on the frontier of
`Rectangle z w`. -/
theorem notMem_frontier_rectangle_of_mem_Ioo {s : ℂ}
    (hs : s ∈ Ioo z.re w.re ×ℂ Ioo z.im w.im) : s ∉ frontier (Rectangle z w) := by
  rw [← interior_rectangle (hs.1.1.trans hs.1.2).le (hs.2.1.trans hs.2.2).le] at hs
  exact disjoint_left.1 disjoint_interior_frontier hs

/-- The closed rectangle is closed. -/
theorem isClosed_rectangle (z w : ℂ) : IsClosed (Rectangle z w) :=
  isClosed_uIcc.reProdIm isClosed_uIcc

/-- The frontier of `Rectangle z w` lies in the rectangle and avoids every set `P` contained in the
open rectangle `Ioo z.re w.re ×ℂ Ioo z.im w.im`. -/
theorem frontier_rectangle_subset_sdiff {P : Set ℂ} (hP : P ⊆ Ioo z.re w.re ×ℂ Ioo z.im w.im) :
    frontier (Rectangle z w) ⊆ Rectangle z w \ P :=
  fun _ hs ↦ ⟨(isClosed_rectangle z w).frontier_subset hs,
    fun hsP ↦ notMem_frontier_rectangle_of_mem_Ioo (hP hsP) hs⟩

/-- The closed rectangle is compact. -/
theorem isCompact_rectangle (z w : ℂ) : IsCompact (Rectangle z w) :=
  isCompact_uIcc.reProdIm isCompact_uIcc

/-- The closed rectangle is convex. -/
theorem convex_rectangle (z w : ℂ) : Convex ℝ (Rectangle z w) := by
  rw [rectangle_eq_convexHull]
  exact convex_convexHull ℝ _

/-- A closed rectangle with distinct opposite corners is not a closed disc: the midpoint of an
edge of positive length is not an interior point of the rectangle, while every midpoint of two
distinct points of a closed disc is. -/
theorem rectangle_ne_closedBall (hzw : z ≠ w) (c : ℂ) (r : ℝ) :
    Rectangle z w ≠ closedBall c r := by
  intro h
  have hsc : StrictConvex ℝ (Rectangle z w) := h ▸ strictConvex_closedBall ℝ c r
  -- An endpoint of an interval of `ℝ` is not an interior point of it.
  have hend (x y : ℝ) : x ∉ interior [[x, y]] := by
    simp only [uIcc, interior_Icc, mem_Ioo, inf_lt_left, left_lt_sup, not_and]
    exact fun h h' ↦ h' (not_le.1 h).le
  -- The midpoint of `z` and another point of the rectangle is an interior point.
  have hmid {p : ℂ} (hp : p ∈ Rectangle z w) (hzp : z ≠ p) :
      (z.re + p.re) / 2 ∈ interior [[z.re, w.re]] ∧
        (z.im + p.im) / 2 ∈ interior [[z.im, w.im]] := by
    have hm := hsc (by simp [Rectangle, mem_reProdIm]) hp hzp one_half_pos one_half_pos
      (add_halves 1)
    rw [Rectangle, interior_reProdIm, mem_reProdIm] at hm
    have hre : ((1 / 2 : ℝ) • z + (1 / 2 : ℝ) • p).re = (z.re + p.re) / 2 := by
      simp only [add_re, smul_re, smul_eq_mul]
      ring
    have him : ((1 / 2 : ℝ) • z + (1 / 2 : ℝ) • p).im = (z.im + p.im) / 2 := by
      simp only [add_im, smul_im, smul_eq_mul]
      ring
    rwa [hre, him] at hm
  rcases eq_or_ne z.re w.re with hre | hre
  · -- The corners `z` and `z.re + w.im * I` are distinct and share the real part `z.re`.
    refine hend z.re w.re ?_
    simpa using (hmid (p := z.re + w.im * I) (by simp [Rectangle, mem_reProdIm])
      fun h ↦ hzw (Complex.ext hre (by simpa using congrArg im h))).1
  · -- The corners `z` and `w.re + z.im * I` are distinct and share the imaginary part `z.im`.
    refine hend z.im w.im ?_
    simpa using (hmid (p := w.re + z.im * I) (by simp [Rectangle, mem_reProdIm])
      fun h ↦ hre (by simpa using congrArg re h)).2

/-- The distance between any two points of a closed rectangle is at most the distance between its
opposite corners. -/
theorem dist_le_of_mem_rectangle {u v : ℂ} (hu : u ∈ Rectangle z w) (hv : v ∈ Rectangle z w) :
    dist u v ≤ dist z w := by
  rw [dist_eq_re_im, dist_eq_re_im]
  have hre := Real.dist_le_of_mem_uIcc hu.1 hv.1
  have him := Real.dist_le_of_mem_uIcc hu.2 hv.2
  rw [Real.dist_eq, Real.dist_eq] at hre him
  exact Real.sqrt_le_sqrt (add_le_add (sq_le_sq.2 hre) (sq_le_sq.2 him))

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
