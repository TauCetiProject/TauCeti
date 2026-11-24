/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Rectangle
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
* `Complex.image_rectBoundary`: the trace of the curve is `frontier (Rectangle z w)`.
* `Complex.integral_rectBoundary`: its contour integral is the signed sum of the four edge
  integrals.
* `Complex.integral_contourCycle_rectPolygon`: the same signed sum for
  `TauCeti.Contour.Cycle.integral` over `(Complex.rectPolygon z w).contourCycle`.
* `Complex.integral_rectBoundary_congr_codiscreteWithin`: codiscrete changes on the frontier
  do not affect the derivative-weighted integral, including for collapsed edges.
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

/-- Two rectangles with the same real-part bounds have `rectBoundary` curves with identical real
parts at every time `t`. -/
theorem re_rectBoundary_eq_of_re_eq {z₁ w₁ z₂ w₂ : ℂ} (hz : z₁.re = z₂.re) (hw : w₁.re = w₂.re)
    (t : ℝ) : (rectBoundary z₁ w₁ t).re = (rectBoundary z₂ w₂ t).re := by
  simp only [rectBoundary_def, Polygon.boundaryParam_eq_edgePath_edgeIndexAt,
    Polygon.edgePath, AffineMap.lineMap_apply_module]
  generalize Polygon.edgeIndexAt 4 t = i
  fin_cases i <;> simp [finRotate_apply, hz, hw]

/-- Two rectangles with the same imaginary-part bounds have `rectBoundary` curves with identical
imaginary parts at every time `t`. -/
theorem im_rectBoundary_eq_of_im_eq {z₁ w₁ z₂ w₂ : ℂ} (hz : z₁.im = z₂.im) (hw : w₁.im = w₂.im)
    (t : ℝ) : (rectBoundary z₁ w₁ t).im = (rectBoundary z₂ w₂ t).im := by
  simp only [rectBoundary_def, Polygon.boundaryParam_eq_edgePath_edgeIndexAt,
    Polygon.edgePath, AffineMap.lineMap_apply_module]
  generalize Polygon.edgeIndexAt 4 t = i
  fin_cases i <;> simp [finRotate_apply, hz, hw]

private theorem rectBoundary_eq_linear_comb (z w : ℂ) (t : ℝ) :
    rectBoundary z w t =
      z.re • rectBoundary 1 0 t + z.im • rectBoundary I 0 t +
        w.re • rectBoundary 0 1 t + w.im • rectBoundary 0 I t := by
  simp only [rectBoundary_def, Polygon.boundaryParam_eq_edgePath_edgeIndexAt,
    Polygon.edgePath, AffineMap.lineMap_apply_module]
  generalize Polygon.edgeIndexAt 4 t = i
  fin_cases i <;> (apply Complex.ext <;> simp [finRotate_apply] <;> ring)

/-- The rectangle boundary `rectBoundary z w` is continuous on `ℝ`. -/
theorem continuous_rectBoundary (z w : ℂ) : Continuous (rectBoundary z w) :=
  (rectPolygon z w).continuous_boundaryParam

/-- The rectangle boundary `rectBoundary z w t` is jointly continuous in `(z, w)` and `t : ℝ`. -/
theorem continuous_uncurry_rectBoundary :
    Continuous (fun p : (ℂ × ℂ) × ℝ ↦ rectBoundary p.1.1 p.1.2 p.2) := by
  have hbase (a b : ℂ) : Continuous (rectBoundary a b) := continuous_rectBoundary a b
  have heq : (fun p : (ℂ × ℂ) × ℝ ↦ rectBoundary p.1.1 p.1.2 p.2) =
      fun p : (ℂ × ℂ) × ℝ ↦
        p.1.1.re • rectBoundary 1 0 p.2 + p.1.1.im • rectBoundary I 0 p.2 +
          p.1.2.re • rectBoundary 0 1 p.2 + p.1.2.im • rectBoundary 0 I p.2 :=
    funext fun p ↦ rectBoundary_eq_linear_comb p.1.1 p.1.2 p.2
  rw [heq]
  fun_prop

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

/-- The rectangle boundary lies on the frontier of the rectangle: it is periodic, so each value is
one over `[0, 4)`. -/
theorem rectBoundary_mem_frontier (t : ℝ) : rectBoundary z w t ∈ frontier (Rectangle z w) := by
  obtain ⟨s, hs, hts⟩ := (periodic_rectBoundary z w).exists_mem_Ico₀ (by norm_num) t
  rw [hts]
  exact image_rectBoundary z w ▸ mem_image_of_mem _ (Ico_subset_Icc_self hs)

/-- The rectangle boundary stays in the closed rectangle. -/
theorem rectBoundary_mem_rectangle (t : ℝ) : rectBoundary z w t ∈ Rectangle z w :=
  (isClosed_rectangle z w).frontier_subset (rectBoundary_mem_frontier t)

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

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
  rw [(rectPolygon z w).integral_contourCycle_eq_integral_boundaryParam, Nat.cast_ofNat,
    ← rectBoundary_def] at hpoly
  -- The four edges are alternately horizontal and vertical segments.
  rw [hpoly, Fin.sum_univ_four]
  simp only [Polygon.edgePath]
  rw [smul_integral_lineMap_of_im_eq f, smul_integral_lineMap_of_re_eq f,
    smul_integral_lineMap_of_im_eq f, smul_integral_lineMap_of_re_eq f]
  · simp only [rectPolygon_apply, finRotate_apply]
    simp [intervalIntegral.integral_symm z.re w.re, intervalIntegral.integral_symm z.im w.im]
    abel
  all_goals simp [finRotate_apply]

/-- **The cycle integral along the rectangle polygon** of a function continuous on the frontier of
the rectangle is the signed sum of its four edge integrals, matching
`Complex.integral_rectBoundary`. -/
theorem integral_contourCycle_rectPolygon {f : ℂ → E}
    (hf : ContinuousOn f (frontier (Rectangle z w))) :
    TauCeti.Contour.Cycle.integral f (rectPolygon z w).contourCycle =
      (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
        I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
        I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I)) := by
  rw [(rectPolygon z w).integral_contourCycle_eq_integral_boundaryParam, Nat.cast_ofNat,
    ← rectBoundary_def, integral_rectBoundary hf]

end Integral

section Congruence

variable {E : Type*} [Zero E] [SMulWithZero ℂ E]

open Filter Topology

private theorem ae_rectBoundary_integrand_eq_on_cell {f g : ℂ → E}
    (hfg : f =ᶠ[codiscreteWithin (frontier (Rectangle z w))] g) (i : Fin 4) :
    ∀ᵐ t : ℝ, t ∈ Ioo ((i : ℕ) : ℝ) ((i : ℕ) + 1) →
      deriv (rectBoundary z w) t • f (rectBoundary z w t) =
        deriv (rectBoundary z w) t • g (rectBoundary z w t) := by
  let a := rectPolygon z w i
  let v := rectPolygon z w (finRotate 4 i) - a
  let p : ℝ → ℂ := fun t ↦ (t - (i : ℕ)) • v + a
  have heq (t : ℝ) (ht : t ∈ Icc ((i : ℕ) : ℝ) ((i : ℕ) + 1)) :
      rectBoundary z w t = p t := by
    rw [rectBoundary_eq_lineMap i ht, AffineMap.lineMap_apply_module']
  have hd (t : ℝ) : HasDerivAt p v t := by
    simpa [p] using (((hasDerivAt_id t).sub_const ((i : ℕ) : ℝ)).smul_const v).add_const a
  have hcurve (t : ℝ) (ht : t ∈ Ioo ((i : ℕ) : ℝ) ((i : ℕ) + 1)) :
      HasDerivAt (rectBoundary z w) v t := by
    refine (hd t).congr_of_eventuallyEq ?_
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with u hu
    exact heq u hu
  by_cases hv : v = 0
  · filter_upwards [] with t ht
    rw [(hcurve t ht).deriv, hv]
    simp
  · have hinj : Function.Injective p := by
      intro t u htu
      have hsmul : (t - (i : ℕ)) • v = (u - (i : ℕ)) • v := add_right_cancel htu
      have hsub : t - (i : ℕ) = u - (i : ℕ) := (smul_left_injective ℝ hv) hsmul
      exact sub_left_injective hsub
    have hcompact : IsCompact (frontier (Rectangle z w)) :=
      (isCompact_uIcc.reProdIm isCompact_uIcc).of_isClosed_subset isClosed_frontier
        (isClosed_rectangle z w).frontier_subset
    have hbad := hcompact.finite_sdiff_of_mem_codiscreteWithin hfg
    have hpre := Set.Finite.preimage hinj.injOn hbad
    filter_upwards [hpre.countable.ae_notMem volume] with t ht hcell
    have hpt : p t ∈ frontier (Rectangle z w) := by
      rw [← heq t (Ioo_subset_Icc_self hcell)]
      exact rectBoundary_mem_frontier t
    have hfg' : f (p t) = g (p t) := by
      by_contra h
      exact ht ⟨hpt, h⟩
    rw [heq t (Ioo_subset_Icc_self hcell), hfg']

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [SMulWithZero ℂ F]

/-- The derivative-weighted rectangle integral ignores changes on a subset codiscrete
within its frontier. No integrability or completeness assumption is needed; a collapsed
edge has zero velocity and hence contributes zero. -/
theorem integral_rectBoundary_congr_codiscreteWithin {f g : ℂ → F}
    (hfg : f =ᶠ[codiscreteWithin (frontier (Rectangle z w))] g) :
    (∫ t in (0 : ℝ)..4, deriv (rectBoundary z w) t • f (rectBoundary z w t)) =
      ∫ t in (0 : ℝ)..4, deriv (rectBoundary z w) t • g (rectBoundary z w t) := by
  have hcell := ae_all_iff.2 (fun i : Fin 4 ↦ ae_rectBoundary_integrand_eq_on_cell hfg i)
  have hfinite : ({(1 : ℝ), 2, 3, 4} : Set ℝ).Finite := by simp
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hcell, hfinite.countable.ae_notMem volume] with t hc hn ht
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hn
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 4)] at ht
  have ht4 : t < 4 := lt_of_le_of_ne ht.2 hn.2.2.2
  by_cases h1 : t < 1
  · exact hc 0 (by simpa using And.intro ht.1 h1)
  · have h1' : 1 < t := lt_of_le_of_ne (le_of_not_gt h1) (Ne.symm hn.1)
    by_cases h2 : t < 2
    · exact hc 1 (by norm_num; exact And.intro h1' h2)
    · have h2' : 2 < t := lt_of_le_of_ne (le_of_not_gt h2) (Ne.symm hn.2.1)
      by_cases h3 : t < 3
      · exact hc 2 (by norm_num; exact And.intro h2' h3)
      · have h3' : 3 < t := lt_of_le_of_ne (le_of_not_gt h3) (Ne.symm hn.2.2.1)
        exact hc 3 (by norm_num; exact And.intro h3' ht4)

end Congruence

end Complex
