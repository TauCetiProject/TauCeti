/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Affine.Triangle
public import TauCeti.MeasureTheory.Integral.CurveIntegral.Line
public import Mathlib.Basic.Real.Sign

/-!
# Green's theorem for degenerate triangles

Collinear triangle edges are interval integrals of one common line coefficient. Their
circulations telescope for every continuous field. The degenerate convex hull has zero area,
so this completes the oriented triangle formula, including repeated vertices and edges.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

/-- Every continuous field has zero circulation around a degenerate ordered triangle.
This includes arbitrary backtracking and repeated vertices. -/
theorem curveIntegral_triangle_eq_zero_of_det_eq_zero {c p q : ℂ}
    (hdet : triangleDet c p q = 0) {P Q : ℂ → ℝ} (hP : ContinuousOn P (convexHull ℝ {c, p, q}))
    (hQ : ContinuousOn Q (convexHull ℝ {c, p, q})) :
    curveIntegral (oneForm P Q) (Path.segment c p) +
      curveIntegral (oneForm P Q) (Path.segment p q) -
      curveIntegral (oneForm P Q) (Path.segment c q) = 0 := by
  by_cases hpc : p - c = 0
  · have hp : p = c := sub_eq_zero.mp hpc
    subst p
    simp
  let r : ℝ := ((q - c) / (p - c)).re
  have hreal : (r : ℂ) = (q - c) / (p - c) := by
    apply Complex.ext
    · rfl
    · simp only [Complex.ofReal_im, im_div_sub_eq_triangleDet, hdet, zero_div]
  have hq : q = c + r • (p - c) := by
    rw [Complex.real_smul, hreal, div_mul_cancel₀ _ hpc]
    abel
  have hc : c = c + (0 : ℝ) • (p - c) := by simp
  have hp : p = c + (1 : ℝ) • (p - c) := by simp
  have h₁ := curveIntegral_segment_line (oneForm P Q) c (p - c) 0 1
  have h₂ := curveIntegral_segment_line (oneForm P Q) c (p - c) 1 r
  have h₃ := curveIntegral_segment_line (oneForm P Q) c (p - c) 0 r
  rw [← hc, ← hp] at h₁
  rw [← hp, ← hq] at h₂
  rw [← hc, ← hq] at h₃
  rw [h₁, h₂, h₃]
  let T : Set ℝ := AffineMap.lineMap c p ⁻¹' convexHull ℝ {c, p, q}
  have hT : Convex ℝ T := (convex_convexHull ℝ _).affine_preimage (AffineMap.lineMap c p)
  have hzero : (0 : ℝ) ∈ T := by simp [T, subset_convexHull ℝ _ (by simp : c ∈ {c, p, q})]
  have hone : (1 : ℝ) ∈ T := by simp [T, subset_convexHull ℝ _ (by simp : p ∈ {c, p, q})]
  have hr : r ∈ T := by
    simp only [T, Set.mem_preimage]
    rw [AffineMap.lineMap_apply_module', add_comm, ← hq]
    exact subset_convexHull ℝ _ (by simp)
  have hline : Continuous (AffineMap.lineMap c p : ℝ → ℂ) := by fun_prop
  have hcont : ContinuousOn (fun t : ℝ ↦ oneForm P Q (c + t • (p - c)) (p - c)) T := by
    have hp := hP.comp hline.continuousOn (mapsTo_preimage _ _)
    have hq' := hQ.comp hline.continuousOn (mapsTo_preimage _ _)
    simpa only [oneForm_apply, Function.comp_apply, AffineMap.lineMap_apply_module',
      add_comm, Pi.add_def, Pi.mul_def] using
      (hp.mul (continuousOn_const (c := (p - c).re))).add
        (hq'.mul (continuousOn_const (c := (p - c).im)))
  rw [intervalIntegral.integral_add_adjacent_intervals
    (hcont.mono (hT.ordConnected.uIcc_subset hzero hone)).intervalIntegrable
    (hcont.mono (hT.ordConnected.uIcc_subset hone hr)).intervalIntegrable, sub_self]

/-- Degenerate triangle Green for continuous fields: both the actual circulation and every
area integral vanish. Area integrability follows from the null convex hull. -/
theorem green_triangle_of_det_eq_zero {c p q : ℂ} (hdet : triangleDet c p q = 0)
    {P Q : ℂ → ℝ} (hP : ContinuousOn P (convexHull ℝ {c, p, q}))
    (hQ : ContinuousOn Q (convexHull ℝ {c, p, q})) :
    IntegrableOn (curl P Q) (convexHull ℝ {c, p, q}) ∧
      curveIntegral (oneForm P Q) (Path.segment c p) +
        curveIntegral (oneForm P Q) (Path.segment p q) -
        curveIntegral (oneForm P Q) (Path.segment c q) = 0 ∧
      (∫ z in convexHull ℝ {c, p, q}, curl P Q z) = 0 := by
  have harea := volume_convexHull_triangle_eq_zero hdet
  refine ⟨?_, curveIntegral_triangle_eq_zero_of_det_eq_zero hdet hP hQ,
    setIntegral_measure_zero _ harea⟩
  simp [IntegrableOn, Measure.restrict_eq_zero.mpr harea]

/-- Green's theorem for every ordered triangle and fields that are `C¹` on an open neighborhood,
including collinear and repeated vertices. The determinant sign agrees with the triangle's winding
orientation. -/
theorem green_triangle (c p q : ℂ) {U : Set ℂ} (hU : IsOpen U)
    (hTU : convexHull ℝ {c, p, q} ⊆ U) {P Q : ℂ → ℝ}
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    IntegrableOn (curl P Q) (convexHull ℝ {c, p, q}) ∧
      curveIntegral (oneForm P Q) (Path.segment c p) +
        curveIntegral (oneForm P Q) (Path.segment p q) -
        curveIntegral (oneForm P Q) (Path.segment c q) =
          Real.sign (triangleDet c p q) * ∫ z in convexHull ℝ {c, p, q}, curl P Q z := by
  by_cases hdet : triangleDet c p q = 0
  · have h := green_triangle_of_det_eq_zero hdet (hP.continuousOn.mono hTU)
      (hQ.continuousOn.mono hTU)
    exact ⟨h.1, by simpa only [hdet, Real.sign_zero, zero_mul] using h.2.1⟩
  · have h := green_triangle_of_det_ne_zero hdet hU hTU hP hQ
    have hsign : triangleDet c p q / |triangleDet c p q| = Real.sign (triangleDet c p q) := by
      rcases lt_or_gt_of_ne hdet with hn | hp
      · rw [abs_of_neg hn, div_neg, div_self hdet, Real.sign_of_neg hn]
      · rw [abs_of_pos hp, div_self hdet, Real.sign_of_pos hp]
    simpa only [hsign] using h

end TauCeti.Green
