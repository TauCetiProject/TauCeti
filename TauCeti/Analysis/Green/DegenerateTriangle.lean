/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.AffineTriangle
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
The proof uses actual one-dimensional integrals, including arbitrary backtracking. -/
theorem curveIntegral_triangle_eq_zero_of_det_eq_zero {c p q : ℂ}
    (hdet : triangleDet c p q = 0) {P Q : ℂ → ℝ} (hP : Continuous P) (hQ : Continuous Q) :
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
  have hcont : Continuous (fun t : ℝ ↦ oneForm P Q (c + t • (p - c)) (p - c)) := by
    simp only [oneForm_apply]
    fun_prop
  rw [intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 1)
    (hcont.intervalIntegrable 1 r), sub_self]

/-- Degenerate triangle Green for continuous fields: both the actual circulation and every
area integral vanish. Area integrability follows from the null convex hull. -/
theorem green_triangle_of_det_eq_zero {c p q : ℂ} (hdet : triangleDet c p q = 0)
    {P Q : ℂ → ℝ} (hP : Continuous P) (hQ : Continuous Q) :
    IntegrableOn (curl P Q) (convexHull ℝ {c, p, q}) ∧
      curveIntegral (oneForm P Q) (Path.segment c p) +
        curveIntegral (oneForm P Q) (Path.segment p q) -
        curveIntegral (oneForm P Q) (Path.segment c q) = 0 ∧
      (∫ z in convexHull ℝ {c, p, q}, curl P Q z) = 0 := by
  have harea := volume_convexHull_triangle_eq_zero hdet
  refine ⟨?_, curveIntegral_triangle_eq_zero_of_det_eq_zero hdet hP hQ,
    setIntegral_measure_zero _ harea⟩
  simp [IntegrableOn, Measure.restrict_eq_zero.mpr harea]

/-- Green's theorem for every ordered triangle and globally `C¹` fields, including collinear
and repeated vertices. The determinant sign agrees with the triangle's winding orientation. -/
theorem green_triangle (c p q : ℂ) {P Q : ℂ → ℝ}
    (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q) :
    IntegrableOn (curl P Q) (convexHull ℝ {c, p, q}) ∧
      curveIntegral (oneForm P Q) (Path.segment c p) +
        curveIntegral (oneForm P Q) (Path.segment p q) -
        curveIntegral (oneForm P Q) (Path.segment c q) =
          Real.sign (triangleDet c p q) * ∫ z in convexHull ℝ {c, p, q}, curl P Q z := by
  by_cases hdet : triangleDet c p q = 0
  · have h := green_triangle_of_det_eq_zero hdet hP.continuous hQ.continuous
    exact ⟨h.1, by simpa only [hdet, Real.sign_zero, zero_mul] using h.2.1⟩
  · have h := green_triangle_of_det_ne_zero hdet isOpen_univ (subset_univ _)
      hP.contDiffOn hQ.contDiffOn
    have hsign : triangleDet c p q / |triangleDet c p q| = Real.sign (triangleDet c p q) := by
      rcases lt_or_gt_of_ne hdet with hn | hp
      · rw [abs_of_neg hn, div_neg, div_self hdet, Real.sign_of_neg hn]
      · rw [abs_of_pos hp, div_self hdet, Real.sign_of_pos hp]
    simpa only [hsign] using h

end TauCeti.Green
