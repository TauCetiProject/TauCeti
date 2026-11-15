/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Examples.CurveArea.Basic
public import TauCeti.Analysis.Green.Polygonal.Green
import Mathlib.Basic.Complex.BigOperators

/-!
# Signed shoelace area

The signed-area form integrates on a segment to half the coordinate determinant.
Consequently every closed polygon has the shoelace area counted with winding index,
including polygons with repeated vertices and self-intersections.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green.Examples

/-- The actual signed-area circulation of one segment is half its endpoint determinant. -/
theorem curveIntegral_area_segment (p q : ℂ) :
    curveIntegral (oneForm areaP areaQ) (Path.segment p q) =
      (p.re * q.im - q.re * p.im) / 2 := by
  rw [curveIntegral_segment]
  have heq (t : ℝ) : oneForm areaP areaQ (AffineMap.lineMap p q t) (q - p) =
      (p.re * q.im - q.re * p.im) / 2 := by
    rw [oneForm_apply, areaP_apply, areaQ_apply, AffineMap.lineMap_apply_module']
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul]
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_const]
  simp

/-- The signed-area circulation of a finite polygonal chain is the shoelace sum. -/
theorem curveIntegral_area_polygon {N : ℕ} (v : Fin (N + 1) → ℂ) :
    Finsupp.linearCombination ℤ (fun η : Arc ↦ curveIntegral (oneForm areaP areaQ) η.2.2)
      (BoundaryChain.polygon v) =
      (∑ i : Fin N, ((v i.castSucc).re * (v i.succ).im -
        (v i.succ).re * (v i.castSucc).im)) / 2 := by
  simp only [BoundaryChain.polygon_def, map_sum, BoundaryChain.ofPath_def,
    Finsupp.linearCombination_single, one_smul, curveIntegral_area_segment]
  rw [Finset.sum_div]

/-- The raw circulation shoelace formula on any increasing affine subdivision. -/
theorem integral_circulationFun_area_shoelace {γ : ℝ → ℂ} {a b : ℝ} {N : ℕ}
    {s : Fin (N + 1) → ℝ} (hs : StrictMono s) (ha : s 0 = a) (hb : s (Fin.last N) = b)
    (hsegments : ∀ i : Fin N, ∀ t ∈ Icc (s i.castSucc) (s i.succ),
      γ t = γ (s i.castSucc) + ((t - s i.castSucc) / (s i.succ - s i.castSucc)) •
        (γ (s i.succ) - γ (s i.castSucc))) :
    (∫ t in a..b, circulationFun areaP areaQ γ t) =
      (∑ i : Fin N, ((γ (s i.castSucc)).re * (γ (s i.succ)).im -
        (γ (s i.succ)).re * (γ (s i.castSucc)).im)) / 2 := by
  rw [integral_circulationFun_eq_polygon hs ha hb hsegments
    (contDiff_areaP (n := 1)).continuous.continuousOn
    (contDiff_areaQ (n := 1)).continuous.continuousOn, curveIntegral_area_polygon]
  rfl

/-- The whole-plane winding-weighted area of a closed polygon is its signed shoelace sum.
No simplicity assumption is used. -/
theorem integral_windingWeight_shoelace {γ : ℝ → ℂ} {a b : ℝ} {N : ℕ}
    {s : Fin (N + 1) → ℝ} (hs : StrictMono s) (ha : s 0 = a) (hb : s (Fin.last N) = b)
    (hsegments : ∀ i : Fin N, ∀ t ∈ Icc (s i.castSucc) (s i.succ),
      γ t = γ (s i.castSucc) + ((t - s i.castSucc) / (s i.succ - s i.castSucc)) •
        (γ (s i.succ) - γ (s i.castSucc)))
    (hclosed : γ a = γ b) :
    Integrable (windingWeight γ a b) ∧
      (∫ z : ℂ, windingWeight γ a b z) =
      (∑ i : Fin N, ((γ (s i.castSucc)).re * (γ (s i.succ)).im -
        (γ (s i.succ)).re * (γ (s i.castSucc)).im)) / 2 := by
  have h := (green_polygon_of_subdivision hs ha hb hsegments hclosed
    (contDiff_areaP (n := 1)) (contDiff_areaQ (n := 1))).2
  simp only [curl_area, mul_one] at h
  refine ⟨h.1, ?_⟩
  rw [← h.2]
  exact integral_circulationFun_area_shoelace hs ha hb hsegments

end TauCeti.Green.Examples
