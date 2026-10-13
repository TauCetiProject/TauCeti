/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Main
public import TauCeti.Analysis.Green.FiniteSum
public import TauCeti.Analysis.Green.Examples.CurveArea.Ellipse
public import TauCeti.Analysis.Green.Examples.CurveArea.DoubleTraversal
public import TauCeti.Analysis.Green.Examples.CurveArea.SqrtReparam
public import TauCeti.Analysis.Green.Examples.CurveArea.Annulus

/-!
# Green's theorem on circles, ellipses, repeated traversals, and annuli

These examples invoke the full absolutely continuous Green theorem to identify the two actual,
integrable signed-area integrals. The square-root circle has unbounded speed. The annulus uses
the finite-family theorem and cancellation of the total index outside the annular field domain.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green.Examples

private theorem green_area_form {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b) :
    IntervalIntegrable (circulationFun areaP areaQ γ) volume a b ∧
      Integrable (windingWeight γ a b) ∧
      (∫ t in a..b, circulationFun areaP areaQ γ t) = ∫ z : ℂ, windingWeight γ a b z := by
  simpa only [curl_area, mul_one] using
    green_ac hab hγ hclosed (contDiff_areaP (n := 1)) (contDiff_areaQ (n := 1))

/-- Full Green's theorem gives both integrability conclusions and disc area for a circle. -/
theorem green_circle_area (R : ℝ) :
    IntervalIntegrable (circulationFun areaP areaQ (circleMap 0 R)) volume 0 (2 * Real.pi) ∧
      Integrable (windingWeight (circleMap 0 R) 0 (2 * Real.pi)) ∧
      (∫ t in (0 : ℝ)..(2 * Real.pi), circulationFun areaP areaQ (circleMap 0 R) t) =
        Real.pi * R ^ 2 ∧
      (∫ z : ℂ, windingWeight (circleMap 0 R) 0 (2 * Real.pi) z) = Real.pi * R ^ 2 := by
  have h := green_area_form Real.two_pi_pos
    (absolutelyContinuous_circleMap 0 R 0 (2 * Real.pi)) (circleMap_closed 0 R)
  exact ⟨h.1, h.2.1, integral_circulationFun_area_circleMap R,
    h.2.2.symm.trans (integral_circulationFun_area_circleMap R)⟩

/-- Full Green's theorem on an ellipse gives the signed area `πab`, for either orientation. -/
theorem green_ellipse_area (a b : ℝ) :
    IntervalIntegrable (circulationFun areaP areaQ (ellipse a b)) volume 0 (2 * Real.pi) ∧
      Integrable (windingWeight (ellipse a b) 0 (2 * Real.pi)) ∧
      (∫ t in (0 : ℝ)..(2 * Real.pi), circulationFun areaP areaQ (ellipse a b) t) =
        Real.pi * a * b ∧
      (∫ z : ℂ, windingWeight (ellipse a b) 0 (2 * Real.pi) z) = Real.pi * a * b := by
  have h := green_area_form Real.two_pi_pos (absolutelyContinuous_ellipse a b) (ellipse_closed a b)
  exact ⟨h.1, h.2.1, integral_circulationFun_area_ellipse a b,
    h.2.2.symm.trans (integral_circulationFun_area_ellipse a b)⟩

/-- The actual twice-traversed circle satisfies full Green, with area counted twice. -/
theorem green_double_circle_area (R : ℝ) :
    IntervalIntegrable (circulationFun areaP areaQ (circleMap 0 R)) volume 0 (4 * Real.pi) ∧
      Integrable (windingWeight (circleMap 0 R) 0 (4 * Real.pi)) ∧
      (∫ t in (0 : ℝ)..(4 * Real.pi), circulationFun areaP areaQ (circleMap 0 R) t) =
        2 * Real.pi * R ^ 2 ∧
      (∫ z : ℂ, windingWeight (circleMap 0 R) 0 (4 * Real.pi) z) = 2 * Real.pi * R ^ 2 := by
  have h := green_area_form (by positivity : (0 : ℝ) < 4 * Real.pi)
    (absolutelyContinuous_circleMap 0 R 0 (4 * Real.pi)) (circleMap_twice_closed 0 R)
  exact ⟨h.1, h.2.1, integral_circulationFun_area_circleMap_twice R,
    h.2.2.symm.trans (integral_circulationFun_area_circleMap_twice R)⟩

/-- Full Green applies to the absolutely continuous square-root circle despite its
unbounded speed. -/
theorem green_sqrt_circle_area :
    IntervalIntegrable (circulationFun areaP areaQ sqrtCircle) volume 0 1 ∧
      Integrable (windingWeight sqrtCircle 0 1) ∧
      (∫ t in (0 : ℝ)..1, circulationFun areaP areaQ sqrtCircle t) = Real.pi ∧
      (∫ z : ℂ, windingWeight sqrtCircle 0 1 z) = Real.pi := by
  have h := green_area_form zero_lt_one absolutelyContinuous_sqrtCircle sqrtCircle_closed
  exact ⟨h.1, h.2.1, integral_circulationFun_area_sqrtCircle,
    h.2.2.symm.trans integral_circulationFun_area_sqrtCircle⟩

/-- The two-component annulus satisfies the finite-family Green theorem using total-index
cancellation in the hole. Its actual area integral is `π(R²-r²)` on an annular field domain. -/
theorem green_annulus_area {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    IntervalIntegrable (circulationFun areaP areaQ (circleMap 0 R)) volume 0 (2 * Real.pi) ∧
      IntervalIntegrable (circulationFun areaP areaQ (clockwiseCircle r)) volume 0 (2 * Real.pi) ∧
      IntegrableOn (fun z ↦ windingWeight (circleMap 0 R) 0 (2 * Real.pi) z +
        windingWeight (clockwiseCircle r) 0 (2 * Real.pi) z) (annulusDomain r R) ∧
      (∫ z in annulusDomain r R, windingWeight (circleMap 0 R) 0 (2 * Real.pi) z +
        windingWeight (clockwiseCircle r) 0 (2 * Real.pi) z) = Real.pi * (R ^ 2 - r ^ 2) := by
  let γ : Bool → ℝ → ℂ := fun i ↦ if i then circleMap 0 R else clockwiseCircle r
  have hγ (i : Bool) : AbsolutelyContinuousOnInterval (γ i) 0 (2 * Real.pi) := by
    cases i
    · exact absolutelyContinuous_clockwiseCircle r
    · exact absolutelyContinuous_circleMap 0 R 0 (2 * Real.pi)
  have hclosed (i : Bool) : γ i 0 = γ i (2 * Real.pi) := by
    cases i
    · exact clockwiseCircle_closed r
    · exact circleMap_closed 0 R
  have ht := traces_subset_annulusDomain hr hrR
  have htrace (i : Bool) : γ i '' uIcc 0 (2 * Real.pi) ⊆ annulusDomain r R := by
    cases i
    · exact ht.2
    · exact ht.1
  have h := green_ac_winding_sum (s := Finset.univ) (γ := γ)
    (a := fun _ ↦ 0) (b := fun _ ↦ 2 * Real.pi) (w := fun _ ↦ 1)
    (fun _ _ ↦ Real.two_pi_pos) (fun i _ ↦ hγ i) (fun i _ ↦ hclosed i)
    (isOpen_annulusDomain r R) (fun i _ ↦ htrace i)
    (contDiff_areaP (n := 1)).contDiffOn (contDiff_areaQ (n := 1)).contDiffOn
    (fun z hz ↦ by
      simpa [γ, add_comm] using windingNumber_annulus_zero_on_compl hr hrR hz)
  have hb := h.2.2
  have hi := h.2.1
  simp only [Fintype.univ_bool, Int.cast_one, one_mul, Finset.mem_singleton, Bool.true_eq_false,
    not_false_eq_true, Finset.sum_insert, ↓reduceIte, Finset.sum_singleton, Bool.false_eq_true,
    curl_area, mul_one, γ] at hb hi
  have he : (∫ z in annulusDomain r R, windingWeight (circleMap 0 R) 0 (2 * Real.pi) z +
      windingWeight (clockwiseCircle r) 0 (2 * Real.pi) z) = Real.pi * (R ^ 2 - r ^ 2) := by
    rw [← integral_circulationFun_area_annulus r R]
    simpa only [add_comm] using hb.symm
  refine ⟨h.1 true (Finset.mem_univ _), h.1 false (Finset.mem_univ _), ?_, he⟩
  simpa only [add_comm] using hi

end TauCeti.Green.Examples
