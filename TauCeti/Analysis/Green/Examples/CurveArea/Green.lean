/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Winding
public import TauCeti.Analysis.Green.FiniteSum
public import TauCeti.Analysis.Green.Examples.CurveArea.Ellipse
public import TauCeti.Analysis.Green.Examples.CurveArea.DoubleTraversal
public import TauCeti.Analysis.Green.Examples.CurveArea.SqrtReparam
public import TauCeti.Analysis.Green.Examples.CurveArea.Annulus
public import TauCeti.Analysis.Green.Examples.CurveArea.Winding

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
  exact ⟨hγ.intervalIntegrable_circulationFun
      ((contDiff_areaP (n := 1)).continuous.continuousOn)
      ((contDiff_areaQ (n := 1)).continuous.continuousOn),
    hγ.integrable_windingWeight hclosed,
    (signedArea_eq_integral_circulationFun γ a b).symm.trans
      (signedArea_eq_integral_windingWeight hab hγ hclosed)⟩

/-- Full Green's theorem gives both integrability conclusions and disc area for a circle. -/
theorem green_circle_area (R : ℝ) :
    IntervalIntegrable (circulationFun areaP areaQ (circleMap 0 R)) volume 0 (2 * Real.pi) ∧
      Integrable (windingWeight (circleMap 0 R) 0 (2 * Real.pi)) ∧
      (∫ t in (0 : ℝ)..(2 * Real.pi), circulationFun areaP areaQ (circleMap 0 R) t) =
        Real.pi * R ^ 2 ∧
      (∫ z : ℂ, windingWeight (circleMap 0 R) 0 (2 * Real.pi) z) = Real.pi * R ^ 2 := by
  have h := green_area_form Real.two_pi_pos
    ((lipschitzWith_circleMap 0 R).lipschitzOnWith.absolutelyContinuousOnInterval
      (a := 0) (b := 2 * Real.pi))
    (by simpa only [zero_add] using (periodic_circleMap 0 R 0).symm)
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

/-- For positive axes, full Green identifies the actual ellipse-interior area, rather than
only a signed winding-weight integral. Its Jacobian area is reconciled with the same result. -/
theorem green_ellipse_region_area {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    let D := ellipseCoordinates a b ha.ne' hb.ne' '' Metric.ball (0 : ℂ) 1
    IntervalIntegrable (circulationFun areaP areaQ (ellipse a b)) volume 0 (2 * Real.pi) ∧
      IntegrableOn (fun _ : ℂ ↦ (1 : ℝ)) D ∧
      (∫ _ in D, (1 : ℝ)) = Real.pi * a * b ∧
      volume D = ENNReal.ofReal (Real.pi * a * b) := by
  let A := ellipseCoordinates a b ha.ne' hb.ne'
  let D := A '' Metric.ball (0 : ℂ) 1
  have hD : MeasurableSet D :=
    (A.toHomeomorph.isOpenMap _ Metric.isOpen_ball).measurableSet
  have h := green_ellipse_area a b
  have he : windingWeight (ellipse a b) 0 (2 * Real.pi) = D.indicator 1 := by
    funext z
    exact windingWeight_ellipse ha hb z
  have hi : IntegrableOn (fun _ : ℂ ↦ (1 : ℝ)) D := by
    rw [he] at h
    exact (integrable_indicator_iff hD).mp h.2.1
  have harea : (∫ _ in D, (1 : ℝ)) = Real.pi * a * b := by
    have hh := h.2.2.2
    rw [he, integral_indicator hD] at hh
    exact hh
  have hJac : volume D = ENNReal.ofReal (Real.pi * |a * b|) := by
    simpa only [affineMap_apply, add_zero, ContinuousLinearEquiv.coe_coe] using
      volume_ellipse_image_ball a b ha.ne' hb.ne'
  have hfinite : volume D ≠ ⊤ := by rw [hJac]; exact ENNReal.ofReal_ne_top
  refine ⟨h.1, hi, harea, ?_⟩
  calc
    volume D = ENNReal.ofReal (volume D).toReal := (ENNReal.ofReal_toReal hfinite).symm
    _ = ENNReal.ofReal (Real.pi * a * b) := by
      congr 1
      simpa only [setIntegral_const, Measure.real, smul_eq_mul, mul_one] using harea

/-- The actual twice-traversed circle satisfies full Green, with area counted twice. -/
theorem green_double_circle_area (R : ℝ) :
    IntervalIntegrable (circulationFun areaP areaQ (circleMap 0 R)) volume 0 (4 * Real.pi) ∧
      Integrable (windingWeight (circleMap 0 R) 0 (4 * Real.pi)) ∧
      (∫ t in (0 : ℝ)..(4 * Real.pi), circulationFun areaP areaQ (circleMap 0 R) t) =
        2 * Real.pi * R ^ 2 ∧
      (∫ z : ℂ, windingWeight (circleMap 0 R) 0 (4 * Real.pi) z) = 2 * Real.pi * R ^ 2 := by
  have h := green_area_form (by positivity : (0 : ℝ) < 4 * Real.pi)
    ((lipschitzWith_circleMap 0 R).lipschitzOnWith.absolutelyContinuousOnInterval
      (a := 0) (b := 4 * Real.pi))
    (circleMap_twice_closed 0 R)
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
cancellation in the hole. Its actual area integral and boundary circulation both equal
`π(R²-r²)` on an annular field domain. -/
theorem green_annulus_area {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    IntervalIntegrable (circulationFun areaP areaQ (circleMap 0 R)) volume 0 (2 * Real.pi) ∧
      IntervalIntegrable (circulationFun areaP areaQ (clockwiseCircle r)) volume 0 (2 * Real.pi) ∧
      IntegrableOn (fun z ↦ windingWeight (circleMap 0 R) 0 (2 * Real.pi) z +
        windingWeight (clockwiseCircle r) 0 (2 * Real.pi) z) (annulusDomain r R) ∧
      (∫ z in annulusDomain r R, windingWeight (circleMap 0 R) 0 (2 * Real.pi) z +
        windingWeight (clockwiseCircle r) 0 (2 * Real.pi) z) = Real.pi * (R ^ 2 - r ^ 2) ∧
      (∫ t in (0 : ℝ)..(2 * Real.pi), circulationFun areaP areaQ (circleMap 0 R) t) +
        (∫ t in (0 : ℝ)..(2 * Real.pi), circulationFun areaP areaQ (clockwiseCircle r) t) =
        Real.pi * (R ^ 2 - r ^ 2) := by
  let γ : Bool → ℝ → ℂ := fun i ↦ if i then circleMap 0 R else clockwiseCircle r
  have hγ (i : Bool) : AbsolutelyContinuousOnInterval (γ i) 0 (2 * Real.pi) := by
    cases i
    · exact absolutelyContinuous_clockwiseCircle r
    · exact (lipschitzWith_circleMap 0 R).lipschitzOnWith.absolutelyContinuousOnInterval
        (a := 0) (b := 2 * Real.pi)
  have hclosed (i : Bool) : γ i 0 = γ i (2 * Real.pi) := by
    cases i
    · exact clockwiseCircle_closed r
    · simpa [γ] using (periodic_circleMap 0 R 0).symm
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
  refine ⟨h.1 true (Finset.mem_univ _), h.1 false (Finset.mem_univ _), ?_, he,
    integral_circulationFun_area_annulus r R⟩
  simpa only [add_comm] using hi

/-- Full Green for the clockwise-inner annular boundary gives the actual geometric annulus
area and the same boundary circulation. The winding weight is replaced by its annulus indicator
only almost everywhere, so the zero-on-trace convention does not discard the inner boundary's
exceptional values. -/
theorem green_annulus_region_area {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    let D := Metric.ball (0 : ℂ) R \ Metric.closedBall 0 r
    IntervalIntegrable (circulationFun areaP areaQ (circleMap 0 R)) volume 0 (2 * Real.pi) ∧
      IntervalIntegrable (circulationFun areaP areaQ (clockwiseCircle r)) volume 0 (2 * Real.pi) ∧
      IntegrableOn (fun _ : ℂ ↦ (1 : ℝ)) D ∧
      (∫ _ in D, (1 : ℝ)) = Real.pi * (R ^ 2 - r ^ 2) ∧
      volume D = ENNReal.ofReal (Real.pi * (R ^ 2 - r ^ 2)) ∧
      (∫ t in (0 : ℝ)..(2 * Real.pi), circulationFun areaP areaQ (circleMap 0 R) t) +
        (∫ t in (0 : ℝ)..(2 * Real.pi), circulationFun areaP areaQ (clockwiseCircle r) t) =
        Real.pi * (R ^ 2 - r ^ 2) := by
  let D := Metric.ball (0 : ℂ) R \ Metric.closedBall 0 r
  have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet.diff
    Metric.isClosed_closedBall.measurableSet
  have hs : D ⊆ annulusDomain r R := by
    intro z hz
    rw [mem_annulusDomain]
    have hz' : ‖z‖ < R ∧ r < ‖z‖ := by
      simpa only [D, mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, dist_zero_right,
        not_le] using hz
    constructor <;> linarith [hz'.1, hz'.2]
  have h := green_annulus_area hr hrR
  have he := windingWeight_annulus_ae_eq_indicator hr hrR
  have hi : IntegrableOn (fun _ : ℂ ↦ (1 : ℝ)) D := by
    have hh := h.2.2.1.congr_fun_ae (ae_restrict_of_ae he)
    have hmask := (integrable_indicator_iff hD).mp hh
    rw [IntegrableOn, Measure.restrict_restrict hD, inter_eq_left.mpr hs] at hmask
    rw [IntegrableOn]
    convert! hmask using 1
  have harea : (∫ _ in D, (1 : ℝ)) = Real.pi * (R ^ 2 - r ^ 2) := by
    have hh := h.2.2.2.1
    rw [integral_congr_ae (ae_restrict_of_ae he), setIntegral_indicator hD,
      inter_eq_right.mpr hs] at hh
    exact hh
  have hsub : D ⊆ Metric.ball (0 : ℂ) R := sdiff_subset
  have hfinite : volume D ≠ ⊤ := (measure_mono hsub).trans_lt measure_ball_lt_top |>.ne
  refine ⟨h.1, h.2.1, hi, harea, ?_, h.2.2.2.2⟩
  calc
    volume D = ENNReal.ofReal (volume D).toReal := (ENNReal.ofReal_toReal hfinite).symm
    _ = ENNReal.ofReal (Real.pi * (R ^ 2 - r ^ 2)) := by
      congr 1
      simpa only [setIntegral_const, Measure.real, smul_eq_mul, mul_one] using harea

end TauCeti.Green.Examples
