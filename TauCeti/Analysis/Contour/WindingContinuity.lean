module

public import TauCeti.Analysis.Contour.WindingNumber
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.Contour.CurveDistance
import TauCeti.Analysis.Contour.WindingNumberReverse

/-!
# Continuity of the generalized winding number in the point

For a curve `γ` continuous on the interval with endpoints `a`, `b` whose index integrand
`(γ · - w₀)⁻¹ * deriv γ` at an avoided point `w₀` is interval-integrable, the generalized winding
number `fun w ↦ windingNumber γ a b w` is continuous at `w₀`
(`continuousAt_windingNumber_of_avoidance`). Combined with integer-valuedness for closed curves
(`exists_int_windingNumber_of_closed`), this yields that the winding number is locally constant on
the complement of the curve — a step toward the homology form of Cauchy's theorem.

## Main results

* `TauCeti.Contour.continuousAt_windingNumber_of_avoidance` — the generalized winding number is
  continuous in the point, off the curve, on an arbitrary oriented interval.

## Provenance

Adapted from `generalizedWindingNumber_continuousAt_of_avoids` in `GeneralizedWindingNumber.lean` of
the AINTLIB `LeanModularForms` development, restated for a raw `γ : ℝ → ℂ` on `[a, b]`.
-/

public section

open Complex MeasureTheory Set

open scoped Interval

namespace TauCeti.Contour

/-- **Uniform distance to the curve near an avoided point.** If `γ` is continuous on the compact
interval `[a, b]` and avoids `w₀` there, then there is a radius `ε > 0` such that every `w` within
`ε` of `w₀` stays at distance at least `ε` from the whole curve `γ '' [a, b]`. Uses the distance to
the compact image `Metric.infDist w₀ (γ '' Icc a b)`. -/
private theorem exists_ball_dist_curve_lower_bound {γ : ℝ → ℂ} {w₀ : ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ_cont : ContinuousOn γ (Icc a b)) (h_avoid : ∀ t ∈ Icc a b, γ t ≠ w₀) :
    ∃ ε > 0, ∀ w ∈ Metric.ball w₀ ε, ∀ t ∈ Icc a b, ε ≤ ‖γ t - w‖ := by
  obtain ⟨ρ, hρ_pos, h_dist_lb⟩ := exists_curve_dist_lower_bound
    (by rw [Set.uIcc_of_le hab]; exact hγ_cont) (by rw [Set.uIcc_of_le hab]; exact h_avoid)
  rw [Set.uIcc_of_le hab] at h_dist_lb
  refine ⟨ρ / 2, half_pos hρ_pos, fun w hw t ht ↦ ?_⟩
  rw [Metric.mem_ball, Complex.dist_eq] at hw
  have h2 : ‖γ t - w₀‖ - ‖w - w₀‖ ≤ ‖γ t - w‖ := by
    have h := norm_sub_norm_le (γ t - w₀) (w - w₀)
    rwa [sub_sub_sub_cancel_right] at h
  linarith [h_dist_lb t ht]

/-- **Integrability of the index integrand for a point off the curve.** If `w` stays a positive
distance `ε` from `γ` on `[a, b]` (so `γ · - w` is nowhere zero and `(γ · - w)⁻¹` is continuous)
and `deriv γ` is interval-integrable, then `(γ t - w)⁻¹ * deriv γ t` is interval-integrable, being
a continuous factor times an integrable one. -/
private theorem intervalIntegrable_inv_sub_mul_deriv {γ : ℝ → ℂ} {w : ℂ} {a b ε : ℝ} (hab : a ≤ b)
    (hε_pos : 0 < ε) (h_dist : ∀ t ∈ Icc a b, ε ≤ ‖γ t - w‖) (hγ_cont : ContinuousOn γ (Icc a b))
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) :
    IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b := by
  have h_ne : ∀ t ∈ Icc a b, γ t - w ≠ 0 := fun t ht ↦
    norm_pos_iff.mp (lt_of_lt_of_le hε_pos (h_dist t ht))
  have hcont : ContinuousOn (fun t ↦ (γ t - w)⁻¹) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]; exact (hγ_cont.sub continuousOn_const).inv₀ h_ne
  exact hderiv_int.continuousOn_mul hcont

/-- The `a ≤ b` case of `continuousAt_windingNumber_of_avoidance`. -/
private theorem continuousAt_windingNumber_of_avoidance_of_le {γ : ℝ → ℂ} {w₀ : ℂ} {a b : ℝ}
    (hab : a ≤ b) (hγ_cont : ContinuousOn γ (Icc a b)) (h_avoid : ∀ t ∈ Icc a b, γ t ≠ w₀)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) :
    ContinuousAt (fun w ↦ windingNumber γ a b w) w₀ := by
  obtain ⟨ε, hε_pos, h_dist_lb⟩ := exists_ball_dist_curve_lower_bound hab hγ_cont h_avoid
  set F : ℂ → ℝ → ℂ := fun w t ↦ (γ t - w)⁻¹ * deriv γ t with hF_def
  have h_ne : ∀ w ∈ Metric.ball w₀ ε, ∀ t ∈ Icc a b, γ t - w ≠ 0 := fun w hw t ht ↦
    norm_pos_iff.mp (lt_of_lt_of_le hε_pos (h_dist_lb w hw t ht))
  have h_meas : ∀ w ∈ Metric.ball w₀ ε,
      AEStronglyMeasurable (F w) (volume.restrict (Ι a b)) := by
    intro w hw
    rw [Set.uIoc_of_le hab]
    refine AEStronglyMeasurable.mul ?_ (aestronglyMeasurable_deriv γ _)
    exact (((hγ_cont.sub continuousOn_const).inv₀ (h_ne w hw)).mono
      Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have h_bound : ∀ w ∈ Metric.ball w₀ ε, ∀ t ∈ Icc a b, ‖F w t‖ ≤ ε⁻¹ * ‖deriv γ t‖ := by
    intro w hw t ht
    rw [hF_def, norm_mul, norm_inv]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hε_pos (h_dist_lb w hw t ht)) (norm_nonneg _)
  have h_eq_nbhd : (fun w ↦ windingNumber γ a b w) =ᶠ[nhds w₀]
      fun w ↦ (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∫ t in a..b, F w t := by
    filter_upwards [Metric.ball_mem_nhds w₀ hε_pos] with w hw
    refine windingNumber_eq_integral_of_avoidance ?_ ?_
      (intervalIntegrable_inv_sub_mul_deriv hab hε_pos (h_dist_lb w hw) hγ_cont hderiv_int)
    · rw [Set.uIcc_of_le hab]; exact hγ_cont
    · rw [Set.uIcc_of_le hab]; exact fun t ht ↦ sub_ne_zero.mp (h_ne w hw t ht)
  refine ContinuousAt.congr ?_ h_eq_nbhd.symm
  refine ContinuousAt.mul continuousAt_const ?_
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun t ↦ ε⁻¹ * ‖deriv γ t‖)
    ?_ ?_ (hderiv_int.norm.const_mul ε⁻¹) ?_
  · filter_upwards [Metric.ball_mem_nhds w₀ hε_pos] with w hw using h_meas w hw
  · filter_upwards [Metric.ball_mem_nhds w₀ hε_pos] with w hw
    refine ae_of_all _ fun t htI ↦ ?_
    rw [Set.uIoc_of_le hab] at htI
    exact h_bound w hw t (Ioc_subset_Icc_self htI)
  · refine ae_of_all _ fun t htI ↦ ?_
    rw [Set.uIoc_of_le hab] at htI
    have ht_Icc : t ∈ Icc a b := Ioc_subset_Icc_self htI
    exact (((continuous_const.sub continuous_id).continuousAt).inv₀
      (h_ne w₀ (Metric.mem_ball_self hε_pos) t ht_Icc)).mul continuousAt_const

/-- **The generalized winding number is continuous in the point, off the curve.** If `γ` is
continuous on `Set.uIcc a b`, avoids `w₀` there, and the index integrand `(γ · - w₀)⁻¹ * deriv γ`
at `w₀` is interval-integrable, then `fun w ↦ windingNumber γ a b w` is continuous at `w₀`, on an
arbitrary oriented interval. The stated hypothesis matches `windingNumber_eq_integral_of_avoidance`
and `exists_int_windingNumber_of_closed`. -/
theorem continuousAt_windingNumber_of_avoidance {γ : ℝ → ℂ} {w₀ : ℂ} {a b : ℝ}
    (hγ_cont : ContinuousOn γ (Set.uIcc a b)) (h_avoid : ∀ t ∈ Set.uIcc a b, γ t ≠ w₀)
    (h_int : IntervalIntegrable (fun t ↦ (γ t - w₀)⁻¹ * deriv γ t) volume a b) :
    ContinuousAt (fun w ↦ windingNumber γ a b w) w₀ := by
  have hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b := by
    have hmul : IntervalIntegrable
        (fun t ↦ (γ t - w₀)⁻¹ * deriv γ t * (γ t - w₀)) volume a b :=
      h_int.mul_continuousOn (hγ_cont.sub continuousOn_const)
    refine hmul.congr (fun t ht ↦ ?_)
    have hne : γ t - w₀ ≠ 0 := sub_ne_zero.mpr (h_avoid t (uIoc_subset_uIcc ht))
    rw [mul_right_comm, inv_mul_cancel₀ hne, one_mul]
  rcases le_total a b with hab | hba
  · rw [Set.uIcc_of_le hab] at hγ_cont h_avoid
    exact continuousAt_windingNumber_of_avoidance_of_le hab hγ_cont h_avoid hderiv_int
  · rw [Set.uIcc_of_ge hba] at hγ_cont h_avoid
    have hcore :=
      continuousAt_windingNumber_of_avoidance_of_le hba hγ_cont h_avoid hderiv_int.symm
    obtain ⟨ε, hε_pos, h_dist_lb⟩ := exists_ball_dist_curve_lower_bound hba hγ_cont h_avoid
    have h_eq : (fun w ↦ windingNumber γ a b w) =ᶠ[nhds w₀] fun w ↦ -windingNumber γ b a w := by
      filter_upwards [Metric.ball_mem_nhds w₀ hε_pos] with w hw
      have h_ne : ∀ t ∈ Icc b a, γ t - w ≠ 0 := fun t ht ↦
        norm_pos_iff.mp (lt_of_lt_of_le hε_pos (h_dist_lb w hw t ht))
      have hcont_u : ContinuousOn γ (Set.uIcc b a) := by rw [Set.uIcc_of_le hba]; exact hγ_cont
      have havoid_u : ∀ t ∈ Set.uIcc b a, γ t ≠ w := by
        rw [Set.uIcc_of_le hba]; exact fun t ht ↦ sub_ne_zero.mp (h_ne t ht)
      have hintg := intervalIntegrable_inv_sub_mul_deriv hba hε_pos (h_dist_lb w hw) hγ_cont
        hderiv_int.symm
      exact windingNumber_symm (cauchyPVExistsAt_of_avoidance hcont_u havoid_u hintg)
    exact hcore.neg.congr h_eq.symm

end TauCeti.Contour
