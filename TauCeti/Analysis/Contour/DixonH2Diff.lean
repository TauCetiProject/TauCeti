/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.DixonDef
import TauCeti.Analysis.Contour.CurveDistance
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Holomorphy of Dixon's `h₂` off the curve

Dixon's `h₂` integral `dixonH2 f γ a b w = ∫ t in a..b, f (γ t) / (γ t - w) * deriv γ t` is
holomorphic in the point `w`, at every `w` off the curve. This is the Cauchy-type half of the
analyticity of Dixon's glued function; it is obtained from the parametric Leibniz rule
(differentiation under the integral sign), differentiating the pole factor `(γ t - w)⁻¹`.

## Main results

* `TauCeti.Contour.dixonH2_differentiableAt` — `fun w ↦ dixonH2 f γ a b w` is complex-differentiable
  at every point off the curve, given continuity of `γ` and of `f` along the curve and
  interval-integrability of `deriv γ`.

This feeds the `homologyCauchyTheorem` roadmap target
(`TauCetiRoadmap/ContourIntegration/Suggested.lean`, Layer 3, Dixon's argument).

## Provenance

Adapted from `dixonH2_differentiableAt` and `dixonH2_differentiableAt_of_regular` in
`DixonDiff.lean` of the AINTLIB `LeanModularForms` development, restated for a raw `γ : ℝ → ℂ` on an
oriented interval and phrased with an interval-integrable derivative in place of a global Lipschitz
constant. See J. D. Dixon, *A brief proof of Cauchy's integral theorem* (1971).
-/

public section

open Complex MeasureTheory Set

open scoped Real Interval

namespace TauCeti.Contour

section

variable {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} {w : ℂ}

/-- The `w`-derivative of the `h₂` integrand's pole factor: `w' ↦ fz · (z - w')⁻¹ · c` has
derivative `fz · (z - w)⁻¹² · c` at `w` whenever `z ≠ w`. -/
private theorem h2_pole_hasDerivAt (fz c z w : ℂ) (hne : z - w ≠ 0) :
    HasDerivAt (fun w' ↦ fz * (z - w')⁻¹ * c) (fz * (z - w)⁻¹ ^ 2 * c) w := by
  have h_sub : HasDerivAt (fun w' ↦ z - w') (-1) w := HasDerivAt.const_sub z (hasDerivAt_id w)
  have h_inv : HasDerivAt (fun w' ↦ (z - w')⁻¹) ((z - w)⁻¹ ^ 2) w := by
    have h := HasDerivAt.inv h_sub hne
    rw [show (- -1 / (z - w) ^ 2 : ℂ) = (z - w)⁻¹ ^ 2 by rw [inv_pow]; ring] at h
    exact h
  exact ((h_inv.const_mul fz).mul_const c).congr_deriv (by ring)

/-- A continuous factor times `deriv γ` is a.e. strongly measurable on `Ι a b`. -/
private theorem aestronglyMeasurable_mul_deriv {g : ℝ → ℂ} (hg : ContinuousOn g (uIcc a b)) :
    AEStronglyMeasurable (fun t ↦ g t * deriv γ t) (volume.restrict (Ι a b)) :=
  ((hg.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc).mul
    (stronglyMeasurable_deriv γ).aestronglyMeasurable

/-- The continuous factor `f (γ ·) · (γ · - w')⁻¹` of the `h₂` integrand, off the curve. -/
private theorem h2_factor_continuousOn (hγ_cont : ContinuousOn γ (uIcc a b))
    (hf_cont : ContinuousOn f (γ '' uIcc a b)) {w' : ℂ} (hoff : ∀ t ∈ uIcc a b, γ t ≠ w') :
    ContinuousOn (fun t ↦ f (γ t) * (γ t - w')⁻¹) (uIcc a b) :=
  (hf_cont.comp hγ_cont fun _ ht ↦ mem_image_of_mem γ ht).mul
    ((hγ_cont.sub continuousOn_const).inv₀ fun t ht ↦ sub_ne_zero.mpr (hoff t ht))

/-- The continuous factor `f (γ ·) · (γ · - w')⁻¹²` of the derivative integrand, off the curve. -/
private theorem h2_sq_factor_continuousOn (hγ_cont : ContinuousOn γ (uIcc a b))
    (hf_cont : ContinuousOn f (γ '' uIcc a b)) {w' : ℂ} (hoff : ∀ t ∈ uIcc a b, γ t ≠ w') :
    ContinuousOn (fun t ↦ f (γ t) * (γ t - w')⁻¹ ^ 2) (uIcc a b) :=
  (hf_cont.comp hγ_cont fun _ ht ↦ mem_image_of_mem γ ht).mul
    (((hγ_cont.sub continuousOn_const).inv₀ fun t ht ↦ sub_ne_zero.mpr (hoff t ht)).pow 2)

/-- On a ball avoiding `w`, the squared-pole integrand is bounded by `M · ε⁻² · ‖deriv γ t‖`. -/
private theorem h2_deriv_integrand_norm_bound {M ε : ℝ} (hM_nn : 0 ≤ M) (hε_pos : 0 < ε)
    (hM : ∀ t ∈ uIcc a b, ‖f (γ t)‖ ≤ M) {w' : ℂ}
    (h_dist : ∀ t ∈ uIcc a b, ε ≤ ‖γ t - w'‖) {t : ℝ} (ht : t ∈ uIcc a b) :
    ‖f (γ t) * (γ t - w')⁻¹ ^ 2 * deriv γ t‖ ≤ M * ε⁻¹ ^ 2 * ‖deriv γ t‖ := by
  rw [norm_mul, norm_mul, norm_pow, norm_inv]
  gcongr
  · exact hM t ht
  · exact h_dist t ht

/-- Points in the `ρ/2`-ball about an off-curve `w` stay `ρ/2` away from the curve. -/
private theorem h2_ball_dist {ρ : ℝ} (hρ_dist : ∀ t ∈ uIcc a b, ρ ≤ ‖γ t - w‖)
    {w' : ℂ} (hw' : w' ∈ Metric.ball w (ρ / 2)) (t : ℝ) (ht : t ∈ uIcc a b) :
    ρ / 2 ≤ ‖γ t - w'‖ := by
  rw [Metric.mem_ball, Complex.dist_eq] at hw'
  have h := norm_sub_norm_le (γ t - w) (w' - w)
  rw [show γ t - w - (w' - w) = γ t - w' by ring] at h
  linarith [hρ_dist t ht]

/-- On the `ρ/2`-ball, every point stays off the curve. -/
private theorem h2_ball_avoids {ρ : ℝ} (hρ_pos : 0 < ρ) (hρ_dist : ∀ t ∈ uIcc a b, ρ ≤ ‖γ t - w‖)
    {w' : ℂ} (hw' : w' ∈ Metric.ball w (ρ / 2)) : ∀ t ∈ uIcc a b, γ t ≠ w' := fun t ht heq ↦ by
  have hd := h2_ball_dist hρ_dist hw' t ht
  rw [heq, sub_self, norm_zero] at hd
  linarith

/-- A uniform bound on `‖f (γ ·)‖` over the interval, from continuity of `f` along the curve. -/
private theorem h2_fγ_bddAbove (hγ_cont : ContinuousOn γ (uIcc a b))
    (hf_cont : ContinuousOn f (γ '' uIcc a b)) :
    ∃ M, 0 ≤ M ∧ ∀ t ∈ uIcc a b, ‖f (γ t)‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_uIcc).bddAbove_image
    (hf_cont.comp hγ_cont fun _ ht ↦ mem_image_of_mem γ ht).norm
  exact ⟨max M 0, le_max_right _ _, fun t ht ↦ le_max_of_le_left (hM ⟨t, ht, rfl⟩)⟩

/-- **`dixonH2` is holomorphic in the point, off the curve.** If `γ` is continuous on `uIcc a b`
and avoids `w` there, `f` is continuous along the curve, and `deriv γ` is interval-integrable, then
`fun w ↦ dixonH2 f γ a b w` is complex-differentiable at `w`. The proof differentiates under the
integral sign (parametric Leibniz), differentiating the pole factor `(γ t - w)⁻¹`. -/
theorem dixonH2_differentiableAt (hγ_cont : ContinuousOn γ (uIcc a b))
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ w) (hf_cont : ContinuousOn f (γ '' uIcc a b))
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) :
    DifferentiableAt ℂ (dixonH2 f γ a b) w := by
  obtain ⟨ρ, hρ_pos, hρ_dist⟩ := exists_curve_dist_lower_bound hγ_cont hoff
  obtain ⟨M, hM_nn, hM⟩ := h2_fγ_bddAbove hγ_cont hf_cont
  have hε_pos : 0 < ρ / 2 := half_pos hρ_pos
  have h_eq : dixonH2 f γ a b = fun w' ↦ ∫ t in a..b, f (γ t) * (γ t - w')⁻¹ * deriv γ t := by
    funext w'
    rw [dixonH2_def]
    exact intervalIntegral.integral_congr fun t _ ↦ by ring
  rw [h_eq]
  refine ((intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ)
    (F := fun w' t ↦ f (γ t) * (γ t - w')⁻¹ * deriv γ t)
    (F' := fun w' t ↦ f (γ t) * (γ t - w')⁻¹ ^ 2 * deriv γ t)
    (bound := fun t ↦ M * (ρ / 2)⁻¹ ^ 2 * ‖deriv γ t‖)
    (Metric.ball_mem_nhds w hε_pos) ?_
    (hderiv_int.continuousOn_mul (h2_factor_continuousOn hγ_cont hf_cont hoff))
    (aestronglyMeasurable_mul_deriv (h2_sq_factor_continuousOn hγ_cont hf_cont hoff)) ?_
    (hderiv_int.norm.const_mul (M * (ρ / 2)⁻¹ ^ 2)) ?_).2).differentiableAt
  · filter_upwards [Metric.ball_mem_nhds w hε_pos] with w' hw'
    exact aestronglyMeasurable_mul_deriv
      (h2_factor_continuousOn hγ_cont hf_cont (h2_ball_avoids hρ_pos hρ_dist hw'))
  · refine Filter.Eventually.of_forall fun t ht w' hw' ↦ ?_
    exact h2_deriv_integrand_norm_bound hM_nn hε_pos hM
      (fun s hs ↦ h2_ball_dist hρ_dist hw' s hs) (Set.uIoc_subset_uIcc ht)
  · refine Filter.Eventually.of_forall fun t ht w' hw' ↦ ?_
    exact h2_pole_hasDerivAt (f (γ t)) (deriv γ t) (γ t) w'
      (sub_ne_zero.mpr (h2_ball_avoids hρ_pos hρ_dist hw' t (Set.uIoc_subset_uIcc ht)))

end

end TauCeti.Contour
