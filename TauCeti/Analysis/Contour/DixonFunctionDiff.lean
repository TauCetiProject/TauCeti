/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.DixonDef
import TauCeti.Analysis.Contour.DixonH1Diff
import TauCeti.Analysis.Contour.DixonH2Diff
import TauCeti.Analysis.Contour.WindingLocallyConstant
import TauCeti.Analysis.Contour.CurveDistance

/-!
# The Dixon function is entire

Dixon's glued function `dixonFunction f U γ a b` — equal to `dixonH1` on `U` and `dixonH2` off `U`
— is complex-differentiable on all of `ℂ` when `f` is holomorphic on the open set `U` and the
curve `γ` lives in `U`, is null-homologous there, is closed, and is differentiable off a countable
set with interval-integrable derivative. On `U`
it agrees with the holomorphic `dixonH1`; off `U` (hence off the curve) it agrees with the
holomorphic `dixonH2`, and the two pieces match across `∂U` because the winding number vanishes
there, so the `h₁`/`h₂` identity collapses.

## Main results

* `TauCeti.Contour.differentiable_dixonFunction` — `dixonFunction f U γ a b` is entire.

This is the analyticity input to the Liouville step of Dixon's proof of the homology form of
Cauchy's theorem (`homologyCauchyTheorem`, `TauCetiRoadmap/ContourIntegration/Suggested.lean`).

## Provenance

Adapted from `dixonFunction_differentiable` in `DixonDiff.lean` of the AINTLIB `LeanModularForms`
development, restated for a raw `γ : ℝ → ℂ` on an oriented interval. See J. D. Dixon, *A brief proof
of Cauchy's integral theorem* (1971).
-/

public section

open Complex MeasureTheory Set

open scoped Real Interval Topology

namespace TauCeti.Contour

section

variable {f : ℂ → ℂ} {U : Set ℂ} {γ : ℝ → ℂ} {a b : ℝ} {P : Set ℝ} {w : ℂ}

/-- The Cauchy-type integrand `f (γ ·) / (γ · - w) · deriv γ` is interval-integrable for `w` off the
curve: a continuous factor (using `f` continuous on `U ⊇ γ`) times the integrable derivative. -/
private theorem cauchy_integrand_intervalIntegrable (hf : DifferentiableOn ℂ f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b)
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ w) :
    IntervalIntegrable (fun t ↦ f (γ t) / (γ t - w) * deriv γ t) volume a b :=
  hderiv_int.continuousOn_mul (((hf.continuousOn.comp hγ_cont hγU).div
    (hγ_cont.sub continuousOn_const) fun t ht ↦ sub_ne_zero.mpr (hoff t ht)))

/-- The index integrand `(γ · - w)⁻¹ · deriv γ` is interval-integrable for `w` off the curve. -/
private theorem base_integrand_intervalIntegrable (hγ_cont : ContinuousOn γ (uIcc a b))
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b)
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ w) :
    IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b :=
  hderiv_int.continuousOn_mul ((hγ_cont.sub continuousOn_const).inv₀
    fun t ht ↦ sub_ne_zero.mpr (hoff t ht))

/-- Near an off-curve point where the winding number vanishes, it vanishes throughout a ball (and
the ball stays off the curve): the winding number is locally constant off the closed curve. -/
private theorem exists_ball_windingNumber_zero (hclosed : γ a = γ b) (hP : P.Countable)
    (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b)
    (hoff : ∀ t ∈ uIcc a b, γ t ≠ w) (hw_zero : windingNumber γ a b w = 0) :
    ∃ ε > 0, ∀ w' ∈ Metric.ball w ε,
      (∀ t ∈ uIcc a b, γ t ≠ w') ∧ windingNumber γ a b w' = 0 := by
  obtain ⟨ε₁, hε₁, h_dist⟩ := exists_ball_dist_curve_lower_bound hγ_cont hoff
  -- The off-curve set is open: it is the complement of the compact curve image.
  have hSopen : IsOpen {z : ℂ | ∀ t ∈ uIcc a b, γ t ≠ z} := by
    have hset : {z : ℂ | ∀ t ∈ uIcc a b, γ t ≠ z} = (γ '' uIcc a b)ᶜ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, not_exists, not_and, ne_eq]
    rw [hset]
    exact (isCompact_uIcc.image_of_continuousOn hγ_cont).isClosed.isOpen_compl
  -- The winding number is locally constant off the curve, so it is `0` on a subtype-open set
  -- around `w`; push that set forward along the open inclusion to a `ℂ`-ball.
  have hlc := isLocallyConstant_windingNumber_of_closed hclosed hP hγ_cont hγ_diff hderiv_int
  obtain ⟨V, hV_open, hwV, hV_const⟩ := hlc.exists_open ⟨w, hoff⟩
  have hVℂ : IsOpen (Subtype.val '' V) := hSopen.isOpenMap_subtype_val V hV_open
  obtain ⟨ε₂, hε₂, hball₂⟩ := Metric.isOpen_iff.mp hVℂ w ⟨⟨w, hoff⟩, hwV, rfl⟩
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun w' hw' ↦ ⟨fun t ht ↦ ?_, ?_⟩⟩
  · exact sub_ne_zero.mp (norm_pos_iff.mp (lt_of_lt_of_le hε₁
      (h_dist w' (Metric.ball_subset_ball (min_le_left _ _) hw') t ht)))
  · obtain ⟨p, hpV, hpeq⟩ := hball₂ (Metric.ball_subset_ball (min_le_right _ _) hw')
    rw [← hpeq, hV_const p hpV]
    exact hw_zero

/-- **The Dixon function is entire.** For `f` differentiable on the open set `U`, a closed curve `γ`
that is continuous on `uIcc a b`, differentiable off a countable subset, with interval-integrable
derivative, image in `U`, and null-homologous in `U`, the glued function `dixonFunction f U γ a b`
is complex-differentiable on all of `ℂ`. -/
theorem differentiable_dixonFunction (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hγ_cont : ContinuousOn γ (uIcc a b)) (hγU : ∀ t ∈ uIcc a b, γ t ∈ U)
    (hderiv_int : IntervalIntegrable (fun t ↦ deriv γ t) volume a b) (hclosed : γ a = γ b)
    (hP : P.Countable) (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (h_null : IsNullHomologous γ a b U) :
    Differentiable ℂ (dixonFunction f U γ a b) := by
  intro w
  by_cases hw : w ∈ U
  · refine ((differentiableOn_dixonH1 hU hf hγ_cont hγU hderiv_int).differentiableAt
      (hU.mem_nhds hw)).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hw] with w' hw' using dixonFunction_eq_dixonH1 hw'
  · have hoff : ∀ t ∈ uIcc a b, γ t ≠ w := fun t ht heq ↦ hw (heq ▸ hγU t ht)
    have hw_zero : windingNumber γ a b w = 0 := (isNullHomologous_iff.mp h_null) w hw
    obtain ⟨ε, hε_pos, h_ball⟩ :=
      exists_ball_windingNumber_zero hclosed hP hγ_cont hγ_diff hderiv_int hoff hw_zero
    refine (differentiableAt_dixonH2 hγ_cont hoff
      (cauchy_integrand_intervalIntegrable hf hγ_cont hγU hderiv_int hoff)).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds w hε_pos] with w' hw'
    obtain ⟨hoff', hwz'⟩ := h_ball w' hw'
    by_cases hw'U : w' ∈ U
    · rw [dixonFunction_eq_dixonH1 hw'U, dixonH1_eq_dixonH2_sub_windingNumber_mul_f hγ_cont hoff'
        (cauchy_integrand_intervalIntegrable hf hγ_cont hγU hderiv_int hoff')
        (base_integrand_intervalIntegrable hγ_cont hderiv_int hoff'), hwz']
      ring
    · rw [dixonFunction_eq_dixonH2 hw'U]

end

end TauCeti.Contour
