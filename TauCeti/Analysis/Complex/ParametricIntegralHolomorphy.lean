/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Complex.Liouville

/-!
# Holomorphic dependence of integrals on parameters

An integral `x ↦ ∫ a, F x a ∂μ` whose integrand is holomorphic in the parameter `x` and locally
bounded by an integrable function of `a` is holomorphic in `x`. No bound on the derivatives of the
integrand is needed: on a disc, the Cauchy estimates bound the derivative by the integrand itself.

## Main results

* `TauCeti.hasDerivAt_integral_of_dominated_of_differentiableOn`: for a complex parameter, the
  integral is differentiable with derivative the integral of the derivatives.
* `TauCeti.analyticOnNhd_integral_of_dominated`: for a parameter in a finite-dimensional complex
  normed space, the integral is analytic.

## Implementation notes

The several-variable statement follows from the one-variable one by Osgood's lemma
`ContinuousOn.analyticAt_of_differentiableAt_update`, with continuity from the dominated
convergence theorem. The integrand need not be jointly measurable or differentiable in the
integration variable, and the bounds may be singular in it, as for Euler's integral at the ends
of `[0, 1]`.

The results are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMFMathlib/Analysis/Complex/ParametricHolomorphy.lean`, with a new proof by Osgood's lemma.
-/

public section

open Filter Function MeasureTheory Metric Set Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Differentiation under the integral sign for a holomorphic integrand.** If `F w a` is
complex differentiable in `w` on an open set `U` for almost every `a`, and bounded there by an
integrable function of `a`, then at every point of `U` the integral `w ↦ ∫ a, F w a ∂μ` has
derivative the integral of the derivatives. -/
theorem hasDerivAt_integral_of_dominated_of_differentiableOn {F : ℂ → α → E} {U : Set ℂ}
    {w₀ : ℂ} {bound : α → ℝ} (hU : IsOpen U) (hw₀ : w₀ ∈ U)
    (hF_meas : ∀ w ∈ U, AEStronglyMeasurable (F w) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ w ∈ U, ‖F w a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, DifferentiableOn ℂ (F · a) U) :
    HasDerivAt (fun w ↦ ∫ a, F w a ∂μ) (∫ a, deriv (F · a) w₀ ∂μ) w₀ := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU w₀ hw₀
  have hr2 : 0 < r / 2 := half_pos hr
  -- Closed discs of radius `r / 2` around points of `ball w₀ (r / 2)` lie in `U`.
  have hsub : ∀ w ∈ ball w₀ (r / 2), closedBall w (r / 2) ⊆ U := fun w hw ζ hζ ↦ by
    rw [mem_ball] at hw
    rw [mem_closedBall] at hζ
    exact hrU (mem_ball.mpr (by linarith [dist_triangle ζ w w₀]))
  -- The derivative at `w₀` is an almost everywhere limit of measurable difference quotients.
  have hF'_meas : AEStronglyMeasurable (fun a ↦ deriv (F · a) w₀) μ := by
    set v : ℕ → ℂ := fun n ↦ w₀ + ((r / 2 / ((n : ℝ) + 1) : ℝ) : ℂ)
    have hpos (n : ℕ) : 0 < r / 2 / ((n : ℝ) + 1) := by positivity
    have hv (n : ℕ) : v n ∈ U := hrU <| by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_of_nonneg (hpos n).le]
      exact (div_le_self hr2.le (by simp)).trans_lt (half_lt_self hr)
    have hvt : Tendsto v atTop (𝓝[≠] w₀) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n ↦ ?_⟩
      · have h : Tendsto (fun n : ℕ ↦ r / 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
          simpa only [mul_zero, mul_one_div] using
            tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (r / 2)
        have h' : Tendsto v atTop (𝓝 (w₀ + ((0 : ℝ) : ℂ))) :=
          tendsto_const_nhds.add ((Complex.continuous_ofReal.tendsto 0).comp h)
        rwa [Complex.ofReal_zero, add_zero] at h'
      · exact fun heq ↦ (hpos n).ne'
          (Complex.ofReal_eq_zero.mp (add_left_cancel (heq.trans (add_zero w₀).symm)))
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n a ↦ slope (F · a) w₀ (v n)) (fun n ↦ ?_) ?_
    · simp only [slope_def_module]
      exact ((hF_meas _ (hv n)).sub (hF_meas w₀ hw₀)).const_smul _
    · filter_upwards [h_diff] with a ha
      exact (hasDerivAt_iff_tendsto_slope.mp
        ((ha w₀ hw₀).differentiableAt (hU.mem_nhds hw₀)).hasDerivAt).comp hvt
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds w₀ hr2)
    (F' := fun w a ↦ deriv (F · a) w) (bound := fun a ↦ bound a / (r / 2))
    (eventually_of_mem (hU.mem_nhds hw₀) hF_meas)
    (bound_integrable.mono' (hF_meas w₀ hw₀) (h_bound.mono fun a ha ↦ ha w₀ hw₀))
    hF'_meas ?_ (bound_integrable.div_const _) ?_).2
  · filter_upwards [h_bound, h_diff] with a hb hd w hw
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr2
      (hd.diffContOnCl_ball (hsub w hw)) fun ζ hζ ↦ hb ζ (hsub w hw (sphere_subset_closedBall hζ))
  · filter_upwards [h_diff] with a hd w hw
    exact (hd.differentiableAt (hU.mem_nhds (hsub w hw (mem_closedBall_self hr2.le)))).hasDerivAt

/-- **Analytic dependence of an integral on parameters.** Let `F x a` be complex differentiable
in `x` on an open subset `s` of a finite-dimensional complex normed space, for almost every `a`,
and let every point of `s` have a neighbourhood on which `F` is bounded by an integrable function
of `a`. Then `x ↦ ∫ a, F x a ∂μ` is analytic on `s`. -/
theorem analyticOnNhd_integral_of_dominated {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {F : V → α → E} {s : Set V} (hs : IsOpen s)
    (hF_meas : ∀ x ∈ s, AEStronglyMeasurable (F x) μ)
    (h_bound : ∀ x ∈ s, ∃ t ∈ 𝓝 x, ∃ bound : α → ℝ, Integrable bound μ ∧
      ∀ᵐ a ∂μ, ∀ y ∈ t, ‖F y a‖ ≤ bound a)
    (h_diff : ∀ᵐ a ∂μ, DifferentiableOn ℂ (F · a) s) :
    AnalyticOnNhd ℂ (fun x ↦ ∫ a, F x a ∂μ) s := by
  by_cases hE : CompleteSpace E; swap
  · simp only [integral_of_not_completeSpace hE]
    exact analyticOnNhd_const
  intro x hx
  obtain ⟨t, ht, bound, hbi, hbt⟩ := h_bound x hx
  -- Transport to `Fin n → ℂ` along a basis, where Osgood's lemma applies.
  let e := (Module.finBasis ℂ V).equivFunL
  set u := e.symm ⁻¹' (interior t ∩ s)
  have hu : IsOpen u := (isOpen_interior.inter hs).preimage e.symm.continuous
  have hus : ∀ y ∈ u, e.symm y ∈ s := fun y hy ↦ hy.2
  have hut : ∀ᵐ a ∂μ, ∀ y ∈ u, ‖F (e.symm y) a‖ ≤ bound a :=
    hbt.mono fun a ha y hy ↦ ha _ (interior_subset hy.1)
  have hud : ∀ᵐ a ∂μ, DifferentiableOn ℂ (fun y ↦ F (e.symm y) a) u :=
    h_diff.mono fun a ha ↦ ha.comp e.symm.differentiableOn fun y hy ↦ hus y hy
  have h : AnalyticAt ℂ (fun y ↦ ∫ a, F (e.symm y) a ∂μ) (e x) := by
    refine ContinuousOn.analyticAt_of_differentiableAt_update ?_
      (hu.mem_nhds (by simpa [u] using ⟨mem_interior_iff_mem_nhds.mpr ht, hx⟩)) ?_
    · exact continuousOn_of_dominated (fun y hy ↦ hF_meas _ (hus y hy))
        (fun y hy ↦ hut.mono fun a ha ↦ ha y hy) hbi (hud.mono fun a ha ↦ ha.continuousOn)
    · intro y hy i
      -- The slice through `y` in coordinate `i` is open and contains `y i`.
      have hcont : Continuous (update y i) := continuous_const.update i continuous_id
      refine (hasDerivAt_integral_of_dominated_of_differentiableOn (hu.preimage hcont)
        (by simpa using hy) (fun w hw ↦ hF_meas _ (hus _ hw))
        (hut.mono fun a ha w hw ↦ ha _ hw) hbi ?_).differentiableAt
      exact hud.mono fun a ha ↦ ha.comp (fun w _ ↦
        (hasFDerivAt_update (𝕜 := ℂ) y w).differentiableAt.differentiableWithinAt) fun w hw ↦ hw
  simpa [Function.comp_def] using h.comp (e.analyticAt x)

end TauCeti
