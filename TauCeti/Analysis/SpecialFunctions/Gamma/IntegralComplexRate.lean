/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The Gamma integral with a complex rate

For `Re s > 0` and `Re z > 0`,
`∫₀^∞ t^{s-1} e^{-zt} dt = Γ(s) z^{-s}` with the principal power `z^{-s}`.

Mathlib's `Complex.integral_cpow_mul_exp_neg_mul_Ioi` is the case of a positive real rate. Both
sides are holomorphic in `z` on the right half-plane: the integral by differentiation under the
integral sign, the right side because the half-plane lies in the slit plane. They agree on the
positive reals, so they agree on the half-plane by the identity theorem.

## Main results

* `Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos`: the Gamma integral with complex rate.
* `Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi` and
  `Complex.differentiableOn_integral_cpow_mul_exp_neg_mul_Ioi`: the integral converges and is
  holomorphic in the rate on the right half-plane.

The proof is adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMFMathlib/Analysis/Asymptotics/WatsonSector.lean`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace Complex

/-- The norm of the integrand `t^{s-1} e^{-wt}` for `t > 0`. -/
private theorem norm_cpow_mul_exp_neg_mul (s w : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (s - 1) * exp (-(w * t))‖ = t ^ (s.re - 1) * Real.exp (-w.re * t) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, norm_exp]
  simp

/-- For `Re s > 0` and `Re w > 0`, `t ↦ t^{s-1} e^{-wt}` is integrable on `(0, ∞)`. -/
theorem integrableOn_cpow_mul_exp_neg_mul_Ioi {s w : ℂ} (hs : 0 < s.re) (hw : 0 < w.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * exp (-(w * t))) (Ioi 0) := by
  have hb := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s.re - 1) (b := w.re)
    (by linarith) one_pos hw
  refine Integrable.mono' hb (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_cpow_mul_exp_neg_mul s w ht, Real.rpow_one]

/-- For `Re s > 0`, the Gamma integral `w ↦ ∫₀^∞ t^{s-1} e^{-wt} dt` is holomorphic in the rate
`w` on the right half-plane. -/
theorem differentiableOn_integral_cpow_mul_exp_neg_mul_Ioi {s : ℂ} (hs : 0 < s.re) :
    DifferentiableOn ℂ (fun w : ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-(w * t)))
      {w | 0 < w.re} := by
  intro w₀ hw₀
  have hw₀' : 0 < w₀.re := hw₀
  -- On the ball of radius `δ = Re w₀ / 2` about `w₀` we have `Re w > δ`, which gives the
  -- integrable bound `t^{Re s} e^{-δt}` for the `w`-derivative `−t · t^{s-1} e^{-wt}`.
  set δ := w₀.re / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hball : Metric.ball w₀ δ ∈ 𝓝 w₀ := Metric.ball_mem_nhds _ hδ0
  have hre : ∀ w ∈ Metric.ball w₀ δ, δ < w.re := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have h1 := abs_re_le_norm (w - w₀)
    rw [sub_re] at h1
    have h2 := (abs_lt.mp (lt_of_le_of_lt h1 hw)).1
    linarith
  have hbint : Integrable (fun t : ℝ => t ^ s.re * Real.exp (-δ * t))
      (volume.restrict (Ioi 0)) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s.re) (b := δ)
      (by linarith) one_pos hδ0
    simp only [Real.rpow_one] at this
    exact this
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0))
    (F := fun w (t : ℝ) => (t : ℂ) ^ (s - 1) * exp (-(w * t)))
    (F' := fun w (t : ℝ) => (t : ℂ) ^ (s - 1) * exp (-(w * t)) * -(t : ℂ))
    (bound := fun t : ℝ => t ^ s.re * Real.exp (-δ * t))
    hball (Eventually.of_forall fun _ => Measurable.aestronglyMeasurable (by fun_prop))
    (integrableOn_cpow_mul_exp_neg_mul_Ioi hs hw₀')
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_ hbint ?_
  · exact h.2.differentiableAt.differentiableWithinAt
  · -- The bound: `‖t^{s-1} e^{-wt} · (−t)‖ = t^{Re s} e^{-(Re w) t} ≤ t^{Re s} e^{-δt}`.
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    have ht' : 0 < t := ht
    rw [norm_mul, norm_cpow_mul_exp_neg_mul s w ht', norm_neg, norm_real,
      Real.norm_of_nonneg ht'.le, mul_right_comm, ← Real.rpow_add_one ht'.ne', sub_add_cancel]
    gcongr
    nlinarith [hre w hw]
  · filter_upwards with t w _
    have := ((hasDerivAt_id w).mul_const (t : ℂ)).neg.cexp.const_mul ((t : ℂ) ^ (s - 1))
    simpa [mul_assoc] using this

/-- The Gamma integral with a complex rate: for `Re s > 0` and `Re z > 0`,
`∫₀^∞ t^{s-1} e^{-zt} dt = Γ(s) z^{-s}`. Mathlib's `Complex.integral_cpow_mul_exp_neg_mul_Ioi`
is the case of a positive real rate. -/
theorem integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-(z * t)) = Gamma s * z ^ (-s) := by
  set U : Set ℂ := {w | 0 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  let I : ℂ → ℂ := fun w => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-(w * t))
  -- Both sides are analytic on the right half-plane `U`.
  have hanI : AnalyticOnNhd ℂ I U :=
    (differentiableOn_integral_cpow_mul_exp_neg_mul_Ioi hs).analyticOnNhd hUo
  have hanR : AnalyticOnNhd ℂ (fun w => Gamma s * w ^ (-s)) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    have hslit : w ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl hw)
    exact ((differentiableAt_id.cpow (differentiableAt_const _) hslit).const_mul
      _).differentiableWithinAt
  -- They agree on the positive reals, by Mathlib's real-rate formula.
  have hreal (r : ℝ) (hr : 0 < r) : I r = Gamma s * (r : ℂ) ^ (-s) := by
    have harg : arg (r : ℂ) ≠ Real.pi := by
      rw [arg_ofReal_of_nonneg hr.le]; exact Real.pi_pos.ne
    simp only [I]
    rw [integral_cpow_mul_exp_neg_mul_Ioi hs hr, one_div, inv_cpow _ _ harg, ← cpow_neg,
      mul_comm]
  -- So they agree frequently near `1`, and hence on `U` by the identity theorem.
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), I w = Gamma s * w ^ (-s) := by
    have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have := (continuous_ofReal.tendsto (1 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℝ)))
        rwa [ofReal_one] at this
      · filter_upwards [self_mem_nhdsWithin] with r hr
        simpa using hr
    apply ht.frequently
    apply Eventually.frequently
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one' ℝ))] with r hr
    exact hreal r hr
  exact hanI.eqOn_of_preconnected_of_frequently_eq hanR (convex_halfSpace_re_gt 0).isPreconnected
    (by simp [hU]) hfreq hz

end Complex
