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
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace Complex

/-- The Gamma integral with a complex rate: for `Re s > 0` and `Re z > 0`,
`∫₀^∞ t^{s-1} e^{-zt} dt = Γ(s) z^{-s}`. Mathlib's `Complex.integral_cpow_mul_exp_neg_mul_Ioi`
is the case of a positive real rate. -/
theorem integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-(z * t)) = Gamma s * z ^ (-s) := by
  set U : Set ℂ := {w | 0 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  let I : ℂ → ℂ := fun w => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * exp (-(w * t))
  have hmeas (w : ℂ) : AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * exp (-(w * t))) (volume.restrict (Ioi 0)) :=
    Measurable.aestronglyMeasurable (by fun_prop)
  have hnorm (w : ℂ) (t : ℝ) (ht : 0 < t) :
      ‖(t : ℂ) ^ (s - 1) * exp (-(w * t))‖ = t ^ (s.re - 1) * Real.exp (-w.re * t) := by
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, norm_exp]
    simp
  have hint (w : ℂ) (hw : 0 < w.re) : Integrable
      (fun t : ℝ => (t : ℂ) ^ (s - 1) * exp (-(w * t))) (volume.restrict (Ioi 0)) := by
    have hb := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s.re - 1) (b := w.re)
      (by linarith) one_pos hw
    refine Integrable.mono' hb (hmeas w) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hnorm w t ht, Real.rpow_one]
  have hdiff : DifferentiableOn ℂ I U := by
    intro w₀ hw₀
    have hw₀' : 0 < w₀.re := hw₀
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
      (F' := fun w (t : ℝ) => (t : ℂ) ^ (s - 1) * (exp (-(w * t)) * -(t : ℂ)))
      (bound := fun t : ℝ => t ^ s.re * Real.exp (-δ * t))
      hball (Eventually.of_forall hmeas) (hint w₀ hw₀')
      (Measurable.aestronglyMeasurable (by fun_prop)) ?_ hbint ?_
    · exact h.2.differentiableAt.differentiableWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
      have ht' : 0 < t := ht
      have hwre := hre w hw
      rw [norm_mul, norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos ht', norm_exp,
        norm_real, Real.norm_of_nonneg ht'.le]
      have e : t ^ (s - 1).re * t = t ^ s.re := by
        rw [sub_re, one_re, Real.rpow_sub_one ht'.ne']
        field_simp
      have hexp : Real.exp (-(w * t)).re ≤ Real.exp (-δ * t) := by
        apply Real.exp_le_exp.mpr
        simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
        nlinarith
      calc t ^ (s - 1).re * (Real.exp (-(w * t)).re * t)
          = t ^ s.re * Real.exp (-(w * t)).re := by rw [← e]; ring
        _ ≤ t ^ s.re * Real.exp (-δ * t) := by gcongr
    · filter_upwards with t w _
      have := ((hasDerivAt_id w).mul_const (t : ℂ)).neg.cexp.const_mul ((t : ℂ) ^ (s - 1))
      simpa using this
  have hanI : AnalyticOnNhd ℂ I U := hdiff.analyticOnNhd hUo
  have hanR : AnalyticOnNhd ℂ (fun w => Gamma s * w ^ (-s)) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    have hslit : w ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl hw)
    exact ((differentiableAt_id.cpow (differentiableAt_const _) hslit).const_mul
      _).differentiableWithinAt
  have hreal (r : ℝ) (hr : 0 < r) : I r = Gamma s * (r : ℂ) ^ (-s) := by
    have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
    have harg : arg (r : ℂ) ≠ Real.pi := by
      rw [arg_ofReal_of_nonneg hr.le]; exact Real.pi_pos.ne
    simp only [I]
    rw [integral_cpow_mul_exp_neg_mul_Ioi hs hr, one_div, inv_cpow _ _ harg, ← cpow_neg,
      mul_comm]
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
