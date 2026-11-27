/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
import TauCeti.Probability.Distributions.Gaussian.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The solution of the Stein equation for the standard normal law

For a test function `h : ℝ → ℝ` and the standard normal law `γ = gaussianReal 0 1`, the
*Stein equation* is the first-order linear differential equation

  `f′(w) - w f(w) = h(w) - ∫ h dγ`.

Its left side is the Stein operator `f ↦ f′(x) - x f(x)` of the standard normal law, whose
integral against `γ` vanishes (Gaussian integration by parts). Stein's method bounds the distance
from a law `μ` to `γ` by integrating the Stein equation against `μ`, which makes the solution and
its regularity the basic objects of the method.

This file defines the solution

  `f_h(w) = e^{w²/2} ∫_{t ≤ w} (h(t) - ∫ h dγ) e^{-t²/2} dt`

and proves that it solves the Stein equation at every point where `h` is continuous, for every
`h` integrable against `γ`. It also records the equivalent form as an integral over `(w, ∞)`,
which shows that `f_h` vanishes outside every closed ball around `0` that contains the support of
a compactly supported `h` with `∫ h dγ = 0`, so that `f_h` has compact support, and it shows that
every other solution differs from `f_h` by a multiple of `e^{w²/2}`. Finally, `h ↦ f_h` is linear
on functions integrable against `γ` and commutes with the reflection `w ↦ -w` up to sign.

## Main definitions

* `TauCeti.Probability.steinSolution h`: the solution `f_h` of the Stein equation.

## Main statements

* `TauCeti.Probability.hasDerivAt_steinSolution`: if `h` is integrable against `γ` and
  continuous at `w`, then `f_h′(w) = w f_h(w) + h(w) - ∫ h dγ`.
* `TauCeti.Probability.contDiff_steinSolution`: for continuous integrable `h`, `f_h` is `C¹`.
* `TauCeti.Probability.steinSolution_add`, `TauCeti.Probability.steinSolution_sub`,
  `TauCeti.Probability.steinSolution_smul`: linearity of `h ↦ f_h`.
* `TauCeti.Probability.steinSolution_comp_neg`: `f_{h(-·)}(w) = -f_h(-w)`.
* `TauCeti.Probability.steinSolution_eq_neg_integral_Ioi`: the form
  `f_h(w) = -e^{w²/2} ∫_{t > w} (h(t) - ∫ h dγ) e^{-t²/2} dt`.
* `TauCeti.Probability.hasCompactSupport_steinSolution`: if `h` has compact support and
  `∫ h dγ = 0`, then `f_h` has compact support.
* `TauCeti.Probability.forall_hasDerivAt_iff_eq_steinSolution_add`: the solutions of the Stein
  equation on `ℝ` are exactly the functions `f_h + a e^{w²/2}`.

## References

* N. Ross, *Fundamentals of Stein's method*, Probability Surveys 8 (2011), 210–293,
  Lemmas 2.2 and 2.5.
* F. Daly, *Upper bounds for Stein-type operators*, Electronic Journal of Probability 13 (2008),
  566–587, equation (1.1).
-/

public section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

/-- The solution of the Stein equation `f′(w) - w f(w) = h(w) - ∫ h dγ` of the standard normal
law `γ = gaussianReal 0 1`:
`f_h(w) = e^{w²/2} ∫_{t ≤ w} (h(t) - ∫ h dγ) e^{-t²/2} dt`. -/
noncomputable def steinSolution (h : ℝ → ℝ) (w : ℝ) : ℝ :=
  exp (w ^ 2 / 2) * ∫ t in Iic w, (h t - ∫ x, h x ∂gaussianReal 0 1) * exp (-(t ^ 2 / 2))

/-- The defining formula of the Stein solution. -/
theorem steinSolution_def (h : ℝ → ℝ) (w : ℝ) :
    steinSolution h w =
      exp (w ^ 2 / 2) * ∫ t in Iic w, (h t - ∫ x, h x ∂gaussianReal 0 1) * exp (-(t ^ 2 / 2)) :=
  (rfl)

/-- The Stein solution of a constant function vanishes. -/
@[simp]
theorem steinSolution_const (c : ℝ) : steinSolution (fun _ => c) = 0 := by
  ext w
  simp [steinSolution_def]

/-- The Stein solution of the zero function vanishes. -/
@[simp]
theorem steinSolution_zero : steinSolution 0 = 0 :=
  steinSolution_const 0

/-- The derivative of the weight `e^{w²/2}` of the Stein solution. -/
theorem hasDerivAt_exp_sq_div_two (w : ℝ) :
    HasDerivAt (fun u : ℝ => exp (u ^ 2 / 2)) (exp (w ^ 2 / 2) * w) w := by
  convert ((hasDerivAt_pow 2 w).div_const 2).exp using 1
  ring

/-- The derivative of the Gaussian weight `e^{-w²/2}` in the integrand of the Stein solution. -/
theorem hasDerivAt_exp_neg_sq_div_two (w : ℝ) :
    HasDerivAt (fun u : ℝ => exp (-(u ^ 2 / 2))) (exp (-(w ^ 2 / 2)) * -w) w := by
  convert ((hasDerivAt_pow 2 w).div_const 2).fun_neg.exp using 1
  ring

/-- The Gaussian weight `e^{-t²/2}` is `√(2π)` times the standard normal density. -/
private theorem exp_neg_sq_div_two_eq_mul_gaussianPDFReal (t : ℝ) :
    exp (-(t ^ 2 / 2)) = √(2 * π) * gaussianPDFReal 0 1 t := by
  have hπ : √(2 * π) ≠ 0 := by positivity
  rw [gaussianPDFReal_zero_one]
  field_simp

/-- The integrand of the Stein solution is Lebesgue integrable on `ℝ` when `h` is integrable
against the standard normal law. -/
theorem integrable_steinSolution_integrand {h : ℝ → ℝ} (hh : Integrable h (gaussianReal 0 1)) :
    Integrable fun t => (h t - ∫ x, h x ∂gaussianReal 0 1) * exp (-(t ^ 2 / 2)) := by
  have hg : Integrable (fun t => gaussianPDFReal 0 1 t • (h t - ∫ x, h x ∂gaussianReal 0 1)) :=
    (integrable_gaussianReal_iff_integrable_gaussianPDFReal_smul one_ne_zero).1
      (hh.sub (integrable_const _))
  refine (hg.const_mul (√(2 * π))).congr (ae_of_all _ fun t => ?_)
  simp only [smul_eq_mul, exp_neg_sq_div_two_eq_mul_gaussianPDFReal]
  ring

/-- The integrand of the Stein solution has integral `0` over `ℝ` when `h` is integrable against
the standard normal law. -/
theorem integral_steinSolution_integrand {h : ℝ → ℝ} (hh : Integrable h (gaussianReal 0 1)) :
    ∫ t, (h t - ∫ x, h x ∂gaussianReal 0 1) * exp (-(t ^ 2 / 2)) = 0 := by
  have hγ : ∫ t, (h t - ∫ x, h x ∂gaussianReal 0 1) ∂gaussianReal 0 1 = 0 := by
    rw [integral_sub hh (integrable_const _)]
    simp
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero] at hγ
  calc
    ∫ t, (h t - ∫ x, h x ∂gaussianReal 0 1) * exp (-(t ^ 2 / 2)) =
        √(2 * π) * ∫ t, gaussianPDFReal 0 1 t • (h t - ∫ x, h x ∂gaussianReal 0 1) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      simp only [smul_eq_mul, exp_neg_sq_div_two_eq_mul_gaussianPDFReal]
      ring
    _ = 0 := by rw [hγ, mul_zero]

/-- The Stein solution is additive in `h` on functions integrable against the standard normal
law. -/
theorem steinSolution_add {h₁ h₂ : ℝ → ℝ} (hh₁ : Integrable h₁ (gaussianReal 0 1))
    (hh₂ : Integrable h₂ (gaussianReal 0 1)) :
    steinSolution (h₁ + h₂) = steinSolution h₁ + steinSolution h₂ := by
  ext w
  simp only [steinSolution_def, Pi.add_apply]
  rw [integral_add hh₁ hh₂, ← mul_add, ← integral_add
    (integrable_steinSolution_integrand hh₁).integrableOn
    (integrable_steinSolution_integrand hh₂).integrableOn]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  ring

/-- The Stein solution commutes with subtraction of functions integrable against the standard
normal law. -/
theorem steinSolution_sub {h₁ h₂ : ℝ → ℝ} (hh₁ : Integrable h₁ (gaussianReal 0 1))
    (hh₂ : Integrable h₂ (gaussianReal 0 1)) :
    steinSolution (h₁ - h₂) = steinSolution h₁ - steinSolution h₂ := by
  ext w
  simp only [steinSolution_def, Pi.sub_apply]
  rw [integral_sub hh₁ hh₂, ← mul_sub, ← integral_sub
    (integrable_steinSolution_integrand hh₁).integrableOn
    (integrable_steinSolution_integrand hh₂).integrableOn]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  ring

/-- The Stein solution commutes with scalar multiplication. -/
theorem steinSolution_smul (c : ℝ) (h : ℝ → ℝ) :
    steinSolution (c • h) = c • steinSolution h := by
  ext w
  simp only [steinSolution_def, Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul]
  simp_rw [← mul_sub, mul_assoc]
  rw [integral_const_mul]
  ring

/-- The Stein solution as an integral over `(w, ∞)`:
`f_h(w) = -e^{w²/2} ∫_{t > w} (h(t) - ∫ h dγ) e^{-t²/2} dt`. The two forms agree because the
integrand has integral `0` over `ℝ`. -/
theorem steinSolution_eq_neg_integral_Ioi {h : ℝ → ℝ} (hh : Integrable h (gaussianReal 0 1))
    (w : ℝ) :
    steinSolution h w = -(exp (w ^ 2 / 2) *
      ∫ t in Ioi w, (h t - ∫ x, h x ∂gaussianReal 0 1) * exp (-(t ^ 2 / 2))) := by
  have hg := integrable_steinSolution_integrand hh
  have hsum := intervalIntegral.integral_Iic_add_Ioi (b := w) hg.integrableOn hg.integrableOn
  rw [integral_steinSolution_integrand hh, add_eq_zero_iff_eq_neg] at hsum
  rw [steinSolution_def, hsum, mul_neg]

/-- **Reflection.** The Stein solution of `h(-·)` at `w` is `-f_h(-w)`, by the symmetry of the
standard normal law. -/
theorem steinSolution_comp_neg {h : ℝ → ℝ} (hh : Integrable h (gaussianReal 0 1)) (w : ℝ) :
    steinSolution (fun x => h (-x)) w = -steinSolution h (-w) := by
  have hmap : (gaussianReal 0 1).map (fun x => -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  have hc : ∫ x, h (-x) ∂gaussianReal 0 1 = ∫ x, h x ∂gaussianReal 0 1 := by
    rw [← integral_map (φ := fun x => -x) measurable_neg.aemeasurable
      (by rw [hmap]; exact hh.aestronglyMeasurable), hmap]
  have hI := integral_comp_neg_Iic w
    (fun t => (h t - ∫ x, h x ∂gaussianReal 0 1) * exp (-(t ^ 2 / 2)))
  simp only [neg_sq] at hI
  rw [steinSolution_def, steinSolution_eq_neg_integral_Ioi hh, hc, hI, neg_sq, neg_neg]

/-- If `h` has compact support and `∫ h dγ = 0`, then its Stein solution has compact support: it
vanishes outside every closed ball around `0` that contains the support of `h`. -/
theorem hasCompactSupport_steinSolution {h : ℝ → ℝ} (hh : Integrable h (gaussianReal 0 1))
    (hs : HasCompactSupport h) (h0 : ∫ x, h x ∂gaussianReal 0 1 = 0) :
    HasCompactSupport (steinSolution h) := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hs.isCompact.isBounded
  have hzero : ∀ t, r < |t| → h t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have := hr hmem
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      linarith
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) r) fun w hw => ?_
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hw
  rcases le_or_gt w 0 with hw0 | hw0
  · rw [steinSolution_def, setIntegral_eq_zero_of_forall_eq_zero, mul_zero]
    intro t ht
    rw [mem_Iic] at ht
    rw [h0, hzero t (by rw [abs_of_nonpos hw0] at hw; rw [abs_of_nonpos (ht.trans hw0)]; linarith)]
    simp
  · rw [steinSolution_eq_neg_integral_Ioi hh, setIntegral_eq_zero_of_forall_eq_zero, mul_zero,
      neg_zero]
    intro t ht
    rw [mem_Ioi] at ht
    rw [h0, hzero t (by rw [abs_of_pos hw0] at hw; rw [abs_of_pos (hw0.trans ht)]; linarith)]
    simp

/-- **The Stein equation.** If `h` is integrable against the standard normal law `γ` and continuous
at `w`, then the Stein solution `f_h` is differentiable at `w` with
`f_h′(w) = w f_h(w) + h(w) - ∫ h dγ`. -/
theorem hasDerivAt_steinSolution {h : ℝ → ℝ} (hh : Integrable h (gaussianReal 0 1)) {w : ℝ}
    (hw : ContinuousAt h w) :
    HasDerivAt (steinSolution h)
      (w * steinSolution h w + h w - ∫ x, h x ∂gaussianReal 0 1) w := by
  set c := ∫ x, h x ∂gaussianReal 0 1
  set g : ℝ → ℝ := fun t => (h t - c) * exp (-(t ^ 2 / 2)) with hg_def
  have hg : Integrable g := integrable_steinSolution_integrand hh
  -- Split the integral over `(-∞, u]` at `0`, and differentiate the interval integral.
  have hI : (fun u => ∫ t in Iic u, g t) = fun u => (∫ t in Iic 0, g t) + ∫ t in 0..u, g t := by
    ext u
    rw [← intervalIntegral.integral_Iic_sub_Iic hg.integrableOn hg.integrableOn]
    ring
  have hderI : HasDerivAt (fun u => ∫ t in Iic u, g t) (g w) w := by
    rw [hI]
    refine (intervalIntegral.integral_hasDerivAt_right hg.intervalIntegrable
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter ?_).const_add _
    exact (hw.sub continuousAt_const).mul (by fun_prop)
  have hf : steinSolution h = fun u => exp (u ^ 2 / 2) * ∫ t in Iic u, g t := (rfl)
  have hexp : exp (w ^ 2 / 2) * exp (-(w ^ 2 / 2)) = 1 := by
    rw [exp_neg, mul_inv_cancel₀ (exp_ne_zero _)]
  convert (hasDerivAt_exp_sq_div_two w).mul hderI using 1
  rw [hf, hg_def]
  linear_combination (c - h w) * hexp

/-- The derivative of the Stein solution at a point where `h` is continuous. -/
theorem deriv_steinSolution {h : ℝ → ℝ} (hh : Integrable h (gaussianReal 0 1)) {w : ℝ}
    (hw : ContinuousAt h w) :
    deriv (steinSolution h) w = w * steinSolution h w + h w - ∫ x, h x ∂gaussianReal 0 1 :=
  (hasDerivAt_steinSolution hh hw).deriv

/-- For a continuous `h` integrable against the standard normal law, the Stein solution is
differentiable. -/
theorem differentiable_steinSolution {h : ℝ → ℝ} (hh : Integrable h (gaussianReal 0 1))
    (hc : Continuous h) : Differentiable ℝ (steinSolution h) :=
  fun _ => (hasDerivAt_steinSolution hh hc.continuousAt).differentiableAt

/-- For a continuous `h` integrable against the standard normal law, the Stein solution is
continuously differentiable. -/
theorem contDiff_steinSolution {h : ℝ → ℝ} (hh : Integrable h (gaussianReal 0 1))
    (hc : Continuous h) : ContDiff ℝ 1 (steinSolution h) := by
  have hd := differentiable_steinSolution hh hc
  rw [contDiff_one_iff_deriv]
  refine ⟨hd, ?_⟩
  rw [show deriv (steinSolution h) =
      fun w => w * steinSolution h w + h w - ∫ x, h x ∂gaussianReal 0 1 from
    funext fun w => deriv_steinSolution hh hc.continuousAt]
  exact (continuous_id.mul hd.continuous).add hc |>.sub continuous_const

/-- **The solutions of the Stein equation.** For a continuous `h` integrable against the standard
normal law `γ`, a function `g` solves `g′(w) = w g(w) + h(w) - ∫ h dγ` at every `w` if and only if
it is the Stein solution plus a multiple of `e^{w²/2}`. -/
theorem forall_hasDerivAt_iff_eq_steinSolution_add {h : ℝ → ℝ}
    (hh : Integrable h (gaussianReal 0 1)) (hc : Continuous h) {g : ℝ → ℝ} :
    (∀ w, HasDerivAt g (w * g w + h w - ∫ x, h x ∂gaussianReal 0 1) w) ↔
      ∃ a : ℝ, g = fun w => steinSolution h w + a * exp (w ^ 2 / 2) := by
  constructor
  · intro hg
    refine ⟨g 0 - steinSolution h 0, funext fun w => ?_⟩
    -- `(g - f_h)(u) e^{-u²/2}` has derivative `0`, so it is constant.
    have he : ∀ u, HasDerivAt (fun u => (g u - steinSolution h u) * exp (-(u ^ 2 / 2))) 0 u :=
      fun u => by
        convert ((hg u).sub (hasDerivAt_steinSolution hh hc.continuousAt)).mul
          (hasDerivAt_exp_neg_sq_div_two u) using 1
        rw [Pi.sub_apply]
        ring
    have hconst : (g w - steinSolution h w) * exp (-(w ^ 2 / 2)) = g 0 - steinSolution h 0 := by
      have := is_const_of_deriv_eq_zero (fun u => (he u).differentiableAt)
        (fun u => (he u).deriv) w 0
      rwa [zero_pow two_ne_zero, zero_div, neg_zero, exp_zero, mul_one] at this
    have hexp : exp (-(w ^ 2 / 2)) * exp (w ^ 2 / 2) = 1 := by
      rw [exp_neg, inv_mul_cancel₀ (exp_ne_zero _)]
    linear_combination exp (w ^ 2 / 2) * hconst - (g w - steinSolution h w) * hexp
  · rintro ⟨a, rfl⟩ w
    convert (hasDerivAt_steinSolution hh hc.continuousAt).add
      ((hasDerivAt_exp_sq_div_two w).const_mul a) using 1
    ring

end TauCeti.Probability
