/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Tricomi
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Basic

/-!
# Tail Gamma integral and variance bound for Tricomi parameter zeros

This file establishes the analytic properties of the real upper tail Gamma integral
`I(a, x) = ∫_x^∞ t^{a - 1} e^{-t} dt` needed to classify the parameter zeros of Tricomi's entire
incomplete Gamma function `γ*(a, x)` for `x > 0` (DLMF §8.13(iii)(b)):

* For all `a ∉ −ℕ` and `x > 0`, `x^a Re γ*(a, x) = 1 - I(a, x) / Γ(a)`
  (`Complex.rpow_mul_re_tricomiIncompleteGamma_eq_one_sub_div_Gamma`).
* Under the substitution `t = x e^s`, `I(a, x) = x^a ∫_0^∞ exp(a s - x e^s) ds`. For `a < 0` and
  `x > 0`, differentiating twice under the integral sign expresses `(log I(·, x))''(a)` as the
  variance of `s ↦ s` under the tilted density `exp(a s - x e^s)` on `(0, ∞)`.
* Monotonicity of the corresponding Mills ratio together with the Chebyshev correlation inequality
  bounds this variance strictly by `(a ^ 2)⁻¹`, giving
  `(log I(·, x))''(a) < (a ^ 2)⁻¹` (`TauCeti.deriv_deriv_log_integral_rpow_sub_one_mul_exp_neg_lt`).

## Main results

* `TauCeti.integrableOn_rpow_sub_one_mul_exp_neg`,
  `TauCeti.integral_rpow_sub_one_mul_exp_neg_pos`,
  `TauCeti.integral_rpow_sub_one_mul_exp_neg_le_exp_neg`,
  `TauCeti.integral_rpow_sub_one_mul_exp_neg_le_rpow` — integrability, positivity, and upper
  bounds for `∫_x^∞ t^{a - 1} e^{-t} dt`.
* `TauCeti.differentiableAt_log_integral_rpow_sub_one_mul_exp_neg`,
  `TauCeti.differentiableAt_deriv_log_integral_rpow_sub_one_mul_exp_neg`,
  `TauCeti.deriv_deriv_log_integral_rpow_sub_one_mul_exp_neg_lt` — smoothness and strict curvature
  bound `(log I(·, x))''(a) < (a ^ 2)⁻¹` for `a < 0` and `x > 0`.
* `Complex.rpow_mul_re_tricomiIncompleteGamma_eq_one_sub_div_Gamma` — the real identity
  `x^a Re γ*(a, x) = 1 - I(a, x) / Γ(a)` for `a ∉ −ℕ` and `x > 0`.

## References

* *NIST Digital Library of Mathematical Functions*, [§8.13(iii)](https://dlmf.nist.gov/8.13#iii).
* F. G. Tricomi, *Asymptotische Eigenschaften der unvollständigen Gammafunktion*,
  Math. Z. 53 (1950), 136–148.
* K. S. Kölbig, *On the zeros of the incomplete gamma function*,
  Math. Comp. 26 (1972), 751–756.
-/

public section

noncomputable section

open Complex Filter Finset MeasureTheory Set
open scoped Nat Topology Interval

namespace TauCeti

/-! ### Integrability, positivity, and elementary bounds for the tail Gamma integral -/

private def tailGamma (a x : ℝ) : ℝ := ∫ t in Ioi x, t ^ (a - 1) * Real.exp (-t)
private def expLaplaceWeight (a x s : ℝ) : ℝ := Real.exp (a * s - x * Real.exp s)
private def expLaplace (a x : ℝ) : ℝ := ∫ s in Ioi (0 : ℝ), expLaplaceWeight a x s
private def expLaplaceDeriv (a x : ℝ) : ℝ := ∫ s in Ioi (0 : ℝ), s * expLaplaceWeight a x s
private def expLaplaceDeriv2 (a x : ℝ) : ℝ := ∫ s in Ioi (0 : ℝ), s ^ 2 * expLaplaceWeight a x s
private def expLaplaceTail (a x s : ℝ) : ℝ := ∫ t in Ioi s, expLaplaceWeight a x t
private def expLaplaceMills (a x s : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), Real.exp (a * u - x * Real.exp s * (Real.exp u - 1))

private theorem expLaplaceWeight_pos (a x s : ℝ) : 0 < expLaplaceWeight a x s :=
  Real.exp_pos _

/-- For every real `a` and `x > 0`, the integrand `t ↦ t^{a - 1} e^{-t}` is integrable on
`(x, ∞)`. -/
theorem integrableOn_rpow_sub_one_mul_exp_neg (a : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-t)) (Ioi x) := by
  rcases le_or_gt a 1 with ha | ha
  · have hexp : IntegrableOn (fun t : ℝ => x ^ (a - 1) * Real.exp (-t)) (Ioi x) :=
      IntegrableOn.congr_fun
        ((integrableOn_exp_mul_Ioi (a := -1) (by norm_num) x).const_mul (x ^ (a - 1)))
        (fun _ _ => by simp) measurableSet_Ioi
    refine hexp.mono' (ContinuousOn.aestronglyMeasurable
      (ContinuousOn.mul (fun t ht => (Real.continuousAt_rpow_const t (a - 1)
        (Or.inl (hx.trans ht).ne')).continuousWithinAt)
        (Real.continuous_exp.comp continuous_neg).continuousOn) measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (hx.trans ht).le _) (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hx ht.le (by linarith)) (Real.exp_pos _).le
  · have hG := (Real.GammaIntegral_convergent (s := a) (by linarith)).mono_set
      (Ioi_subset_Ioi hx.le)
    exact IntegrableOn.congr_fun hG (fun t _ => mul_comm _ _) measurableSet_Ioi

/-- For every real `a` and `x > 0`, the tail Gamma integral `∫_x^∞ t^{a - 1} e^{-t} dt` is
strictly positive. -/
theorem integral_rpow_sub_one_mul_exp_neg_pos (a : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < ∫ t in Ioi x, t ^ (a - 1) * Real.exp (-t) := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ (integrableOn_rpow_sub_one_mul_exp_neg a hx)]
  · exact lt_of_lt_of_le (by simp) (measure_mono fun t ht =>
      ⟨(mul_pos (Real.rpow_pos_of_pos (hx.trans ht) _) (Real.exp_pos _)).ne', ht⟩)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg (hx.trans ht).le _) (Real.exp_pos _).le

/-- For `a ≤ 1` and `x ≥ 1`, `∫_x^∞ t^{a - 1} e^{-t} dt ≤ e^{-x}`. -/
theorem integral_rpow_sub_one_mul_exp_neg_le_exp_neg {a x : ℝ} (ha : a ≤ 1) (hx : 1 ≤ x) :
    ∫ t in Ioi x, t ^ (a - 1) * Real.exp (-t) ≤ Real.exp (-x) := by
  have hle : ∫ t in Ioi x, t ^ (a - 1) * Real.exp (-t) ≤ ∫ t in Ioi x, Real.exp (-t) :=
    setIntegral_mono_on (integrableOn_rpow_sub_one_mul_exp_neg a (zero_lt_one.trans_le hx))
      (IntegrableOn.congr_fun (integrableOn_exp_mul_Ioi (a := -1) (by norm_num) x)
        (fun _ _ => by simp) measurableSet_Ioi) measurableSet_Ioi fun t ht => by
      simpa using mul_le_mul_of_nonneg_right
        (Real.rpow_le_one_of_one_le_of_nonpos (hx.trans ht.le) (by linarith)) (Real.exp_pos (-t)).le
  have hexp_eq : ∫ t in Ioi x, Real.exp (-t) = Real.exp (-x) := by
    simpa using integral_exp_mul_Ioi (a := -1) (by norm_num) x
  linarith

/-- For `a ≤ 1` and `0 < x₁ ≤ x₂`, shifting the lower endpoint satisfies
`e^{-(x₂ - x₁)} (x₂ / x₁)^{a - 1} ∫_{x₁}^∞ t^{a - 1} e^{-t} dt ≤ ∫_{x₂}^∞ t^{a - 1} e^{-t} dt`. -/
theorem mul_integral_rpow_sub_one_mul_exp_neg_le {a x₁ x₂ : ℝ} (ha : a ≤ 1)
    (hx₁ : 0 < x₁) (hle : x₁ ≤ x₂) :
    Real.exp (-(x₂ - x₁)) * (x₂ / x₁) ^ (a - 1) *
      (∫ t in Ioi x₁, t ^ (a - 1) * Real.exp (-t)) ≤
      ∫ t in Ioi x₂, t ^ (a - 1) * Real.exp (-t) := by
  have hx₂ : 0 < x₂ := hx₁.trans_le hle
  let δ : ℝ := x₂ - x₁
  have himg : (fun u : ℝ => u + δ) '' Ioi x₁ = Ioi x₂ := by
    ext t; simp only [mem_image, Set.mem_Ioi]
    exact ⟨fun ⟨u, hu, h⟩ => by dsimp [δ] at h; linarith,
      fun ht => ⟨t - δ, by dsimp [δ]; linarith, by ring⟩⟩
  have hderiv : ∀ u ∈ Ioi x₁, HasDerivWithinAt (fun u : ℝ => u + δ) 1 (Ioi x₁) u :=
    fun u _ => ((hasDerivAt_id u).add_const δ).hasDerivWithinAt
  have hshift : ∫ t in Ioi x₂, t ^ (a - 1) * Real.exp (-t) =
      ∫ u in Ioi x₁, (u + δ) ^ (a - 1) * Real.exp (-(u + δ)) := by
    rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      hderiv (fun _ _ _ _ h => add_right_cancel h)]
    exact setIntegral_congr_fun measurableSet_Ioi fun _ _ => by simp
  rw [hshift, ← integral_const_mul]
  have hint_rhs : IntegrableOn (fun u : ℝ => (u + δ) ^ (a - 1) * Real.exp (-(u + δ)))
      (Ioi x₁) := by
    have h1 := integrableOn_rpow_sub_one_mul_exp_neg a hx₂
    rw [← himg] at h1
    simpa using (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
      hderiv (fun _ _ _ _ h => add_right_cancel h)
      (fun t : ℝ => t ^ (a - 1) * Real.exp (-t))).mp h1
  refine setIntegral_mono_on ((integrableOn_rpow_sub_one_mul_exp_neg a hx₁).const_mul _) hint_rhs
    measurableSet_Ioi fun u hu => ?_
  have hu_pos : 0 < u := hx₁.trans hu
  have hrat_ge1 : 1 ≤ (u + δ) / u := (one_le_div hu_pos).mpr (by dsimp [δ]; linarith)
  have hrat_le : (u + δ) / u ≤ x₂ / x₁ := by
    rw [div_le_div_iff₀ hu_pos hx₁]; dsimp [δ]; nlinarith [Set.mem_Ioi.mp hu]
  have hpow : (x₂ / x₁) ^ (a - 1) ≤ ((u + δ) / u) ^ (a - 1) :=
    Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hrat_ge1) hrat_le (by linarith)
  have hpow_u : (x₂ / x₁) ^ (a - 1) * u ^ (a - 1) ≤ (u + δ) ^ (a - 1) := by
    have hdiv_rpow : (u + δ) ^ (a - 1) = ((u + δ) / u) ^ (a - 1) * u ^ (a - 1) := by
      rw [Real.div_rpow (by dsimp [δ]; linarith) hu_pos.le,
        div_mul_cancel₀ _ (Real.rpow_pos_of_pos hu_pos _).ne']
    rw [hdiv_rpow]
    exact mul_le_mul_of_nonneg_right hpow (Real.rpow_pos_of_pos hu_pos _).le
  have hexp : Real.exp (-(u + δ)) = Real.exp (-δ) * Real.exp (-u) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]
  calc Real.exp (-δ) * (x₂ / x₁) ^ (a - 1) * (u ^ (a - 1) * Real.exp (-u))
      = Real.exp (-δ) * ((x₂ / x₁) ^ (a - 1) * u ^ (a - 1)) * Real.exp (-u) := by ring
    _ ≤ Real.exp (-δ) * (u + δ) ^ (a - 1) * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow_u (Real.exp_pos _).le) (Real.exp_pos _).le
    _ = (u + δ) ^ (a - 1) * (Real.exp (-δ) * Real.exp (-u)) := by ring

private theorem hasDerivAt_tailGamma (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (tailGamma a) (-(x ^ (a - 1) * Real.exp (-x))) x := by
  let x₀ : ℝ := x / 2
  have hx₀ : 0 < x₀ := half_pos hx
  have hint := integrableOn_rpow_sub_one_mul_exp_neg a hx₀
  have hcont : ContinuousOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-t)) (Ioi x₀) :=
    ContinuousOn.mul (fun t ht => (Real.continuousAt_rpow_const t (a - 1)
      (Or.inl (hx₀.trans ht).ne')).continuousWithinAt)
      (Real.continuous_exp.comp continuous_neg).continuousOn
  have heq : tailGamma a =ᶠ[𝓝 x]
      fun y => tailGamma a x₀ - ∫ t in x₀..y, t ^ (a - 1) * Real.exp (-t) := by
    filter_upwards [Ioi_mem_nhds (half_lt_self hx)] with y hy
    have hadd := intervalIntegral.integral_interval_add_Ioi hint
      (integrableOn_rpow_sub_one_mul_exp_neg a (hx₀.trans hy))
    simp only [tailGamma]; linarith
  have hint_seg : IntervalIntegrable (fun t : ℝ => t ^ (a - 1) * Real.exp (-t)) volume x₀ x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (half_lt_self hx).le).mpr
      (hint.mono_set Ioc_subset_Ioi_self)
  have hd : HasDerivAt (fun y => ∫ t in x₀..y, t ^ (a - 1) * Real.exp (-t))
      (x ^ (a - 1) * Real.exp (-x)) x :=
    intervalIntegral.integral_hasDerivAt_right hint_seg
      (hcont.stronglyMeasurableAtFilter isOpen_Ioi x (half_lt_self hx))
      (hcont.continuousAt (isOpen_Ioi.mem_nhds (half_lt_self hx)))
  exact (hd.const_sub (tailGamma a x₀)).congr_of_eventuallyEq heq

private theorem tailGamma_eq_rpow_mul_expLaplace (a : ℝ) {x : ℝ} (hx : 0 < x) :
    tailGamma a x = x ^ a * expLaplace a x := by
  have himg : (fun s : ℝ => x * Real.exp s) '' Ioi (0 : ℝ) = Ioi x := by
    ext t; simp only [mem_image, Set.mem_Ioi]
    refine ⟨fun ⟨s, hs, h⟩ => h ▸ lt_mul_of_one_lt_right hx (Real.one_lt_exp_iff.mpr hs),
      fun ht => ⟨Real.log (t / x), Real.log_pos ((one_lt_div hx).mpr ht), ?_⟩⟩
    rw [Real.exp_log (div_pos (hx.trans ht) hx), mul_div_cancel₀ _ hx.ne']
  rw [tailGamma, ← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun s _ => ((Real.hasDerivAt_exp s).const_mul x).hasDerivWithinAt)
    (fun _ _ _ _ h => Real.exp_injective (mul_left_cancel₀ hx.ne' h)),
    expLaplace, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [expLaplaceWeight, smul_eq_mul, abs_of_pos (mul_pos hx (Real.exp_pos s)),
    Real.mul_rpow hx.le (Real.exp_pos s).le, ← Real.exp_mul, Real.rpow_sub hx, Real.rpow_one,
    Real.exp_sub, Real.exp_neg]
  have hexp : Real.exp s * Real.exp (s * (a - 1)) = Real.exp (a * s) := by
    rw [← Real.exp_add]; congr 1; ring
  calc x * Real.exp s * (x ^ a / x * Real.exp (s * (a - 1)) * (Real.exp (x * Real.exp s))⁻¹)
      = x ^ a * (Real.exp s * Real.exp (s * (a - 1))) / Real.exp (x * Real.exp s) := by
        field_simp [hx.ne', (Real.exp_pos _).ne']
    _ = x ^ a * (Real.exp (a * s) / Real.exp (x * Real.exp s)) := by rw [hexp, mul_div_assoc]

/-! ### Derivatives and variance bound for the tilted exponential-Laplace integral -/

private theorem integrableOn_expLaplaceWeight {a x : ℝ} (ha : a < 0) (hx : 0 ≤ x) (b : ℝ) :
    IntegrableOn (expLaplaceWeight a x) (Ioi b) := by
  refine (integrableOn_exp_mul_Ioi ha b).mono'
    (Continuous.aestronglyMeasurable (by unfold expLaplaceWeight; fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s _
  rw [expLaplaceWeight, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (by linarith [mul_nonneg hx (Real.exp_pos s).le])

/-- For `a ≤ -1` and `x > 0`, `∫_x^∞ t^{a - 1} e^{-t} dt ≤ x ^ a`. -/
theorem integral_rpow_sub_one_mul_exp_neg_le_rpow {a x : ℝ} (ha : a ≤ -1) (hx : 0 < x) :
    ∫ t in Ioi x, t ^ (a - 1) * Real.exp (-t) ≤ x ^ a := by
  have hsub := tailGamma_eq_rpow_mul_expLaplace a hx
  dsimp only [tailGamma] at hsub
  rw [hsub]
  have hexp_le1 : expLaplace a x ≤ 1 := by
    have h1 : expLaplace a x ≤ ∫ s in Ioi (0 : ℝ), Real.exp (-s) := by
      refine setIntegral_mono_on (integrableOn_expLaplaceWeight (by linarith) hx.le 0)
        (by simpa [neg_one_mul] using integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0)
        measurableSet_Ioi fun s hs => Real.exp_le_exp.mpr ?_
      have : 0 ≤ x * Real.exp s := mul_nonneg hx.le (Real.exp_pos s).le
      have : a * s ≤ (-1) * s := mul_le_mul_of_nonneg_right ha hs.le
      linarith
    have hval : ∫ s in Ioi (0 : ℝ), Real.exp (-s) = 1 := by
      simpa using integral_exp_mul_Ioi (a := -1) (by norm_num) 0
    linarith
  simpa using mul_le_mul_of_nonneg_left hexp_le1 (Real.rpow_pos_of_pos hx a).le

private theorem integrableOn_pow_mul_expLaplaceWeight {a x : ℝ} (ha : a < 0) (hx : 0 ≤ x)
    (k : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    IntegrableOn (fun s : ℝ => s ^ k * expLaplaceWeight a x s) (Ioi b) := by
  have hna : 0 < -a := by linarith
  have hscaled : IntegrableOn (fun s : ℝ => Real.exp (-((-a) * s)) * ((-a) * s) ^ ((k : ℝ) + 1 - 1))
      (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff
      (fun t : ℝ => Real.exp (-t) * t ^ ((k : ℝ) + 1 - 1)) 0 hna).mpr
      (by simpa [mul_zero] using Real.GammaIntegral_convergent (s := (k : ℝ) + 1) (by positivity))
  have hdom : IntegrableOn (fun s : ℝ =>
      ((-a) ^ k)⁻¹ * (Real.exp (-((-a) * s)) * ((-a) * s) ^ ((k : ℝ) + 1 - 1))) (Ioi b) :=
    IntegrableOn.mono_set (hscaled.const_mul ((-a) ^ k)⁻¹) (Ioi_subset_Ioi hb)
  refine hdom.mono' (Continuous.aestronglyMeasurable (by unfold expLaplaceWeight; fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 ≤ s := hb.trans hs.le
  rw [expLaplaceWeight, Real.norm_of_nonneg (mul_nonneg (pow_nonneg hs0 _) (Real.exp_pos _).le),
    add_sub_cancel_right, Real.rpow_natCast, mul_pow]
  have hcancel : ((-a) ^ k)⁻¹ * (Real.exp (-((-a) * s)) * ((-a) ^ k * s ^ k)) =
      s ^ k * Real.exp (-((-a) * s)) := by field_simp [(pow_pos hna k).ne']
  rw [hcancel]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith [mul_nonneg hx (Real.exp_pos s).le])) (pow_nonneg hs0 k)

private theorem expLaplace_pos {a x : ℝ} (ha : a < 0) (hx : 0 ≤ x) : 0 < expLaplace a x := by
  rw [expLaplace, setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun s => (expLaplaceWeight_pos a x s).le)
    (integrableOn_expLaplaceWeight ha hx 0)]
  exact lt_of_lt_of_le (by simp) (measure_mono fun s hs => ⟨(expLaplaceWeight_pos a x s).ne', hs⟩)

private theorem hasDerivAt_expLaplace_moment {a x : ℝ} (ha : a < 0) (hx : 0 ≤ x) (k : ℕ) :
    HasDerivAt (fun b : ℝ => ∫ s in Ioi (0 : ℝ), s ^ k * expLaplaceWeight b x s)
      (∫ s in Ioi (0 : ℝ), s ^ (k + 1) * expLaplaceWeight a x s) a := by
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun b s => s ^ k * expLaplaceWeight b x s)
    (F' := fun b s => s ^ (k + 1) * expLaplaceWeight b x s)
    (bound := fun s => s ^ (k + 1) * expLaplaceWeight (a / 2) x s)
    (s := Iio (a / 2)) (x₀ := a) (Iio_mem_nhds (by linarith))
    (Eventually.of_forall fun _ =>
      Continuous.aestronglyMeasurable (by unfold expLaplaceWeight; fun_prop))
    (integrableOn_pow_mul_expLaplaceWeight ha hx k le_rfl)
    (Continuous.aestronglyMeasurable (by unfold expLaplaceWeight; fun_prop))
    ?_ (integrableOn_pow_mul_expLaplaceWeight (by linarith) hx (k + 1) le_rfl) ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht b hb
    simp only [expLaplaceWeight]
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg ht.le _) (Real.exp_pos _).le)]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (pow_nonneg ht.le _)
    linarith [mul_le_mul_of_nonneg_right hb.out.le ht.le]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _ b _
    have hd1 : HasDerivAt (fun c : ℝ => c * t - x * Real.exp t) t b := by
      simpa using ((hasDerivAt_id b).mul_const t).sub_const (x * Real.exp t)
    have hd2 : HasDerivAt (fun c : ℝ => t ^ k * expLaplaceWeight c x t)
        (t ^ k * (Real.exp (b * t - x * Real.exp t) * t)) b := hd1.exp.const_mul (t ^ k)
    convert hd2 using 1
    rw [expLaplaceWeight, pow_succ]; ring

private theorem hasDerivAt_expLaplace {a x : ℝ} (ha : a < 0) (hx : 0 ≤ x) :
    HasDerivAt (fun b : ℝ => expLaplace b x) (expLaplaceDeriv a x) a := by
  simpa [expLaplace, expLaplaceDeriv] using hasDerivAt_expLaplace_moment ha hx 0

private theorem hasDerivAt_expLaplaceDeriv {a x : ℝ} (ha : a < 0) (hx : 0 ≤ x) :
    HasDerivAt (fun b : ℝ => expLaplaceDeriv b x) (expLaplaceDeriv2 a x) a := by
  simpa [expLaplaceDeriv, expLaplaceDeriv2] using hasDerivAt_expLaplace_moment ha hx 1

private theorem hasDerivAt_expLaplaceTail {a x : ℝ} (ha : a < 0) (hx : 0 ≤ x) (s : ℝ) :
    HasDerivAt (expLaplaceTail a x) (-expLaplaceWeight a x s) s := by
  let s₀ : ℝ := s - 1
  have hint := integrableOn_expLaplaceWeight ha hx s₀
  have hcont : Continuous (expLaplaceWeight a x) := by unfold expLaplaceWeight; fun_prop
  have heq : expLaplaceTail a x =ᶠ[𝓝 s]
      fun y => expLaplaceTail a x s₀ - ∫ t in s₀..y, expLaplaceWeight a x t := by
    filter_upwards [Ioi_mem_nhds (by dsimp [s₀]; linarith : s₀ < s)] with y _
    have hadd := intervalIntegral.integral_interval_add_Ioi hint
      (integrableOn_expLaplaceWeight ha hx y)
    simp only [expLaplaceTail]; linarith
  have hd : HasDerivAt (fun y => ∫ t in s₀..y, expLaplaceWeight a x t)
      (expLaplaceWeight a x s) s :=
    intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable s₀ s)
      (hcont.stronglyMeasurableAtFilter volume (𝓝 s)) hcont.continuousAt
  exact (hd.const_sub (expLaplaceTail a x s₀)).congr_of_eventuallyEq heq

private theorem expLaplaceTail_eq_weight_mul_mills (a x s : ℝ) :
    expLaplaceTail a x s = expLaplaceWeight a x s * expLaplaceMills a x s := by
  have himg : (fun u : ℝ => s + u) '' Ioi (0 : ℝ) = Ioi s := by
    ext t; simp only [mem_image, Set.mem_Ioi]
    exact ⟨fun ⟨u, hu, h⟩ => by linarith, fun ht => ⟨t - s, by linarith, by ring⟩⟩
  have hderiv : ∀ u ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun u : ℝ => s + u) 1 (Ioi 0) u :=
    fun u _ => ((hasDerivAt_id u).const_add s).hasDerivWithinAt
  rw [expLaplaceTail, ← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    hderiv (fun _ _ _ _ h => add_left_cancel h), expLaplaceMills, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  simp only [abs_one, one_smul, expLaplaceWeight, ← Real.exp_add]
  congr 1; rw [Real.exp_add]; ring

private theorem integrableOn_expLaplaceMills {a x : ℝ} (ha : a < 0) (hx : 0 ≤ x) (s : ℝ) :
    IntegrableOn (fun u : ℝ => Real.exp (a * u - x * Real.exp s * (Real.exp u - 1)))
      (Ioi (0 : ℝ)) := by
  refine (integrableOn_exp_mul_Ioi ha 0).mono' (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr (by
    linarith [mul_nonneg (mul_nonneg hx (Real.exp_pos s).le)
      (sub_nonneg.mpr (Real.one_le_exp hu.le))])

private theorem expLaplaceMills_pos {a x : ℝ} (ha : a < 0) (hx : 0 ≤ x) (s : ℝ) :
    0 < expLaplaceMills a x s := by
  rw [expLaplaceMills, setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun _ => (Real.exp_pos _).le) (integrableOn_expLaplaceMills ha hx s)]
  exact lt_of_lt_of_le (by simp) (measure_mono fun u hu => ⟨(Real.exp_pos _).ne', hu⟩)

private theorem expLaplaceMills_lt_inv_neg {a x : ℝ} (ha : a < 0) (hx : 0 < x) (s : ℝ) :
    expLaplaceMills a x s < (-a)⁻¹ := by
  have hint_exp := integrableOn_exp_mul_Ioi ha 0
  have hint_m := integrableOn_expLaplaceMills ha hx.le s
  have hdiff_pos : 0 < ∫ u in Ioi (0 : ℝ),
      (Real.exp (a * u) - Real.exp (a * u - x * Real.exp s * (Real.exp u - 1))) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · refine lt_of_lt_of_le (by simp) (measure_mono fun u hu => ⟨(sub_pos.mpr
        (Real.exp_lt_exp.mpr (by
          linarith [mul_pos (mul_pos hx (Real.exp_pos s))
            (sub_pos.mpr (Real.one_lt_exp_iff.mpr hu))]))).ne', hu⟩)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by
        linarith [mul_nonneg (mul_nonneg hx.le (Real.exp_pos s).le)
          (sub_nonneg.mpr (Real.one_le_exp hu.le))]))
    · exact hint_exp.sub hint_m
  rw [integral_sub hint_exp hint_m] at hdiff_pos
  have hexp_val : ∫ u in Ioi (0 : ℝ), Real.exp (a * u) = (-a)⁻¹ := by
    have h := integral_exp_mul_Ioi ha 0; simp only [mul_zero, Real.exp_zero] at h
    rw [h]; field_simp [ha.ne]
  simp only [expLaplaceMills]; linarith

private theorem antitone_expLaplaceMills {a x : ℝ} (ha : a < 0) (hx : 0 ≤ x) :
    Antitone (expLaplaceMills a x) := fun s₁ s₂ hle =>
  setIntegral_mono_on (integrableOn_expLaplaceMills ha hx s₂)
    (integrableOn_expLaplaceMills ha hx s₁) measurableSet_Ioi fun u hu => Real.exp_le_exp.mpr <| by
      linarith [mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) hx)
        (sub_nonneg.mpr (Real.one_le_exp hu.le))]

private theorem expLaplace_moment_eq {a x : ℝ} (ha : a < 0) (hx : 0 < x) {k : ℕ} (hk : 1 ≤ k) :
    ∫ s in Ioi (0 : ℝ), s ^ k * expLaplaceWeight a x s =
      (k : ℝ) * ∫ s in Ioi (0 : ℝ), s ^ (k - 1) * expLaplaceTail a x s := by
  -- Integrate `s ^ k * w(s)` by parts using `(-tail)' = w` and vanishing boundary terms at `0, ∞`.
  have hna_pos : 0 < (-a)⁻¹ := inv_pos.mpr (by linarith)
  have htail_le : ∀ s : ℝ, 0 ≤ expLaplaceTail a x s ∧
      expLaplaceTail a x s ≤ (-a)⁻¹ * expLaplaceWeight a x s := fun s => by
    rw [expLaplaceTail_eq_weight_mul_mills]
    exact ⟨mul_nonneg (expLaplaceWeight_pos a x s).le (expLaplaceMills_pos ha hx.le s).le, by
      rw [mul_comm (-a)⁻¹]
      exact mul_le_mul_of_nonneg_left
        (expLaplaceMills_lt_inv_neg ha hx s).le (expLaplaceWeight_pos a x s).le⟩
  have hcont_t : Continuous (expLaplaceTail a x) :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_expLaplaceTail ha hx.le s).continuousAt
  have hint_tail :
      IntegrableOn (fun s : ℝ => s ^ (k - 1) * expLaplaceTail a x s) (Ioi (0 : ℝ)) := by
    refine ((integrableOn_pow_mul_expLaplaceWeight ha hx.le (k - 1) le_rfl).const_mul (-a)⁻¹).mono'
      ((continuous_pow _).mul hcont_t).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hs.le _) (htail_le s).1), mul_left_comm]
    exact mul_le_mul_of_nonneg_left (htail_le s).2 (pow_nonneg hs.le _)
  have h_zero : Tendsto (fun s : ℝ => s ^ k * (-expLaplaceTail a x s)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun s : ℝ => s ^ k * (-expLaplaceTail a x s)) 0 :=
      (continuous_pow k).continuousAt.mul hcont_t.continuousAt.neg
    have h0 : (0 : ℝ) ^ k * (-expLaplaceTail a x 0) = 0 := by rw [zero_pow (by omega), zero_mul]
    simpa [h0] using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have h_top : Tendsto (fun s : ℝ => s ^ k * (-expLaplaceTail a x s)) atTop (𝓝 0) := by
    have hpow_exp : Tendsto (fun s : ℝ => (-a)⁻¹ * (s ^ k * Real.exp (a * s))) atTop (𝓝 0) := by
      have h1 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
        (tendsto_id.const_mul_atTop (by linarith : 0 < -a))).const_mul ((-a)⁻¹ * ((-a) ^ k)⁻¹)
      rw [mul_zero] at h1
      refine h1.congr fun s => ?_
      dsimp only [Function.comp_def, id]
      rw [mul_pow, neg_mul, neg_neg]; field_simp [(by linarith : -a ≠ 0)]
    refine tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hpow_exp)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    rw [norm_mul, norm_neg, Real.norm_of_nonneg (pow_nonneg hs.le _),
      Real.norm_of_nonneg (htail_le s).1, mul_left_comm]
    have hexp : expLaplaceWeight a x s ≤ Real.exp (a * s) :=
      Real.exp_le_exp.mpr (by linarith [mul_nonneg hx.le (Real.exp_pos s).le])
    exact mul_le_mul_of_nonneg_left
      ((htail_le s).2.trans (mul_le_mul_of_nonneg_left hexp hna_pos.le)) (pow_nonneg hs.le _)
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := fun s : ℝ => s ^ k) (u' := fun s : ℝ => (k : ℝ) * s ^ (k - 1))
    (v := fun s : ℝ => -expLaplaceTail a x s) (v' := expLaplaceWeight a x)
    (fun s _ => hasDerivAt_pow k s)
    (fun s _ => by simpa using (hasDerivAt_expLaplaceTail ha hx.le s).fun_neg)
    (integrableOn_pow_mul_expLaplaceWeight ha hx.le k le_rfl)
    ((hint_tail.const_mul (k : ℝ)).neg.congr (Eventually.of_forall fun s => by
      dsimp only [Pi.neg_apply, Pi.mul_apply]; ring))
    h_zero h_top
  simp only [sub_self, zero_sub] at hibp
  rw [hibp, ← integral_const_mul, ← integral_neg]
  exact setIntegral_congr_fun measurableSet_Ioi fun _ _ => by ring

private theorem integrableOn_weight_mul_mills {a x : ℝ} (ha : a < 0) (hx : 0 < x) :
    IntegrableOn (fun s : ℝ => expLaplaceWeight a x s * expLaplaceMills a x s) (Ioi (0 : ℝ)) := by
  have htail_cont : Continuous (expLaplaceTail a x) :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_expLaplaceTail ha hx.le s).continuousAt
  refine ((integrableOn_expLaplaceWeight ha hx.le 0).const_mul (-a)⁻¹).mono'
    (htail_cont.aestronglyMeasurable.congr
      (Eventually.of_forall fun s => expLaplaceTail_eq_weight_mul_mills a x s)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s _
  rw [Real.norm_of_nonneg
    (mul_nonneg (expLaplaceWeight_pos a x s).le (expLaplaceMills_pos ha hx.le s).le), mul_comm]
  exact mul_le_mul_of_nonneg_right
    (expLaplaceMills_lt_inv_neg ha hx s).le (expLaplaceWeight_pos a x s).le

private theorem expLaplace_mean_bounds {a x : ℝ} (ha : a < 0) (hx : 0 < x) :
    0 < expLaplaceDeriv a x / expLaplace a x ∧
      expLaplaceDeriv a x / expLaplace a x < (-a)⁻¹ := by
  have hZ₀ := expLaplace_pos ha hx.le
  have hZ₁_eq : expLaplaceDeriv a x =
      ∫ s in Ioi (0 : ℝ), expLaplaceWeight a x s * expLaplaceMills a x s := by
    simpa [expLaplaceDeriv, expLaplaceTail_eq_weight_mul_mills] using
      expLaplace_moment_eq ha hx (k := 1) le_rfl
  have hint0 := integrableOn_expLaplaceWeight ha hx.le 0
  have hint_wR := integrableOn_weight_mul_mills ha hx
  refine ⟨div_pos ?_ hZ₀, (div_lt_iff₀ hZ₀).mpr ?_⟩
  · rw [hZ₁_eq, setIntegral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall fun s =>
        mul_nonneg (expLaplaceWeight_pos a x s).le (expLaplaceMills_pos ha hx.le s).le) hint_wR]
    exact lt_of_lt_of_le (by simp) (measure_mono fun s hs =>
      ⟨(mul_pos (expLaplaceWeight_pos a x s) (expLaplaceMills_pos ha hx.le s)).ne', hs⟩)
  · have hdiff_pos : 0 < ∫ s in Ioi (0 : ℝ),
        ((-a)⁻¹ * expLaplaceWeight a x s - expLaplaceWeight a x s * expLaplaceMills a x s) := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae]
      · refine lt_of_lt_of_le (by simp) (measure_mono fun s hs => ⟨(sub_pos.mpr (by
          rw [mul_comm (-a)⁻¹]
          exact mul_lt_mul_of_pos_left
            (expLaplaceMills_lt_inv_neg ha hx s) (expLaplaceWeight_pos a x s))).ne', hs⟩)
      · exact Eventually.of_forall fun s => sub_nonneg.mpr (by
          rw [mul_comm (-a)⁻¹]
          exact mul_le_mul_of_nonneg_left
            (expLaplaceMills_lt_inv_neg ha hx s).le (expLaplaceWeight_pos a x s).le)
      · exact (hint0.const_mul (-a)⁻¹).sub hint_wR
    rw [integral_sub (hint0.const_mul (-a)⁻¹) hint_wR, integral_const_mul] at hdiff_pos
    simp only [expLaplace] at *; linarith

private theorem expLaplace_second_moment_le {a x : ℝ} (ha : a < 0) (hx : 0 < x) :
    expLaplaceDeriv2 a x ≤
      2 * (expLaplaceDeriv a x / expLaplace a x) * expLaplaceDeriv a x := by
  let Z₀ := expLaplace a x
  let Z₁ := expLaplaceDeriv a x
  let μ := Z₁ / Z₀
  have hZ₀ : 0 < Z₀ := expLaplace_pos ha hx.le
  have hZ₁_eq : Z₁ = ∫ s in Ioi (0 : ℝ), expLaplaceWeight a x s * expLaplaceMills a x s := by
    simpa [Z₁, expLaplaceDeriv, expLaplaceTail_eq_weight_mul_mills] using
      expLaplace_moment_eq ha hx (k := 1) le_rfl
  have hZ₂_eq : expLaplaceDeriv2 a x = 2 * ∫ s in Ioi (0 : ℝ),
      s * (expLaplaceWeight a x s * expLaplaceMills a x s) := by
    simpa [expLaplaceDeriv2, expLaplaceTail_eq_weight_mul_mills] using
      expLaplace_moment_eq ha hx (k := 2) (by omega)
  have hint0 := integrableOn_expLaplaceWeight ha hx.le 0
  have hint1 : IntegrableOn (fun s : ℝ => s * expLaplaceWeight a x s) (Ioi (0 : ℝ)) := by
    simpa using integrableOn_pow_mul_expLaplaceWeight ha hx.le 1 le_rfl
  have hint_wR := integrableOn_weight_mul_mills ha hx
  have htail_cont : Continuous (expLaplaceTail a x) :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_expLaplaceTail ha hx.le s).continuousAt
  have hint_swR : IntegrableOn (fun s : ℝ => s * (expLaplaceWeight a x s * expLaplaceMills a x s))
      (Ioi (0 : ℝ)) := by
    refine (hint1.const_mul (-a)⁻¹).mono' ((continuous_id.mul htail_cont).aestronglyMeasurable.congr
      (Eventually.of_forall fun s => by simp [expLaplaceTail_eq_weight_mul_mills])) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [Real.norm_of_nonneg (mul_nonneg hs.le
      (mul_nonneg (expLaplaceWeight_pos a x s).le (expLaplaceMills_pos ha hx.le s).le))]
    calc s * (expLaplaceWeight a x s * expLaplaceMills a x s)
        ≤ s * (expLaplaceWeight a x s * (-a)⁻¹) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (expLaplaceMills_lt_inv_neg ha hx s).le (expLaplaceWeight_pos a x s).le) hs.le
      _ = (-a)⁻¹ * (s * expLaplaceWeight a x s) := by ring
  -- Chebyshev correlation inequality: `(s - μ) (R(s) - R(μ)) ≤ 0` since `R` is antitone.
  have hcheb : ∫ s in Ioi (0 : ℝ),
      ((s * (expLaplaceWeight a x s * expLaplaceMills a x s) -
          μ * (expLaplaceWeight a x s * expLaplaceMills a x s)) -
        expLaplaceMills a x μ * (s * expLaplaceWeight a x s - μ * expLaplaceWeight a x s)) ≤ 0 := by
    refine setIntegral_nonpos measurableSet_Ioi fun s _ => ?_
    have hfac : (s * (expLaplaceWeight a x s * expLaplaceMills a x s) -
          μ * (expLaplaceWeight a x s * expLaplaceMills a x s)) -
        expLaplaceMills a x μ * (s * expLaplaceWeight a x s - μ * expLaplaceWeight a x s) =
        (s - μ) * (expLaplaceMills a x s - expLaplaceMills a x μ) * expLaplaceWeight a x s := by
      ring
    rw [hfac]
    refine mul_nonpos_of_nonpos_of_nonneg ?_ (expLaplaceWeight_pos a x s).le
    rcases le_total s μ with hle | hge
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hle)
        (sub_nonneg.mpr (antitone_expLaplaceMills ha hx.le hle))
    · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hge)
        (sub_nonpos.mpr (antitone_expLaplaceMills ha hx.le hge))
  have hI1 : IntegrableOn (fun s : ℝ => s * (expLaplaceWeight a x s * expLaplaceMills a x s) -
      μ * (expLaplaceWeight a x s * expLaplaceMills a x s)) (Ioi (0 : ℝ)) :=
    hint_swR.sub (hint_wR.const_mul μ)
  have hI2 : IntegrableOn (fun s : ℝ => expLaplaceMills a x μ *
      (s * expLaplaceWeight a x s - μ * expLaplaceWeight a x s)) (Ioi (0 : ℝ)) :=
    (hint1.sub (hint0.const_mul μ)).const_mul _
  rw [integral_sub hI1 hI2, integral_sub hint_swR (hint_wR.const_mul μ), integral_const_mul,
    integral_const_mul, integral_sub hint1 (hint0.const_mul μ), integral_const_mul] at hcheb
  have hcancel : (∫ s in Ioi (0 : ℝ), s * expLaplaceWeight a x s) -
      μ * ∫ s in Ioi (0 : ℝ), expLaplaceWeight a x s = 0 := by
    have hZ₀' : (∫ s in Ioi (0 : ℝ), expLaplaceWeight a x s) ≠ 0 := hZ₀.ne'
    dsimp only [μ, Z₁, Z₀, expLaplace, expLaplaceDeriv]
    rw [div_mul_cancel₀ _ hZ₀', sub_self]
  rw [hcancel, mul_zero, sub_zero, ← hZ₁_eq] at hcheb
  linarith [hZ₂_eq]

private theorem variance_expLaplace_lt {a x : ℝ} (ha : a < 0) (hx : 0 < x) :
    expLaplaceDeriv2 a x / expLaplace a x - (expLaplaceDeriv a x / expLaplace a x) ^ 2 <
      (a ^ 2)⁻¹ := by
  let Z₀ := expLaplace a x
  let Z₁ := expLaplaceDeriv a x
  let μ := Z₁ / Z₀
  have hZ₀ : 0 < Z₀ := expLaplace_pos ha hx.le
  obtain ⟨hμ_pos, hμ_lt⟩ := expLaplace_mean_bounds ha hx
  have hZ₂_le := expLaplace_second_moment_le ha hx
  have hdiv : expLaplaceDeriv2 a x / Z₀ ≤ 2 * μ ^ 2 := by
    rw [div_le_iff₀ hZ₀]
    have hZ₁_eq : Z₁ = μ * Z₀ := by dsimp only [μ]; field_simp [hZ₀.ne']
    have h2 : 2 * μ * Z₁ = 2 * μ ^ 2 * Z₀ := by rw [hZ₁_eq]; ring
    linarith
  have hμ2_lt : μ ^ 2 < (a ^ 2)⁻¹ := by
    simpa [inv_pow, neg_sq] using sq_lt_sq' (by linarith) hμ_lt
  linarith

/-! ### Smoothness and curvature bound for `a ↦ log ∫_x^∞ t^{a - 1} e^{-t} dt` -/

private theorem hasDerivAt_log_tailGamma {a x : ℝ} (ha : a < 0) (hx : 0 < x) :
    HasDerivAt (fun b : ℝ => Real.log (tailGamma b x))
      (Real.log x + expLaplaceDeriv a x / expLaplace a x) a := by
  have heq : (fun b : ℝ => Real.log (tailGamma b x)) =ᶠ[𝓝 a]
      fun b : ℝ => b * Real.log x + Real.log (expLaplace b x) := by
    filter_upwards [isOpen_Iio.mem_nhds ha] with b hb
    rw [tailGamma_eq_rpow_mul_expLaplace b hx,
      Real.log_mul (Real.rpow_pos_of_pos hx b).ne' (expLaplace_pos hb hx.le).ne',
      Real.log_rpow hx]
  have hd1 : HasDerivAt (fun b : ℝ => b * Real.log x) (Real.log x) a := by
    simpa using (hasDerivAt_id a).mul_const (Real.log x)
  have hd2 := (hasDerivAt_expLaplace ha hx.le).log (expLaplace_pos ha hx.le).ne'
  exact (hd1.fun_add hd2).congr_of_eventuallyEq heq

private theorem hasDerivAt_deriv_log_tailGamma {a x : ℝ} (ha : a < 0) (hx : 0 < x) :
    HasDerivAt (deriv fun b : ℝ => Real.log (tailGamma b x))
      (expLaplaceDeriv2 a x / expLaplace a x - (expLaplaceDeriv a x / expLaplace a x) ^ 2) a := by
  have heq : deriv (fun b : ℝ => Real.log (tailGamma b x)) =ᶠ[𝓝 a]
      fun b : ℝ => Real.log x + expLaplaceDeriv b x / expLaplace b x := by
    filter_upwards [isOpen_Iio.mem_nhds ha] with b hb
    exact (hasDerivAt_log_tailGamma hb hx).deriv
  have hZ₀ : expLaplace a x ≠ 0 := (expLaplace_pos ha hx.le).ne'
  have hd_quo := (hasDerivAt_expLaplaceDeriv ha hx.le).fun_div
    (hasDerivAt_expLaplace ha hx.le) hZ₀
  have hquo_eq : (expLaplaceDeriv2 a x * expLaplace a x -
        expLaplaceDeriv a x * expLaplaceDeriv a x) / expLaplace a x ^ 2 =
      expLaplaceDeriv2 a x / expLaplace a x - (expLaplaceDeriv a x / expLaplace a x) ^ 2 := by
    field_simp [hZ₀]
  rw [hquo_eq] at hd_quo
  exact (hd_quo.const_add (Real.log x)).congr_of_eventuallyEq heq

/-- For `a < 0` and `x > 0`, `b ↦ log ∫_x^∞ t^{b - 1} e^{-t} dt` is differentiable at `a`. -/
theorem differentiableAt_log_integral_rpow_sub_one_mul_exp_neg {a x : ℝ} (ha : a < 0) (hx : 0 < x) :
    DifferentiableAt ℝ (fun b : ℝ => Real.log (∫ t in Ioi x, t ^ (b - 1) * Real.exp (-t))) a :=
  (hasDerivAt_log_tailGamma ha hx).differentiableAt

/-- For `a < 0` and `x > 0`, the derivative of `b ↦ log ∫_x^∞ t^{b - 1} e^{-t} dt` is
differentiable at `a`. -/
theorem differentiableAt_deriv_log_integral_rpow_sub_one_mul_exp_neg {a x : ℝ}
    (ha : a < 0) (hx : 0 < x) :
    DifferentiableAt ℝ
      (deriv fun b : ℝ => Real.log (∫ t in Ioi x, t ^ (b - 1) * Real.exp (-t))) a :=
  (hasDerivAt_deriv_log_tailGamma ha hx).differentiableAt

/-- For `a < 0` and `x > 0`, the second derivative of `b ↦ log ∫_x^∞ t^{b - 1} e^{-t} dt` is
strictly bounded by `(a ^ 2)⁻¹`. -/
theorem deriv_deriv_log_integral_rpow_sub_one_mul_exp_neg_lt {a x : ℝ} (ha : a < 0) (hx : 0 < x) :
    deriv (deriv fun b : ℝ => Real.log (∫ t in Ioi x, t ^ (b - 1) * Real.exp (-t))) a <
      (a ^ 2)⁻¹ := by
  have hd := (hasDerivAt_deriv_log_tailGamma ha hx).deriv
  dsimp only [tailGamma] at hd
  rw [hd]
  exact variance_expLaplace_lt ha hx

end TauCeti

/-! ### Identity relating `γ*(a, x)` and the tail Gamma integral for `x > 0` -/

namespace Complex

private theorem rpow_mul_re_tricomi_eq_regularizedGamma {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    x ^ b * (tricomiIncompleteGamma (b : ℂ) (x : ℂ)).re = TauCeti.regularizedGamma b x := by
  have htric := tricomiIncompleteGamma_eq_integral (by simpa using hb : 0 < (b : ℂ).re) (x : ℂ)
  have hint_eq :
      (∫ s in (0 : ℝ)..1, (s : ℂ) ^ ((b : ℂ) - 1) * cexp (-((x : ℂ) * s))) =
        ((∫ s in (0 : ℝ)..1, s ^ (b - 1) * Real.exp (-(x * s)) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hs => ?_)
    rw [uIoc_of_le zero_le_one] at hs
    rw [← ofReal_one, ← ofReal_sub, ← ofReal_cpow hs.1.le, ← ofReal_mul, ← ofReal_neg,
      ← ofReal_exp, ← ofReal_mul]
  have hre : (tricomiIncompleteGamma (b : ℂ) (x : ℂ)).re =
      (Real.Gamma b)⁻¹ * ∫ s in (0 : ℝ)..1, s ^ (b - 1) * Real.exp (-(x * s)) := by
    rw [htric, hint_eq, Gamma_ofReal, ← ofReal_inv, ← ofReal_mul, ofReal_re]
  have hsub : x ^ b * ∫ s in (0 : ℝ)..1, s ^ (b - 1) * Real.exp (-(x * s)) =
      ∫ t in (0 : ℝ)..x, t ^ (b - 1) * Real.exp (-t) := by
    have hcomp := intervalIntegral.integral_comp_mul_left
      (f := fun t : ℝ => t ^ (b - 1) * Real.exp (-t)) (a := 0) (b := 1) hx.ne'
    simp only [mul_zero, mul_one] at hcomp
    rw [eq_inv_smul_iff₀ hx.ne', smul_eq_mul] at hcomp
    rw [← hcomp, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hs => ?_)
    rw [uIoc_of_le zero_le_one] at hs
    rw [Real.mul_rpow hx.le hs.1.le, Real.rpow_sub hx, Real.rpow_one]
    field_simp
  rw [hre, TauCeti.regularizedGamma_eq_div, TauCeti.lowerIncompleteGamma_eq_integral hx.le,
    div_eq_inv_mul, ← mul_assoc, mul_comm (x ^ b), mul_assoc, hsub]

private theorem re_tricomi_step (a y : ℝ) :
    (tricomiIncompleteGamma (a : ℂ) (y : ℂ)).re =
      y * (tricomiIncompleteGamma ((a + 1 : ℝ) : ℂ) (y : ℂ)).re +
        Real.exp (-y) / Real.Gamma (a + 1) := by
  have hstep := congr_arg Complex.re
    (tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one (a : ℂ) (y : ℂ))
  have h1 : ((y : ℂ) * tricomiIncompleteGamma ((a : ℂ) + 1) (y : ℂ)).re =
      y * (tricomiIncompleteGamma ((a + 1 : ℝ) : ℂ) (y : ℂ)).re := by
    rw [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, ofReal_add, ofReal_one]
  have h2 : (cexp (-(y : ℂ)) / Gamma ((a : ℂ) + 1)).re = Real.exp (-y) / Real.Gamma (a + 1) := by
    have hcast : cexp (-(y : ℂ)) / Gamma ((a : ℂ) + 1) =
        ((Real.exp (-y) / Real.Gamma (a + 1) : ℝ) : ℂ) := by
      rw [ofReal_div, ofReal_exp, ofReal_neg, ← Gamma_ofReal]; push_cast; rfl
    rw [hcast, ofReal_re]
  rwa [add_re, h1, h2] at hstep

private theorem rpow_mul_re_tricomi_iterate (m : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    x ^ a * (tricomiIncompleteGamma (a : ℂ) (x : ℂ)).re =
      x ^ (a + m) * (tricomiIncompleteGamma ((a + m : ℝ) : ℂ) (x : ℂ)).re +
        Real.exp (-x) * ∑ k ∈ range m, x ^ (a + k) / Real.Gamma (a + k + 1) := by
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    have hrec := ih (a + 1)
    have ha_shift : a + 1 + (m : ℝ) = a + ((m + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [ha_shift] at hrec
    have hpow : x ^ a * x = x ^ (a + 1) := by rw [Real.rpow_add hx, Real.rpow_one]
    calc x ^ a * (tricomiIncompleteGamma (a : ℂ) (x : ℂ)).re
        = x ^ (a + 1) * (tricomiIncompleteGamma ((a + 1 : ℝ) : ℂ) (x : ℂ)).re +
            Real.exp (-x) * (x ^ a / Real.Gamma (a + 1)) := by
          rw [re_tricomi_step a x, mul_add, ← mul_assoc, hpow]; ring
      _ = x ^ (a + ((m + 1 : ℕ) : ℝ)) *
              (tricomiIncompleteGamma ((a + ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) (x : ℂ)).re +
            Real.exp (-x) * (x ^ a / Real.Gamma (a + 1) +
              ∑ k ∈ range m, x ^ (a + 1 + k) / Real.Gamma (a + 1 + k + 1)) := by rw [hrec]; ring
      _ = x ^ (a + ((m + 1 : ℕ) : ℝ)) *
              (tricomiIncompleteGamma ((a + ((m + 1 : ℕ) : ℝ) : ℝ) : ℂ) (x : ℂ)).re +
            Real.exp (-x) * ∑ k ∈ range (m + 1), x ^ (a + k) / Real.Gamma (a + k + 1) := by
          congr 2; rw [Finset.sum_range_succ']
          simp only [Nat.cast_zero, add_zero, Nat.cast_succ]
          rw [add_comm]; congr 1
          exact Finset.sum_congr rfl fun _ _ => by ring_nf

private theorem hasDerivAt_rpow_mul_re_tricomi_add_tailGamma_div_Gamma
    {a y : ℝ} (ha : a < 0) (ha_ne : ∀ k : ℕ, a ≠ -(k : ℝ)) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => t ^ a * (tricomiIncompleteGamma (a : ℂ) (t : ℂ)).re +
      (∫ s in Ioi t, s ^ (a - 1) * Real.exp (-s)) / Real.Gamma a) 0 y := by
  have hd_tric : HasDerivAt (fun t : ℝ => (tricomiIncompleteGamma (a : ℂ) (t : ℂ)).re)
      (-a * (tricomiIncompleteGamma ((a + 1 : ℝ) : ℂ) (y : ℂ)).re) y := by
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y
      (hasDerivAt_tricomiIncompleteGamma (a : ℂ) (y : ℂ)).comp_ofReal
    have hval : Complex.reCLM (-(a : ℂ) * tricomiIncompleteGamma ((a : ℂ) + 1) (y : ℂ)) =
        -a * (tricomiIncompleteGamma ((a + 1 : ℝ) : ℂ) (y : ℂ)).re := by simp [mul_re]
    simpa [Function.comp_def, hval] using hre
  have hd_pow : HasDerivAt (fun t : ℝ => t ^ a) (a * y ^ (a - 1)) y :=
    Real.hasDerivAt_rpow_const (Or.inl hy.ne')
  have hd_tail : HasDerivAt
      (fun t : ℝ => (∫ s in Ioi t, s ^ (a - 1) * Real.exp (-s)) / Real.Gamma a)
      (-(y ^ (a - 1) * Real.exp (-y)) / Real.Gamma a) y :=
    (TauCeti.hasDerivAt_tailGamma a hy).div_const (Real.Gamma a)
  convert (hd_pow.fun_mul hd_tric).fun_add hd_tail using 1
  have hrec' : (tricomiIncompleteGamma (a : ℂ) (y : ℂ)).re -
      y * (tricomiIncompleteGamma ((a + 1 : ℝ) : ℂ) (y : ℂ)).re =
      Real.exp (-y) / Real.Gamma (a + 1) := by linarith [re_tricomi_step a y]
  have hpow_mul : y ^ a = y ^ (a - 1) * y := by rw [← Real.rpow_add_one hy.ne', sub_add_cancel]
  have hfac : a * y ^ (a - 1) * (tricomiIncompleteGamma (a : ℂ) (y : ℂ)).re +
      y ^ (a - 1) * y * (-a * (tricomiIncompleteGamma ((a + 1 : ℝ) : ℂ) (y : ℂ)).re) =
      a * y ^ (a - 1) * ((tricomiIncompleteGamma (a : ℂ) (y : ℂ)).re -
        y * (tricomiIncompleteGamma ((a + 1 : ℝ) : ℂ) (y : ℂ)).re) := by ring
  rw [hpow_mul, hfac, hrec', Real.Gamma_add_one ha.ne]
  field_simp [ha.ne, Real.Gamma_ne_zero ha_ne]
  ring

private theorem tendsto_rpow_mul_re_tricomi_atTop {a : ℝ} (ha : a < 0) :
    Tendsto (fun y : ℝ => y ^ a * (tricomiIncompleteGamma (a : ℂ) (y : ℂ)).re) atTop (𝓝 1) := by
  let m : ℕ := Nat.floor (-a) + 1
  have hb : 0 < a + (m : ℝ) := by
    have := Nat.lt_floor_add_one (-a); push_cast [m]; linarith
  have hsum0 : Tendsto (fun y : ℝ =>
      Real.exp (-y) * ∑ k ∈ range m, y ^ (a + k) / Real.Gamma (a + k + 1)) atTop (𝓝 0) := by
    have hfn : (fun y : ℝ => Real.exp (-y) * ∑ k ∈ range m,
          y ^ (a + k) / Real.Gamma (a + k + 1)) =
        fun y : ℝ => ∑ k ∈ range m,
          (Real.exp (-y) * y ^ (a + k)) / Real.Gamma (a + k + 1) := by
      ext y; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hfn, ← Finset.sum_const_zero]
    refine tendsto_finsetSum _ fun k hk => ?_
    have hk_lt : a + (k : ℝ) < 1 := by
      have hkm : (k : ℝ) ≤ (Nat.floor (-a) : ℝ) := by
        exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      linarith [Nat.floor_le (by linarith : 0 ≤ -a)]
    have hterm0 : Tendsto (fun y : ℝ => Real.exp (-y) * y ^ (a + k)) atTop (𝓝 0) := by
      have hupper : Tendsto (fun y : ℝ => y * Real.exp (-y)) atTop (𝓝 0) := by
        simpa [Real.exp_neg, div_eq_mul_inv, mul_comm] using
          Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
      refine squeeze_zero' ?_ ?_ hupper
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
        exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hy.le _)
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right
          ((Real.rpow_le_rpow_of_exponent_le hy hk_lt.le).trans_eq (Real.rpow_one y))
          (Real.exp_pos _).le
    simpa using hterm0.div_const (Real.Gamma (a + k + 1))
  have hev : (fun y : ℝ => y ^ a * (tricomiIncompleteGamma (a : ℂ) (y : ℂ)).re) =ᶠ[atTop]
      fun y : ℝ => TauCeti.regularizedGamma (a + (m : ℝ)) y +
        Real.exp (-y) * ∑ k ∈ range m, y ^ (a + k) / Real.Gamma (a + k + 1) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [rpow_mul_re_tricomi_iterate m a hy, rpow_mul_re_tricomi_eq_regularizedGamma hb hy]
  simpa using ((TauCeti.tendsto_regularizedGamma_atTop hb).add hsum0).congr' hev.symm

/-- For every regular real parameter `a ∉ −ℕ` and `x > 0`, Tricomi's function satisfies
`x^a Re γ*(a, x) = 1 - (∫_x^∞ t^{a - 1} e^{-t} dt) / Γ(a)`. -/
theorem rpow_mul_re_tricomiIncompleteGamma_eq_one_sub_div_Gamma {a x : ℝ}
    (ha : ∀ k : ℕ, a ≠ -(k : ℝ)) (hx : 0 < x) :
    x ^ a * (tricomiIncompleteGamma (a : ℂ) (x : ℂ)).re =
      1 - (∫ t in Ioi x, t ^ (a - 1) * Real.exp (-t)) / Real.Gamma a := by
  rcases lt_trichotomy a 0 with ha_neg | rfl | ha_pos
  · let h : ℝ → ℝ := fun y => y ^ a * (tricomiIncompleteGamma (a : ℂ) (y : ℂ)).re +
      (∫ t in Ioi y, t ^ (a - 1) * Real.exp (-t)) / Real.Gamma a
    have hderiv : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt h 0 y := fun y hy =>
      hasDerivAt_rpow_mul_re_tricomi_add_tailGamma_div_Gamma ha_neg ha hy
    have hconst : ∀ y ∈ Ioi (0 : ℝ), h y = h x := fun y hy =>
      isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
        (fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt)
        (fun z hz => (hderiv z hz).deriv) hy hx
    have htend_tail : Tendsto (fun y : ℝ =>
        (∫ t in Ioi y, t ^ (a - 1) * Real.exp (-t)) / Real.Gamma a) atTop (𝓝 0) := by
      have h0 : Tendsto (fun y : ℝ => ∫ t in Ioi y, t ^ (a - 1) * Real.exp (-t)) atTop (𝓝 0) :=
        squeeze_zero'
          (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
              exact (TauCeti.integral_rpow_sub_one_mul_exp_neg_pos a hy).le)
          (by filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
              exact TauCeti.integral_rpow_sub_one_mul_exp_neg_le_exp_neg (by linarith) hy)
          Real.tendsto_exp_neg_atTop_nhds_zero
      simpa using h0.div_const (Real.Gamma a)
    have h1 : h x = 1 := tendsto_nhds_unique
      (tendsto_const_nhds.congr' (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
                                     exact (hconst y hy).symm))
      (by simpa using (tendsto_rpow_mul_re_tricomi_atTop ha_neg).add htend_tail)
    simp only [h] at h1; linarith
  · exact absurd (by simp) (ha 0)
  · rw [rpow_mul_re_tricomi_eq_regularizedGamma ha_pos hx, TauCeti.regularizedGamma_eq_div,
      TauCeti.lowerIncompleteGamma_eq_integral hx.le]
    have hI0 : IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-t)) (Ioi (0 : ℝ)) :=
      IntegrableOn.congr_fun (Real.GammaIntegral_convergent ha_pos)
        (fun _ _ => mul_comm _ _) measurableSet_Ioi
    have hadd := intervalIntegral.integral_interval_add_Ioi hI0
      (TauCeti.integrableOn_rpow_sub_one_mul_exp_neg a hx)
    have hG : ∫ t in Ioi (0 : ℝ), t ^ (a - 1) * Real.exp (-t) = Real.Gamma a := by
      rw [Real.Gamma_eq_integral ha_pos]
      exact setIntegral_congr_fun measurableSet_Ioi fun _ _ => mul_comm _ _
    have hGa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha_pos).ne'
    rw [hG] at hadd
    have hnum : ∫ t in (0 : ℝ)..x, t ^ (a - 1) * Real.exp (-t) =
        Real.Gamma a - ∫ t in Ioi x, t ^ (a - 1) * Real.exp (-t) := by linarith
    rw [hnum, sub_div, div_self hGa]

end Complex
