/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.LoopIntegral
public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic
import TauCeti.Analysis.Calculus.RealCharts
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# A hypergeometric loop based at infinity

The change of variables `v = u / (1 - u)` carries the loop based at `1` in DLMF 15.6.4
to the loop based at infinity in DLMF 15.6.3. The circular part is parametrized by the
image of `u = ρ exp (iθ)`, and its power of `v` uses continuation of the logarithm.
At `θ = π` the image lies at `-ρ / (1 + ρ)` between `-1` and `0`. The continued
argument of `v` there is `π`, and the argument of `1 + v` is zero.

## References

* NIST Digital Library of Mathematical Functions, §15.6, equations 15.6.3 and 15.6.4.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Real Set
open scoped Topology Interval

namespace Complex

private def infinityRay (a b c z : ℂ) (v : ℝ) : ℂ :=
  (v : ℂ) ^ (b - 1) * (1 + (v : ℂ)) ^ (a - c) * (1 + v - z * v) ^ (-a)

private def infinityCircle (a b c z : ℂ) (ρ θ : ℝ) : ℂ :=
  let u : ℂ := ρ * exp (θ * I)
  let v := u / (1 - u)
  exp (((Real.log ρ : ℂ) + θ * I - log (1 - u)) * (b - 1)) *
    (1 + v) ^ (a - c) * (1 + v - z * v) ^ (-a) * (I * u / (1 - u) ^ 2)

/-- The loop based at infinity in DLMF 15.6.3, obtained from the `(0+)` loop by
`v = u / (1 - u)`. The outgoing ray carries the monodromy of `v ^ (b - 1)`. -/
def hypergeometricLoopInfinity (a b c z : ℂ) (ρ : ℝ) : ℂ :=
  (exp (2 * π * I * (b - 1)) - 1) *
    (∫ v : ℝ in Ioi (ρ / (1 - ρ)), infinityRay a b c z v) +
    ∫ θ : ℝ in 0..(2 * π), infinityCircle a b c z ρ θ

/-- The real ray and continued circular piece defining the loop at infinity. -/
theorem hypergeometricLoopInfinity_def (a b c z : ℂ) (ρ : ℝ) :
    hypergeometricLoopInfinity a b c z ρ =
      (exp (2 * π * I * (b - 1)) - 1) *
        (∫ v : ℝ in Ioi (ρ / (1 - ρ)),
          (v : ℂ) ^ (b - 1) * (1 + (v : ℂ)) ^ (a - c) * (1 + v - z * v) ^ (-a)) +
      ∫ θ : ℝ in 0..(2 * π),
        let u : ℂ := ρ * exp (θ * I)
        let v := u / (1 - u)
        exp (((Real.log ρ : ℂ) + θ * I - log (1 - u)) * (b - 1)) *
          (1 + v) ^ (a - c) * (1 + v - z * v) ^ (-a) *
            (I * u / (1 - u) ^ 2) := (rfl)

private theorem transformed_factors (a b c : ℂ) {s q : ℂ} (hs : 0 < s.re)
    (hpow : (q * s⁻¹) ^ (-a) = q ^ (-a) * s⁻¹ ^ (-a)) (l D : ℂ) :
    exp ((l - log s) * (b - 1)) * s⁻¹ ^ (a - c) * (q * s⁻¹) ^ (-a) * (D / s ^ 2) =
      exp (l * (b - 1)) * s ^ (c - b - 1) * q ^ (-a) * D := by
  have hs0 : s ≠ 0 := ne_zero_of_re_pos hs
  have harg := slitPlane_arg_ne_pi (mem_slitPlane_iff.mpr (Or.inl hs))
  have he : exp ((l - log s) * (b - 1)) = exp (l * (b - 1)) * s ^ (-(b - 1)) := by
    rw [cpow_def_of_ne_zero hs0, ← exp_add]
    congr 1
    ring
  have h2 : (s ^ 2)⁻¹ = s ^ (-2 : ℂ) := by rw [cpow_neg]; norm_num
  rw [he, hpow, inv_cpow _ _ harg, inv_cpow _ _ harg,
    div_eq_mul_inv, h2, ← cpow_neg, ← cpow_neg]
  calc
    _ = exp (l * (b - 1)) *
        (s ^ (-(b - 1)) * s ^ (-(a - c)) * s ^ (-(-a)) * s ^ (-2 : ℂ)) * q ^ (-a) * D := by ring
    _ = _ := by
      rw [← cpow_add _ _ hs0, ← cpow_add _ _ hs0, ← cpow_add _ _ hs0]
      have hexponent : -(b - 1) + -(a - c) + -(-a) + (-2 : ℂ) = c - b - 1 := by ring
      rw [hexponent]

private theorem ray_pullback (a b c z : ℂ) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    (((1 - u) ^ 2)⁻¹ : ℝ) • infinityRay a b c z (u / (1 - u)) =
      (u : ℂ) ^ (b - 1) * (1 - (u : ℂ)) ^ (c - b - 1) * (1 - z * u) ^ (-a) := by
  have hs : 0 < 1 - u := sub_pos.mpr hu1
  have hs0 : (1 : ℂ) - u ≠ 0 := by exact_mod_cast hs.ne'
  have h1 : (1 : ℂ) + (u : ℂ) / (1 - u) = ((1 : ℂ) - u)⁻¹ := by
    field_simp; ring
  have hq : (1 : ℂ) + (u : ℂ) / (1 - u) - z * ((u : ℂ) / (1 - u)) =
      (1 - z * u) * ((1 : ℂ) - u)⁻¹ := by field_simp; ring
  have hp : ((u / (1 - u) : ℝ) : ℂ) ^ (b - 1) =
      exp ((log (u : ℂ) - log (1 - (u : ℂ))) * (b - 1)) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (div_pos hu hs).ne'),
      ← ofReal_log (div_pos hu hs).le, Real.log_div hu.ne' hs.ne']
    simp only [ofReal_sub, ofReal_log hu.le, ofReal_log hs.le, ofReal_one]
  have hpow : ((1 - z * u) * ((1 : ℂ) - u)⁻¹) ^ (-a) =
      (1 - z * u) ^ (-a) * ((1 : ℂ) - u)⁻¹ ^ (-a) := by
    simpa only [ofReal_inv, ofReal_sub, ofReal_one] using
      mul_ofReal_cpow (1 - z * u) (inv_nonneg.mpr hs.le) (-a)
  have ht := transformed_factors a b c (s := 1 - (u : ℂ)) (q := 1 - z * u)
    (by simpa using hs) hpow (log (u : ℂ)) 1
  unfold infinityRay
  rw [hp]
  push_cast
  rw [hq, h1, real_smul]
  push_cast
  simpa only [one_div, mul_one, one_mul, cpow_def_of_ne_zero (ofReal_ne_zero.mpr hu.ne'),
    mul_comm, mul_left_comm, mul_assoc] using ht

private theorem circle_pullback (a b c z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hzρ : ‖z‖ * ρ < 1) (θ : ℝ) :
    infinityCircle a b c z ρ θ =
      ((ρ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) *
        (1 - ρ * exp (θ * I)) ^ (c - b - 1) *
          (1 - z * (ρ * exp (θ * I))) ^ (-a) * (I * ρ * exp (θ * I)) := by
  let u : ℂ := ρ * exp (θ * I)
  have hun : ‖u‖ = ρ := by
    simp [u, norm_exp_ofReal_mul_I, Real.norm_of_nonneg hρ.le]
  have hs : 0 < (1 - u).re := by
    have := re_le_norm u
    simp only [sub_re, one_re]
    linarith
  have hq : 0 < (1 - z * u).re := by
    have := re_le_norm (z * u)
    rw [norm_mul, hun] at this
    simp only [sub_re, one_re]
    linarith
  have hs0 : 1 - u ≠ 0 := ne_zero_of_re_pos hs
  have h1 : 1 + u / (1 - u) = (1 - u)⁻¹ := by field_simp; ring
  have h2 : 1 + u / (1 - u) - z * (u / (1 - u)) = (1 - z * u) * (1 - u)⁻¹ := by
    field_simp; ring
  have hi : 0 < ((1 - u)⁻¹).re := by
    rw [inv_re]
    exact div_pos hs (normSq_pos.mpr hs0)
  have ht := transformed_factors a b c hs (TauCeti.mul_cpow_of_re_pos hq hi (-a))
    ((Real.log ρ : ℂ) + θ * I) (I * u)
  have he : exp (((Real.log ρ : ℂ) + θ * I) * (b - 1)) =
      (ρ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1)) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hρ.ne'),
      ← ofReal_log hρ.le, ← exp_add]
    congr 1; ring
  -- Use the local name `u` in the unfolded circular integrand to apply the chart identities.
  change exp (((Real.log ρ : ℂ) + θ * I - log (1 - u)) * (b - 1)) *
    (1 + u / (1 - u)) ^ (a - c) *
      (1 + u / (1 - u) - z * (u / (1 - u))) ^ (-a) * (I * u / (1 - u) ^ 2) = _
  rw [h2, h1]
  simpa only [he, u, mul_assoc] using ht

private def zeroRay (a b c z : ℂ) (u : ℝ) : ℂ :=
  (u : ℂ) ^ (b - 1) * (1 - (u : ℂ)) ^ (c - b - 1) * (1 - z * u) ^ (-a)

private theorem integral_infinityRay (a b c z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    (∫ v : ℝ in Ioi (ρ / (1 - ρ)), infinityRay a b c z v) =
      ∫ u : ℝ in ρ..1, zeroRay a b c z u := by
  rw [intervalIntegral.integral_of_le hρ1.le, integral_Ioc_eq_integral_Ioo,
    ← TauCeti.image_div_one_sub_Ioo hρ1]
  have hd (u : ℝ) (hu : u ∈ Ioo ρ 1) :=
    (TauCeti.hasDerivAt_div_one_sub hu.2.ne).hasDerivWithinAt (s := Ioo ρ 1)
  have hm := (TauCeti.strictMonoOn_div_one_sub (α := ℝ)).monotoneOn.mono
    (Ioo_subset_Iio_self : Ioo ρ 1 ⊆ Iio 1)
  rw [integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Ioo hd hm]
  exact setIntegral_congr_fun measurableSet_Ioo fun u hu => ray_pullback a b c z
    (hρ.trans hu.1) hu.2

/-- On the cut plane, the real tail of the loop at infinity is absolutely integrable for
`re b < re c`, including when `re b` is nonpositive. -/
theorem integrableOn_hypergeometricLoopInfinity_ray (a b c z : ℂ) (hbc : b.re < c.re)
    (hz : 1 - z ∈ slitPlane) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    IntegrableOn (fun v : ℝ =>
      (v : ℂ) ^ (b - 1) * (1 + (v : ℂ)) ^ (a - c) * (1 + v - z * v) ^ (-a))
      (Ioi (ρ / (1 - ρ))) := by
  -- Use the private ray integrand to match the pullback equation.
  change IntegrableOn (infinityRay a b c z) _
  rw [← TauCeti.image_div_one_sub_Ioo hρ1]
  have hd (u : ℝ) (hu : u ∈ Ioo ρ 1) :=
    (TauCeti.hasDerivAt_div_one_sub hu.2.ne).hasDerivWithinAt (s := Ioo ρ 1)
  have hm := (TauCeti.strictMonoOn_div_one_sub (α := ℝ)).monotoneOn.mono
    (Ioo_subset_Iio_self : Ioo ρ 1 ⊆ Iio 1)
  rw [integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn measurableSet_Ioo hd hm]
  apply IntegrableOn.congr_fun
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hρ1.le).mp
      (intervalIntegrable_eulerIntegrand_right a hbc hz hρ hρ1.le))
    (fun u hu => (ray_pullback a b c z (hρ.trans hu.1) hu.2).symm) measurableSet_Ioo

/-- The continued circular piece of the loop at infinity is integrable for every
complex parameter as soon as the contour stays away from the remaining singularities. -/
theorem intervalIntegrable_hypergeometricLoopInfinity_circle (a b c z : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hzρ : ‖z‖ * ρ < 1) :
    IntervalIntegrable (fun θ : ℝ =>
      let u : ℂ := ρ * exp (θ * I)
      let v := u / (1 - u)
      exp (((Real.log ρ : ℂ) + θ * I - log (1 - u)) * (b - 1)) *
        (1 + v) ^ (a - c) * (1 + v - z * v) ^ (-a) * (I * u / (1 - u) ^ 2))
      volume 0 (2 * π) := by
  have hc : Continuous (fun θ : ℝ =>
      ((ρ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) *
        (1 - ρ * exp (θ * I)) ^ (c - b - 1) *
          (1 - z * (ρ * exp (θ * I))) ^ (-a) * (I * ρ * exp (θ * I))) := by
    refine continuous_iff_continuousAt.mpr fun θ => ?_
    have hu : ‖(ρ : ℂ) * exp (θ * I)‖ = ρ := by
      simp [norm_exp_ofReal_mul_I, Real.norm_of_nonneg hρ.le]
    have hs : 1 - (ρ : ℂ) * exp (θ * I) ∈ slitPlane := by
      rw [sub_eq_add_neg]
      apply mem_slitPlane_of_norm_lt_one
      simpa only [norm_neg, hu] using hρ1
    have hq : 1 - z * ((ρ : ℂ) * exp (θ * I)) ∈ slitPlane := by
      rw [sub_eq_add_neg]
      apply mem_slitPlane_of_norm_lt_one
      simpa only [norm_neg, norm_mul, hu] using hzρ
    have he : Continuous (fun t : ℝ => exp (t * I)) := by fun_prop
    have h1 := ContinuousAt.cpow (continuousAt_const.sub (he.continuousAt.const_mul _))
      (continuousAt_const (y := c - b - 1)) hs
    have h2 := ContinuousAt.cpow
      (continuousAt_const.sub ((he.continuousAt.const_mul _).const_mul _))
      (continuousAt_const (y := -a)) hq
    exact (((by fun_prop : ContinuousAt (fun t : ℝ =>
      (ρ : ℂ) ^ (b - 1) * exp (t * I * (b - 1))) θ).mul h1).mul h2).mul
      (by fun_prop)
  have heq : infinityCircle a b c z ρ = (fun θ : ℝ =>
      ((ρ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) *
        (1 - ρ * exp (θ * I)) ^ (c - b - 1) *
          (1 - z * (ρ * exp (θ * I))) ^ (-a) * (I * ρ * exp (θ * I))) :=
    funext (circle_pullback a b c z hρ hρ1 hzρ)
  -- The function equality is stated using the private circular integrand.
  change IntervalIntegrable (infinityCircle a b c z ρ) volume 0 (2 * π)
  rw [heq]
  exact hc.intervalIntegrable _ _

/-- The Möbius substitution `v = u / (1 - u)` identifies the loop based at infinity
with the loop based at `1`. The identity also holds for totalized integrals outside
the convergence region. -/
theorem hypergeometricLoopInfinity_eq_hypergeometricLoopZero (a b c z : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hzρ : ‖z‖ * ρ < 1) :
    hypergeometricLoopInfinity a b c z ρ = hypergeometricLoopZero a b c z ρ := by
  unfold hypergeometricLoopInfinity
  rw [integral_infinityRay a b c z hρ hρ1, hypergeometricLoopZero_def]
  have hc := intervalIntegral.integral_congr (μ := volume) (a := 0) (b := 2 * π)
    (fun θ _ => circle_pullback a b c z hρ hρ1 hzρ θ)
  rw [hc]
  have hb : (∫ u : ℝ in 1..ρ,
      (u : ℂ) ^ (b - 1) * (1 - (u : ℂ)) ^ (c - b - 1) * (1 - z * u) ^ (-a)) =
      -∫ u : ℝ in ρ..1, zeroRay a b c z u := intervalIntegral.integral_symm ρ 1
  rw [hb]
  have hs : (∫ u : ℝ in ρ..1,
      (u : ℂ) ^ (b - 1) * exp (2 * π * I * (b - 1)) *
        (1 - (u : ℂ)) ^ (c - b - 1) * (1 - z * u) ^ (-a)) =
      exp (2 * π * I * (b - 1)) * ∫ u : ℝ in ρ..1, zeroRay a b c z u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    simp only [zeroRay]
    ring
  rw [hs]
  simp only [zeroRay]
  ring

/-- The half-line loop integral is independent of the admissible radius of its preimage circle. -/
theorem hypergeometricLoopInfinity_eq (a b c z : ℂ) (hbc : b.re < c.re)
    (hz : 1 - z ∈ slitPlane) {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₁1 : ρ₁ < 1)
    (hρ₂ : 0 < ρ₂) (hρ₂1 : ρ₂ < 1) (hz₁ : ‖z‖ * ρ₁ < 1) (hz₂ : ‖z‖ * ρ₂ < 1) :
    hypergeometricLoopInfinity a b c z ρ₁ = hypergeometricLoopInfinity a b c z ρ₂ := by
  rw [hypergeometricLoopInfinity_eq_hypergeometricLoopZero a b c z hρ₁ hρ₁1 hz₁,
    hypergeometricLoopInfinity_eq_hypergeometricLoopZero a b c z hρ₂ hρ₂1 hz₂]
  exact hypergeometricLoopZero_eq a b c z hbc hz hρ₁ hρ₁1 hρ₂ hρ₂1 hz₁ hz₂

/-- The half-line loop gives Euler's integral on the cut plane in the Euler convergence
region, with the prefactor of DLMF 15.6.3. -/
theorem eulerIntegral_eq_hypergeometricLoopInfinity (a : ℂ) {b c z : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) (hb_int : ∀ n : ℕ, b ≠ n + 1) (hz : 1 - z ∈ slitPlane) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hzρ : ‖z‖ * ρ < 1) :
    eulerIntegral a b c z =
      exp (-b * π * I) * Gamma (1 - b) / (2 * π * I * Gamma (c - b)) *
        hypergeometricLoopInfinity a b c z ρ := by
  rw [hypergeometricLoopInfinity_eq_hypergeometricLoopZero a b c z hρ hρ1 hzρ]
  exact eulerIntegral_eq_hypergeometricLoopZero a hb hbc hb_int hz hρ hρ1 hzρ

/-- On the open unit disk the half-line loop equals the regularized Gauss series times its
Gamma and phase factors. This form includes positive integral (b), where the loop vanishes. -/
theorem hypergeometricLoopInfinity_eq_mul_regularizedGaussHGFun (a : ℂ) {b c z : ℂ}
    (hbc : b.re < c.re) (hz : ‖z‖ < 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    hypergeometricLoopInfinity a b c z ρ =
      2 * π * I * exp (b * π * I) * Gamma (c - b) / Gamma (1 - b) *
        regularizedGaussHGFun a b c z := by
  have hslit : 1 - z ∈ slitPlane := by
    simpa only [sub_eq_add_neg] using mem_slitPlane_of_norm_lt_one (by rwa [norm_neg] : ‖-z‖ < 1)
  have hzρ : ‖z‖ * ρ < 1 := by nlinarith [norm_nonneg z]
  rw [hypergeometricLoopInfinity_eq_hypergeometricLoopZero a b c z hρ hρ1 hzρ]
  let d := c - b
  have hd : 0 < d.re := by simpa only [d, sub_re, sub_pos] using hbc
  have hc : c = b + d := by simp [d]
  have hloop : AnalyticOnNhd ℂ (fun w : ℂ => hypergeometricLoopZero a w (w + d) z ρ) univ :=
    fun w _ => (analyticOnNhd_hypergeometricLoopZero hd hρ hρ1 (a, w, z) ⟨hslit, hzρ⟩).comp₂
      analyticAt_const (analyticAt_id.prod analyticAt_const)
  have hseries : AnalyticOnNhd ℂ (fun w : ℂ =>
      2 * π * I * exp (w * π * I) * Gamma d / Gamma (1 - w) *
        regularizedGaussHGFun a w (w + d) z) univ := by
    intro w _
    have hG := Complex.differentiable_one_div_Gamma.analyticAt (1 - w)
    simp only [div_eq_mul_inv]
    exact ((by fun_prop : AnalyticAt ℂ
      (fun w : ℂ => 2 * π * I * exp (w * π * I) * Gamma d) w).mul
        (hG.comp (analyticAt_const.sub analyticAt_id))).mul
      (analyticAt_const.regularizedGaussHGFun analyticAt_id
        (analyticAt_id.add analyticAt_const) analyticAt_const hz)
  have heq := hloop.eq_of_eventuallyEq hseries (z₀ := 1) (by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by simp : (0 : ℝ) < (1 : ℂ).re)] with w hw
    have hwd : w.re < (w + d).re := by simpa only [add_re, lt_add_iff_pos_right] using hd
    rw [hypergeometricLoopZero_eq_eulerIntegral a hw hwd hslit hρ hρ1 hzρ,
      ← regularizedGaussHGFun_eq_eulerIntegral a hw hwd hz, add_sub_cancel_left])
  simpa only [hc, add_sub_cancel_left] using congrFun heq b

/-- DLMF 15.6.3 on the open unit disk, with the full parameter range of the half-line loop.
The two infinite rays converge under `b.re < c.re`, which allows nonpositive `b.re`. -/
theorem regularizedGaussHGFun_eq_hypergeometricLoopInfinity (a : ℂ) {b c z : ℂ}
    (hbc : b.re < c.re) (hb_int : ∀ n : ℕ, b ≠ n + 1) (hz : ‖z‖ < 1) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    regularizedGaussHGFun a b c z =
      exp (-b * π * I) * Gamma (1 - b) / (2 * π * I * Gamma (c - b)) *
        hypergeometricLoopInfinity a b c z ρ := by
  have hGamma : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using hbc)
  have hGamma' : Gamma (1 - b) ≠ 0 :=
    Gamma_ne_zero fun n hn => hb_int n (by linear_combination -hn)
  have hexp : exp (-(b * π * I)) * exp (b * π * I) = 1 := by
    rw [← exp_add, neg_add_cancel, exp_zero]
  rw [hypergeometricLoopInfinity_eq_mul_regularizedGaussHGFun a hbc hz hρ hρ1]
  field_simp
  linear_combination regularizedGaussHGFun a b c z * hexp.symm

end Complex
