/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Airy.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# The Scorer functions `Hi` and `Gi`

The Scorer function `Hi` is defined by the Laplace-type integral (DLMF 9.12.20)

$$\operatorname{Hi}(z) = \frac{1}{\pi} \int_0^\infty \exp\!\left(-\frac{t^3}{3} + z t\right) dt,$$

which converges absolutely for every complex `z`, and `Gi = Bi − Hi` (DLMF 9.12.11).

Differentiating under the integral sign shows that `Hi` is entire, with the iterated derivatives
given by the moments `π⁻¹ ∫₀^∞ tⁿ exp(−t³/3 + z t) dt`. Since
`(t² − z) exp(−t³/3 + z t) = −∂ₜ exp(−t³/3 + z t)`, the second moment equals `z` times the zeroth
moment plus `1`, which is the inhomogeneous Airy equation `Hi'' = z Hi + 1/π` (DLMF 9.12.1). For a
cube root of unity `ν`, the rotated function `z ↦ ν Hi(ν z)` solves the same equation; with
`ν = e^{∓2πi/3}` this is the `Hi` part of DLMF 9.12.3. The value at the origin is
`Hi(0) = 3^{−2/3} Γ(1/3) / π`.

## Main results

* `TauCeti.scorerHi`, `TauCeti.scorerGi` — the Scorer functions; `TauCeti.Real.scorerHi`,
  `TauCeti.Real.scorerGi` their real restrictions.
* `TauCeti.integrableOn_pow_mul_cexp_neg_cube_div_three_add_mul` — integrability of the moment
  integrands on `(0, ∞)`.
* `TauCeti.iterate_deriv_scorerHi` — the iterated derivatives of `Hi` as moment integrals.
* `TauCeti.differentiable_scorerHi` — `Hi` is entire.
* `TauCeti.scorerHi_ode` — `Hi'' = z Hi + 1/π` (DLMF 9.12.1).
* `TauCeti.scorerHi_rotation_ode` — `z ↦ ν Hi(ν z)` solves the same equation when `ν³ = 1`
  (DLMF 9.12.3).
* `TauCeti.scorerHi_zero` — `Hi(0) = 3^{−2/3} Γ(1/3) / π`.

The proofs are new; the integral definition of `Hi` differs from the series definition of the
lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), whose file
`DLMF/Airy/Scorer/Representations.lean` supplied the rotation argument.

## References

* NIST Digital Library of Mathematical Functions, §9.12, <https://dlmf.nist.gov/9.12>.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Real Topology

namespace TauCeti

/-- The Scorer function `Hi(z) = π⁻¹ ∫₀^∞ exp(−t³/3 + z t) dt` (DLMF 9.12.20). -/
def scorerHi (z : ℂ) : ℂ :=
  (π : ℂ)⁻¹ * ∫ t in Ioi (0 : ℝ), cexp (-(t : ℂ) ^ 3 / 3 + z * t)

/-- The defining integral of `Hi`. -/
theorem scorerHi_def (z : ℂ) :
    scorerHi z = (π : ℂ)⁻¹ * ∫ t in Ioi (0 : ℝ), cexp (-(t : ℂ) ^ 3 / 3 + z * t) := (rfl)

/-- The Scorer function `Gi = Bi − Hi` (DLMF 9.12.11). -/
def scorerGi (z : ℂ) : ℂ := airyBi z - scorerHi z

/-- The defining expression of `Gi`. -/
theorem scorerGi_def (z : ℂ) : scorerGi z = airyBi z - scorerHi z := (rfl)

namespace Real

/-- The real restriction of `Hi`. -/
def scorerHi (x : ℝ) : ℝ := (TauCeti.scorerHi x).re

/-- The defining expression of the real restriction of `Hi`. -/
theorem scorerHi_def (x : ℝ) : scorerHi x = (TauCeti.scorerHi x).re := (rfl)

/-- The real restriction of `Gi`. -/
def scorerGi (x : ℝ) : ℝ := (TauCeti.scorerGi x).re

/-- The defining expression of the real restriction of `Gi`. -/
theorem scorerGi_def (x : ℝ) : scorerGi x = (TauCeti.scorerGi x).re := (rfl)

end Real

/-! ### Moment integrals -/

private theorem norm_pow_mul_cexp_neg_cube_div_three_add_mul {t : ℝ} (ht : 0 < t) (n : ℕ)
    (z : ℂ) :
    ‖(t : ℂ) ^ n * cexp (-(t : ℂ) ^ 3 / 3 + z * t)‖ =
      t ^ (n : ℝ) * Real.exp (z.re * t - 1 / 3 * t ^ (3 : ℝ)) := by
  have hre : (-(t : ℂ) ^ 3 / 3 + z * t).re = z.re * t - 1 / 3 * t ^ (3 : ℝ) := by
    have ht3 : -(t : ℂ) ^ 3 / 3 = ((-t ^ 3 / 3 : ℝ) : ℂ) := by push_cast; ring
    rw [add_re, ht3, ofReal_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero,
      Real.rpow_ofNat]
    ring
  rw [norm_mul, norm_pow, Complex.norm_of_nonneg ht.le, Complex.norm_exp, hre,
    Real.rpow_natCast]

/-- For every natural number `n` and complex `z`, the moment integrand
`t ↦ tⁿ exp(−t³/3 + z t)` is Bochner integrable on `(0, ∞)`. -/
theorem integrableOn_pow_mul_cexp_neg_cube_div_three_add_mul (n : ℕ) (z : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * cexp (-(t : ℂ) ^ 3 / 3 + z * t)) (Ioi 0) := by
  have hmajor := integrableOn_rpow_mul_exp_mul_sub_mul_rpow
    (p := 3) (q := (n : ℝ)) (b := 1 / 3)
    (by norm_num) (by linarith [n.cast_nonneg (α := ℝ)]) (by norm_num) z.re
  refine hmajor.mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  rw [norm_pow_mul_cexp_neg_cube_div_three_add_mul ht]

/-- The integrand `t ↦ exp(−t³/3 + z t)` of `Hi` is Bochner integrable on `(0, ∞)`. -/
theorem integrableOn_cexp_neg_cube_div_three_add_mul (z : ℂ) :
    IntegrableOn (fun t : ℝ => cexp (-(t : ℂ) ^ 3 / 3 + z * t)) (Ioi 0) := by
  simpa only [pow_zero, one_mul] using integrableOn_pow_mul_cexp_neg_cube_div_three_add_mul 0 z

/-- The derivative of `w ↦ ∫₀^∞ tⁿ exp(−t³/3 + w t) dt` is obtained by multiplying the integrand
by `t`. -/
theorem hasDerivAt_integral_pow_mul_cexp_neg_cube_div_three_add_mul (n : ℕ) (z : ℂ) :
    HasDerivAt
      (fun w : ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * cexp (-(t : ℂ) ^ 3 / 3 + w * t))
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (n + 1) * cexp (-(t : ℂ) ^ 3 / 3 + z * t)) z := by
  let bound : ℝ → ℝ := fun t =>
    t ^ ((n + 1 : ℕ) : ℝ) * Real.exp ((‖z‖ + 1) * t - 1 / 3 * t ^ (3 : ℝ))
  have hbound_int : Integrable bound (volume.restrict (Ioi 0)) :=
    integrableOn_rpow_mul_exp_mul_sub_mul_rpow
      (p := 3) (q := ((n + 1 : ℕ) : ℝ)) (b := 1 / 3)
      (by norm_num) (by linarith [(n + 1).cast_nonneg (α := ℝ)]) (by norm_num) (‖z‖ + 1)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := bound)
    (F' := fun w (t : ℝ) => (t : ℂ) ^ (n + 1) * cexp (-(t : ℂ) ^ 3 / 3 + w * t))
    (Metric.ball_mem_nhds z zero_lt_one)
    (.of_forall fun w => (integrableOn_pow_mul_cexp_neg_cube_div_three_add_mul n w).1)
    (integrableOn_pow_mul_cexp_neg_cube_div_three_add_mul n z)
    (integrableOn_pow_mul_cexp_neg_cube_div_three_add_mul (n + 1) z).1
    ?_ hbound_int ?_).2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) w hw
    have hw_re : w.re ≤ ‖z‖ + 1 := by
      have hdist : ‖w - z‖ < 1 := by simpa [dist_eq_norm] using Metric.mem_ball.mp hw
      have hnorm : ‖w‖ ≤ ‖z‖ + 1 := by
        linarith [norm_sub_rev w z, norm_sub_norm_le w z]
      exact (Complex.re_le_norm w).trans hnorm
    rw [norm_pow_mul_cexp_neg_cube_div_three_add_mul ht (n + 1) w]
    dsimp only [bound]
    gcongr
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _ w _
    have hd := (((hasDerivAt_id w).mul_const (t : ℂ)).const_add
      (-(t : ℂ) ^ 3 / 3)).cexp.const_mul ((t : ℂ) ^ n)
    refine hd.congr_deriv ?_
    rw [pow_succ]
    simp only [id]
    ring

/-! ### Derivatives of `Hi` -/

/-- Every iterated derivative of `Hi` is a moment integral:
`Hi⁽ⁿ⁾(z) = π⁻¹ ∫₀^∞ tⁿ exp(−t³/3 + z t) dt`. -/
theorem iterate_deriv_scorerHi (n : ℕ) (z : ℂ) :
    deriv^[n] scorerHi z =
      (π : ℂ)⁻¹ * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * cexp (-(t : ℂ) ^ 3 / 3 + z * t) := by
  induction n generalizing z with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, one_mul, scorerHi_def]
  | succ n ih =>
    rw [Function.iterate_succ_apply', funext ih]
    exact ((hasDerivAt_integral_pow_mul_cexp_neg_cube_div_three_add_mul n z).const_mul
      ((π : ℂ)⁻¹)).deriv

/-- The derivative of `Hi` is `Hi′(z) = π⁻¹ ∫₀^∞ t exp(−t³/3 + z t) dt`. -/
theorem hasDerivAt_scorerHi (z : ℂ) :
    HasDerivAt scorerHi
      ((π : ℂ)⁻¹ * ∫ t in Ioi (0 : ℝ), (t : ℂ) * cexp (-(t : ℂ) ^ 3 / 3 + z * t)) z := by
  simpa only [pow_zero, one_mul, zero_add, pow_one, ← scorerHi_def] using
    (hasDerivAt_integral_pow_mul_cexp_neg_cube_div_three_add_mul 0 z).const_mul ((π : ℂ)⁻¹)

/-- The Scorer function `Hi` is entire. -/
@[fun_prop]
theorem differentiable_scorerHi : Differentiable ℂ scorerHi :=
  fun z => (hasDerivAt_scorerHi z).differentiableAt

/-- The kernel identity `∫₀^∞ (t² − z) exp(−t³/3 + z t) dt = 1`, from
`(t² − z) exp(−t³/3 + z t) = −∂ₜ exp(−t³/3 + z t)`. -/
theorem integral_sq_sub_mul_cexp_neg_cube_div_three_add_mul (z : ℂ) :
    ∫ t in Ioi (0 : ℝ), ((t : ℂ) ^ 2 - z) * cexp (-(t : ℂ) ^ 3 / 3 + z * t) = 1 := by
  let g : ℝ → ℂ := fun t => -cexp (-(t : ℂ) ^ 3 / 3 + z * t)
  have hcont : Continuous g := by fun_prop
  have hderiv : ∀ t ∈ Ioi (0 : ℝ),
      HasDerivAt g (((t : ℂ) ^ 2 - z) * cexp (-(t : ℂ) ^ 3 / 3 + z * t)) t := by
    intro t _
    have harg : HasDerivAt (fun s : ℝ => -(s : ℂ) ^ 3 / 3 + z * s) (-(t : ℂ) ^ 2 + z) t := by
      refine ((((hasDerivAt_pow 3 (t : ℂ)).neg.div_const 3).add
        ((hasDerivAt_id (t : ℂ)).const_mul z)).comp_ofReal).congr_deriv ?_
      push_cast
      ring
    exact harg.cexp.neg.congr_deriv (by ring)
  have hint : IntegrableOn
      (fun t : ℝ => ((t : ℂ) ^ 2 - z) * cexp (-(t : ℂ) ^ 3 / 3 + z * t)) (Ioi 0) := by
    refine ((integrableOn_pow_mul_cexp_neg_cube_div_three_add_mul 2 z).sub
      ((integrableOn_cexp_neg_cube_div_three_add_mul z).const_mul z)).congr_fun
      (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply]
    ring
  have htend : Tendsto g atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hpoly : Tendsto (fun t : ℝ => z.re * t - 1 / 3 * t ^ (3 : ℝ)) atTop atBot := by
      have hsq : Tendsto (fun t : ℝ => z.re - t ^ 2 / 3) atTop atBot := by
        refine tendsto_atBot_add_const_left _ z.re ?_
        exact tendsto_neg_atTop_atBot.comp
          ((tendsto_pow_atTop two_ne_zero).atTop_div_const (by norm_num))
      have h : Tendsto (fun t : ℝ => t * (z.re - t ^ 2 / 3)) atTop atBot :=
        tendsto_id.atTop_mul_atBot₀ hsq
      refine h.congr fun t => ?_
      rw [Real.rpow_ofNat]
      ring
    refine (Real.tendsto_exp_atBot.comp hpoly).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    have h := norm_pow_mul_cexp_neg_cube_div_three_add_mul ht 0 z
    simp only [pow_zero, one_mul, Nat.cast_zero, Real.rpow_zero] at h
    simp only [Function.comp_apply, g, norm_neg, h]
  have hibp := integral_Ioi_of_hasDerivAt_of_tendsto hcont.continuousWithinAt hderiv hint htend
  simpa [g] using hibp

/-- `Hi` solves the inhomogeneous Airy equation `Hi'' = z Hi + 1/π` (DLMF 9.12.1). -/
theorem scorerHi_ode (z : ℂ) : deriv^[2] scorerHi z = z * scorerHi z + (π : ℂ)⁻¹ := by
  have hk := integral_sq_sub_mul_cexp_neg_cube_div_three_add_mul z
  have h2 := integrableOn_pow_mul_cexp_neg_cube_div_three_add_mul 2 z
  have h0 := (integrableOn_cexp_neg_cube_div_three_add_mul z).const_mul z
  have hsplit :
      ∫ t in Ioi (0 : ℝ), ((t : ℂ) ^ 2 - z) * cexp (-(t : ℂ) ^ 3 / 3 + z * t) =
        (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ 2 * cexp (-(t : ℂ) ^ 3 / 3 + z * t)) -
          z * ∫ t in Ioi (0 : ℝ), cexp (-(t : ℂ) ^ 3 / 3 + z * t) := by
    rw [← integral_const_mul, ← integral_sub h2 h0]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  rw [iterate_deriv_scorerHi, scorerHi_def]
  rw [hsplit] at hk
  linear_combination (π : ℂ)⁻¹ * hk

/-- For a cube root of unity `ν`, the rotated function `z ↦ ν Hi(ν z)` solves the inhomogeneous
Airy equation `w'' = z w + 1/π`; with `ν = e^{∓2πi/3}` this is DLMF 9.12.3 for `Hi`. -/
theorem scorerHi_rotation_ode {ν : ℂ} (hν : ν ^ 3 = 1) (z : ℂ) :
    deriv^[2] (fun w => ν * scorerHi (ν * w)) z = z * (ν * scorerHi (ν * z)) + (π : ℂ)⁻¹ := by
  have hd (c : ℂ) (f : ℂ → ℂ) :
      deriv (fun w => c * f (ν * w)) = fun w => c * ν * deriv f (ν * w) := by
    rw [deriv_const_mul_field']
    funext w
    rw [deriv_comp_mul_left, smul_eq_mul, mul_assoc]
  have hode := scorerHi_ode (ν * z)
  rw [Function.iterate_succ_apply', Function.iterate_one] at hode ⊢
  rw [hd ν scorerHi, hd (ν * ν) (deriv scorerHi)]
  beta_reduce
  rw [hode]
  linear_combination (z * ν * scorerHi (ν * z) + (π : ℂ)⁻¹) * hν

/-! ### The value at the origin -/

/-- The value `Hi(0) = 3^{−2/3} Γ(1/3) / π`. -/
theorem scorerHi_zero : scorerHi 0 = (3 : ℂ) ^ (-2 / 3 : ℂ) * Gamma (1 / 3) / π := by
  have hcongr : EqOn (fun t : ℝ => cexp (-(t : ℂ) ^ 3 / 3 + 0 * t))
      (fun t : ℝ => ((t ^ (0 : ℝ) * Real.exp (-(1 / 3) * t ^ (3 : ℝ)) : ℝ) : ℂ)) (Ioi 0) := by
    intro t _
    simp only [Real.rpow_zero, one_mul, Real.rpow_ofNat, zero_mul, add_zero, ofReal_exp]
    push_cast
    ring_nf
  have hreal := _root_.integral_rpow_mul_exp_neg_mul_rpow
    (p := 3) (q := 0) (b := 1 / 3) (by norm_num) (by norm_num) (by norm_num)
  rw [scorerHi_def, setIntegral_congr_fun measurableSet_Ioi hcongr, integral_complex_ofReal,
    hreal]
  have h3 : (1 / 3 : ℝ) ^ (-((0 : ℝ) + 1) / 3) = (3 : ℝ) ^ (1 / 3 : ℝ) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
    norm_num
  have hc : (3 : ℂ) ^ (1 / 3 : ℂ) = (3 : ℂ) ^ (-2 / 3 : ℂ) * 3 := by
    calc (3 : ℂ) ^ (1 / 3 : ℂ) = (3 : ℂ) ^ ((-2 / 3 : ℂ) + 1) := by norm_num
      _ = (3 : ℂ) ^ (-2 / 3 : ℂ) * 3 := by rw [cpow_add _ _ (by norm_num), cpow_one]
  have hΓ : ((Real.Gamma ((0 + 1) / 3) : ℝ) : ℂ) = Gamma (1 / 3) := by
    rw [← Gamma_ofReal]
    norm_num
  rw [h3, ofReal_mul, ofReal_mul, hΓ, ofReal_cpow (by norm_num)]
  push_cast
  rw [hc]
  ring

end TauCeti
