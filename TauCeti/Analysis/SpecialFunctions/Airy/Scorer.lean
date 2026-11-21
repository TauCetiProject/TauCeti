/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Airy.Basic
import Mathlib.MeasureTheory.Integral.Gamma
import TauCeti.Analysis.Calculus.Deriv.Second
import TauCeti.MeasureTheory.Integral.Exp.Cubic

/-!
# The Scorer functions `Hi` and `Gi`

The Scorer function `Hi` is defined by the Laplace-type integral (DLMF 9.12.20)

$$\operatorname{Hi}(z) = \frac{1}{\pi} \int_0^\infty \exp\!\left(-\frac{t^3}{3} + z t\right) dt,$$

which converges absolutely for every complex `z`, and `Gi = Bi − Hi` (DLMF 9.12.11).

The integrand is the cubic-decay kernel of `TauCeti.MeasureTheory.Integral.Exp.Cubic` with
`b = 1/3`. Differentiating under the integral sign shows that `Hi` is entire, with the iterated
derivatives given by the moments `π⁻¹ ∫₀^∞ tⁿ exp(−t³/3 + z t) dt`; at the origin these are Gamma
values, `Hi⁽ⁿ⁾(0) = 3^{(n−2)/3} Γ((n+1)/3) / π`. Since
`(t² − z) exp(−t³/3 + z t) = −∂ₜ exp(−t³/3 + z t)`, the second moment equals `z` times the zeroth
moment plus `1`, which is the inhomogeneous Airy equation `Hi'' = z Hi + 1/π` (DLMF 9.12.1). For a
cube root of unity `ν`, the rotation `f ↦ (z ↦ ν f(ν z))` preserves every equation
`w'' = z w + c`; with `ν = e^{∓2πi/3}` this gives the `Hi` part of DLMF 9.12.3. On the real line
`Hi` is real.

## Main results

* `TauCeti.scorerHi`, `TauCeti.scorerGi` — the Scorer functions; `Real.scorerHi`,
  `Real.scorerGi` their real restrictions, and `TauCeti.scorerHi_ofReal` — `Hi(x)` is the cast
  of `Real.scorerHi x`.
* `TauCeti.integrableOn_pow_mul_cexp_neg_cube_div_three_add_mul` — integrability of the moment
  integrands on `(0, ∞)`.
* `TauCeti.iterate_deriv_scorerHi` — the iterated derivatives of `Hi` as moment integrals.
* `TauCeti.differentiable_scorerHi`, `TauCeti.differentiable_scorerGi` — `Hi` and `Gi` are
  entire.
* `TauCeti.scorerHi_ode` — `Hi'' = z Hi + 1/π` (DLMF 9.12.1).
* `TauCeti.iterate_deriv_two_const_mul_comp_mul_left` — `z ↦ ν f(ν z)` solves `w'' = z w + c`
  when `f` does and `ν³ = 1`; `TauCeti.scorerHi_rotation_ode` is the case of `Hi` (DLMF 9.12.3).
* `TauCeti.iterate_deriv_scorerHi_zero` — `Hi⁽ⁿ⁾(0) = 3^{(n−2)/3} Γ((n+1)/3) / π`, and
  `TauCeti.scorerHi_zero` — `Hi(0) = 3^{−2/3} Γ(1/3) / π`.

The moment, differentiation and kernel-to-equation proofs are adapted from those of
`TauCeti.Analysis.SpecialFunctions.Airy.ProductIntegral` for the integral of `Ai² + Bi²`
(`TauCeti.hasDerivAt_integral_pow_mul_cexp_sub_cube_div_twelve_mul_cpow`,
`TauCeti.iterate_deriv_airyAi_sq_add_airyBi_sq_eq_integral`), now shared through the cubic-decay
kernel. The rotation argument is adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file `DLMF/Airy/Scorer/Representations.lean`, whose
`Hi` is defined by its Maclaurin series rather than by the integral used here.

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

/-- The real restriction of `Hi`. -/
def _root_.Real.scorerHi (x : ℝ) : ℝ := (TauCeti.scorerHi x).re

/-- The defining expression of the real restriction of `Hi`. -/
theorem _root_.Real.scorerHi_def (x : ℝ) : Real.scorerHi x = (TauCeti.scorerHi x).re := (rfl)

/-- The real restriction of `Gi`. -/
def _root_.Real.scorerGi (x : ℝ) : ℝ := (TauCeti.scorerGi x).re

/-- The defining expression of the real restriction of `Gi`. -/
theorem _root_.Real.scorerGi_def (x : ℝ) : Real.scorerGi x = (TauCeti.scorerGi x).re := (rfl)

/-- On the real line `Hi` is real: `Hi(x)` is the cast of its real restriction. -/
@[simp]
theorem scorerHi_ofReal (x : ℝ) : scorerHi x = Real.scorerHi x := by
  -- `Hi(x)` is the cast of the real integral `π⁻¹ ∫₀^∞ exp(−t³/3 + x t) dt`.
  have h : scorerHi x = ((π⁻¹ * ∫ t in Ioi (0 : ℝ), Real.exp (-t ^ 3 / 3 + x * t) : ℝ) : ℂ) := by
    rw [scorerHi_def, ofReal_mul, ← integral_complex_ofReal, ofReal_inv]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    push_cast
    ring_nf
  rw [Real.scorerHi_def, h, ofReal_re]

/-! ### Moment integrals -/

/-- The moment integrand of `Hi` is the cubic-decay kernel with `q = n` and `b = 1/3`. -/
private theorem pow_mul_cexp_neg_cube_div_three_add_mul_eq (n : ℕ) (z : ℂ) (t : ℝ) :
    (t : ℂ) ^ n * cexp (-(t : ℂ) ^ 3 / 3 + z * t) =
      (t : ℂ) ^ ((n : ℝ) : ℂ) * cexp (z * t - ((1 / 3 : ℝ) : ℂ) * (t : ℂ) ^ 3) := by
  rw [ofReal_natCast, cpow_natCast]
  push_cast
  ring_nf

/-- For every natural number `n` and complex `z`, the moment integrand
`t ↦ tⁿ exp(−t³/3 + z t)` is Bochner integrable on `(0, ∞)`. -/
theorem integrableOn_pow_mul_cexp_neg_cube_div_three_add_mul (n : ℕ) (z : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ n * cexp (-(t : ℂ) ^ 3 / 3 + z * t)) (Ioi 0) := by
  simpa only [pow_mul_cexp_neg_cube_div_three_add_mul_eq] using
    integrableOn_cpow_mul_cexp_mul_sub_mul_cube (q := n) (b := 1 / 3)
      (by linarith [n.cast_nonneg (α := ℝ)]) (by norm_num) z

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
  have h := hasDerivAt_integral_cpow_mul_cexp_mul_sub_mul_cube (q := n) (b := 1 / 3)
    (by linarith [n.cast_nonneg (α := ℝ)]) (by norm_num) z
  -- The exponent `n + 1` of the derivative kernel is the real number `n + 1`.
  have hcast : ((n : ℝ) : ℂ) + 1 = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  simpa only [hcast, pow_mul_cexp_neg_cube_div_three_add_mul_eq] using h

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

/-- `Gi` is entire. -/
@[fun_prop]
theorem differentiable_scorerGi : Differentiable ℂ scorerGi := by
  rw [funext scorerGi_def]
  fun_prop

/-- The kernel identity `∫₀^∞ (t² − z) exp(−t³/3 + z t) dt = 1`, from
`(t² − z) exp(−t³/3 + z t) = −∂ₜ exp(−t³/3 + z t)`. -/
private theorem integral_sq_sub_mul_cexp_neg_cube_div_three_add_mul (z : ℂ) :
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
    have h := norm_cpow_mul_cexp_mul_sub_mul_cube ht 0 (1 / 3) z
    simp only [ofReal_zero, cpow_zero, one_mul, Real.rpow_zero] at h
    have harg : -(t : ℂ) ^ 3 / 3 + z * t = z * t - ((1 / 3 : ℝ) : ℂ) * (t : ℂ) ^ 3 := by
      push_cast
      ring
    rw [Function.comp_apply, norm_neg, harg, h]
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

/-- If `f'' = z f + c` and `ν³ = 1`, then the rotated function `z ↦ ν f(ν z)` satisfies the same
equation. No differentiability of `f` is needed. -/
theorem iterate_deriv_two_const_mul_comp_mul_left {f : ℂ → ℂ} {c ν : ℂ}
    (hf : ∀ z, deriv^[2] f z = z * f z + c) (hν : ν ^ 3 = 1) (z : ℂ) :
    deriv^[2] (fun w => ν * f (ν * w)) z = z * (ν * f (ν * z)) + c := by
  simp only [← iteratedDeriv_eq_iterate, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_mul_left, smul_eq_mul]
  rw [iteratedDeriv_eq_iterate, hf]
  linear_combination (ν * z * f (ν * z) + c) * hν

/-- For a cube root of unity `ν`, the rotated function `z ↦ ν Hi(ν z)` solves the inhomogeneous
Airy equation `w'' = z w + 1/π`; with `ν = e^{∓2πi/3}` this is DLMF 9.12.3 for `Hi`. -/
theorem scorerHi_rotation_ode {ν : ℂ} (hν : ν ^ 3 = 1) (z : ℂ) :
    deriv^[2] (fun w => ν * scorerHi (ν * w)) z = z * (ν * scorerHi (ν * z)) + (π : ℂ)⁻¹ :=
  iterate_deriv_two_const_mul_comp_mul_left scorerHi_ode hν z

/-! ### The value at the origin -/

/-- The iterated derivatives of `Hi` at the origin:
`Hi⁽ⁿ⁾(0) = 3^{(n − 2)/3} Γ((n + 1)/3) / π`. -/
theorem iterate_deriv_scorerHi_zero (n : ℕ) :
    deriv^[n] scorerHi 0 = (3 : ℂ) ^ (((n : ℂ) - 2) / 3) * Gamma (((n : ℂ) + 1) / 3) / π := by
  have hcongr : EqOn (fun t : ℝ => (t : ℂ) ^ n * cexp (-(t : ℂ) ^ 3 / 3 + 0 * t))
      (fun t : ℝ => ((t ^ (n : ℝ) * Real.exp (-(1 / 3) * t ^ (3 : ℝ)) : ℝ) : ℂ)) (Ioi 0) := by
    intro t _
    simp only [Real.rpow_natCast, Real.rpow_ofNat, zero_mul, add_zero]
    push_cast
    ring_nf
  have hreal := _root_.integral_rpow_mul_exp_neg_mul_rpow
    (p := 3) (q := n) (b := 1 / 3) (by norm_num) (by linarith [n.cast_nonneg (α := ℝ)])
    (by norm_num)
  -- `(1/3)^(-(n + 1)/3) * (1/3) = 3^((n - 2)/3)`, as real numbers.
  have h3 : (1 / 3 : ℝ) ^ (-((n : ℝ) + 1) / 3) * (1 / 3) = (3 : ℝ) ^ (((n : ℝ) - 2) / 3) := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num),
      ← Real.rpow_neg_one 3, ← Real.rpow_add (by norm_num)]
    ring_nf
  rw [iterate_deriv_scorerHi, setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_complex_ofReal, hreal, h3, ofReal_mul,
    ofReal_cpow (by norm_num), ← Gamma_ofReal]
  push_cast
  ring

/-- The value `Hi(0) = 3^{−2/3} Γ(1/3) / π`. -/
@[simp]
theorem scorerHi_zero : scorerHi 0 = (3 : ℂ) ^ (-2 / 3 : ℂ) * Gamma (1 / 3) / π := by
  simpa using iterate_deriv_scorerHi_zero 0

end TauCeti
