/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.MeasureTheory.Integral.IntegralEqImproper

/-!
# Rotated Kummer-Laplace integrals for the upper incomplete Gamma function

For a natural number `c` and complex parameters `d` and `z`, the Laplace-type integral
`K(c, d; z) = ∫₀^∞ e^{-zt} t^c (1 + t)^d dt` converges on the open right half-plane `0 < Re z`
and extends holomorphically to `Complex.slitPlane` by rotating the ray of integration to the
bisecting direction `t = r e^{-i arg(z) / 2}` (`r > 0`), where `Re (z t) = r ‖z‖ cos(arg z / 2) > 0`
and `Re (1 + t) > 1`. At `c = 0` and `d = a - 1`, `K(0, a - 1; z)` represents the normalized upper
incomplete Gamma combination `z^{-a} e^z Γ(a, z)` on `Complex.slitPlane`; in general it equals
`c! U(c + 1, c + d + 2, z)` in terms of Tricomi's confluent hypergeometric function `U`.

## Main definitions

* `Complex.kummerLaplace c d z` — the rotated-ray Kummer-Laplace integral `K(c, d; z)`.

## Main results

* `Complex.integrableOn_exp_neg_mul_mul_exp_mul_I_mul_pow_mul_one_add_cpow_Ioi`,
  `Complex.integrableOn_exp_neg_mul_mul_pow_mul_one_add_cpow_Ioi` — integrability on `(0, ∞)` of
  the rotated-ray Kummer-Laplace integrand (`|θ| < π`, `0 < Re (z e^{iθ})`) and of the
  positive-axis integrand (`0 < Re z`).
* `Complex.kummerLaplace_eq_ray_integral`,
  `Complex.kummerLaplace_eq_ray_integral_of_abs_le_of_re_mul_exp_mul_I_pos` — Cauchy-Goursat ray
  independence across the slit-plane Stokes sector (`z ∈ slitPlane`, `|θ| < π`,
  `|arg z + θ| < π / 2`, including steepest descent `θ = -arg z`) and along any right-half-plane
  ray (`|θ| ≤ π / 2`, `0 < Re (z e^{iθ})`).
* `Complex.kummerLaplace_eq_integral_of_re_pos` — on `0 < Re z`, `kummerLaplace c d z` equals the
  unrotated positive-axis integral `∫ t in Ioi 0, cexp (-z * t) * t ^ c * (1 + t) ^ d`.
* `Complex.kummerLaplace_zero_ofReal_eq_cpow_neg_mul_exp_mul_integral` — for real `x > 0` and any
  `a : ℂ`, `kummerLaplace 0 (a - 1) x = x ^ (-a) * exp x * ∫ t in Ioi x, t ^ (a - 1) * exp (-t)`.
* `Complex.hasDerivAt_kummerLaplace`, `Complex.deriv_kummerLaplace`,
  `Complex.differentiableOn_kummerLaplace`, `Complex.differentiable_kummerLaplace_middle` —
  holomorphy on `slitPlane` in `z` (with derivative `-kummerLaplace (c + 1) d z`) and entirety
  in `d`.
* `Complex.kummerLaplace_sub_kummerLaplace_sub_one`, `Complex.mul_kummerLaplace_zero`,
  `Complex.mul_kummerLaplace_add_one`, `Complex.kummerLaplace_zero_middle` — the contiguous
  difference relation, integration-by-parts recurrences, and evaluation
  `K(c, 0; z) = c! z^{-(c+1)}`.

## References

* *NIST Digital Library of Mathematical Functions*, [§8.6](https://dlmf.nist.gov/8.6),
  [§8.9](https://dlmf.nist.gov/8.9), and [§13.4](https://dlmf.nist.gov/13.4).
* W. Gautschi, *Computational aspects of three-term recurrence relations*, SIAM Rev. 9 (1967).
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Interval Nat Real Topology

namespace Complex

/-- The rotated-ray Kummer-Laplace integral
`K(c, d; z) = ω ∫₀^∞ e^{-z r ω} (r ω)^c (1 + r ω)^d dr` along the bisecting direction
`ω = e^{-i arg(z)/2}`. For `z ∈ slitPlane`, `|arg ω| < π / 2` and `0 < Re (z ω)`, continuing
`∫₀^∞ e^{-zt} t^c (1 + t)^d dt` holomorphically across `slitPlane`. -/
def kummerLaplace (c : ℕ) (d z : ℂ) : ℂ :=
  cexp (-(z.arg / 2 : ℝ) * I) *
    ∫ r in Ioi (0 : ℝ),
      cexp (-z * (r * cexp (-(z.arg / 2 : ℝ) * I))) *
        (r * cexp (-(z.arg / 2 : ℝ) * I)) ^ c *
        (1 + r * cexp (-(z.arg / 2 : ℝ) * I)) ^ d

/-- Defining formula for `Complex.kummerLaplace`. -/
theorem kummerLaplace_def (c : ℕ) (d z : ℂ) :
    kummerLaplace c d z =
      cexp (-(z.arg / 2 : ℝ) * I) *
        ∫ r in Ioi (0 : ℝ),
          cexp (-z * (r * cexp (-(z.arg / 2 : ℝ) * I))) *
            (r * cexp (-(z.arg / 2 : ℝ) * I)) ^ c *
            (1 + r * cexp (-(z.arg / 2 : ℝ) * I)) ^ d := (rfl)

/-! ### Ray bounds and integrability -/

private def kummerLaplaceRayIntegrand (c : ℕ) (d z : ℂ) (θ r : ℝ) : ℂ :=
  cexp (-z * (r * cexp (θ * I))) * (r * cexp (θ * I)) ^ c * (1 + r * cexp (θ * I)) ^ d

private theorem kummerLaplace_eq_canonical_ray (c : ℕ) (d z : ℂ) :
    kummerLaplace c d z =
      cexp (((-(z.arg / 2) : ℝ) : ℂ) * I) *
        ∫ r in Ioi (0 : ℝ), kummerLaplaceRayIntegrand c d z (-(z.arg / 2)) r := by
  simp only [kummerLaplace_def, kummerLaplaceRayIntegrand, ofReal_neg]

private def kummerLaplaceLogIntegrand (c : ℕ) (d z w : ℂ) : ℂ :=
  cexp (((c : ℂ) + 1) * w - z * cexp w) * (1 + cexp w) ^ d

private def kummerLaplaceMajorantConst (c : ℕ) (d : ℂ) (α η : ℝ) : ℝ :=
  Real.exp (π * |d.im|) * (Real.cos (α / 2)) ^ min 0 d.re *
    (((c + ⌈d.re⌉₊)! : ℝ) * Real.exp η / η ^ (c + ⌈d.re⌉₊))

private theorem abs_neg_arg_div_two_le_pi_div_two (z : ℂ) : |-(z.arg / 2)| ≤ π / 2 :=
  (abs_neg _).trans_le (abs_arg_div_two_le_pi_div_two z)

private theorem abs_neg_arg_div_two_lt_pi (z : ℂ) : |-(z.arg / 2)| < π :=
  (abs_neg_arg_div_two_le_pi_div_two z).trans_lt (half_lt_self Real.pi_pos)

private theorem norm_kummerLaplaceRayIntegrand_le (c : ℕ) (d : ℂ) {z : ℂ} {α θ η r : ℝ}
    (hα : α < π) (hθ : |θ| ≤ α) (hη : 0 < η) (hre : 2 * η ≤ (z * cexp (θ * I)).re)
    (hr : 0 ≤ r) :
    ‖kummerLaplaceRayIntegrand c d z θ r‖ ≤
      kummerLaplaceMajorantConst c d α η * Real.exp (-η * r) := by
  have h0α : 0 ≤ α := (abs_nonneg θ).trans hθ
  have hcos_pos : 0 < Real.cos (α / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hcos_le : Real.cos (α / 2) ≤ Real.cos (θ / 2) := by
    rw [← Real.cos_abs (θ / 2), abs_div, abs_two]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith)
      (div_le_div_of_nonneg_right hθ two_pos.le)
  have hcos_rpow : (Real.cos (θ / 2)) ^ min 0 d.re ≤ (Real.cos (α / 2)) ^ min 0 d.re :=
    Real.rpow_le_rpow_of_nonpos hcos_pos hcos_le (min_le_left 0 d.re)
  have hr_rpow : (1 + r) ^ max 0 d.re ≤ (1 + r) ^ ⌈d.re⌉₊ :=
    (Real.rpow_le_rpow_of_exponent_le (by linarith)
      (max_le (Nat.cast_nonneg _) (Nat.le_ceil _))).trans_eq (Real.rpow_natCast _ _)
  have hw_cpow : ‖(1 + (r : ℂ) * cexp (θ * I)) ^ d‖ ≤
      Real.exp (π * |d.im|) * (Real.cos (α / 2)) ^ min 0 d.re * (1 + r) ^ ⌈d.re⌉₊ :=
    (norm_one_add_ofReal_mul_exp_mul_I_cpow_le (hθ.trans_lt hα) hr d).trans <|
      mul_le_mul (mul_le_mul_of_nonneg_left hcos_rpow (by positivity)) hr_rpow
        (by positivity) (by positivity)
  have hexp_re : (-z * (r * cexp (θ * I))).re = -r * (z * cexp (θ * I)).re := by
    rw [show -z * ((r : ℂ) * cexp (θ * I)) = ((-r : ℝ) : ℂ) * (z * cexp (θ * I)) by
      push_cast; ring, re_ofReal_mul]
  have hexp_le : Real.exp (-r * (z * cexp (θ * I)).re) ≤ Real.exp (-(η + η) * r) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hrc : ‖((r : ℂ) * cexp (θ * I)) ^ c‖ ≤ (1 + r) ^ c := by
    rw [norm_pow, norm_mul, norm_real, Real.norm_of_nonneg hr, norm_exp_ofReal_mul_I, mul_one]
    exact pow_le_pow_left₀ hr (by linarith) c
  rw [kummerLaplaceRayIntegrand, norm_mul, norm_mul, norm_exp, hexp_re]
  calc Real.exp (-r * (z * cexp (θ * I)).re) * ‖((r : ℂ) * cexp (θ * I)) ^ c‖ *
        ‖(1 + (r : ℂ) * cexp (θ * I)) ^ d‖
      ≤ Real.exp (-(η + η) * r) * (1 + r) ^ c *
          (Real.exp (π * |d.im|) * (Real.cos (α / 2)) ^ min 0 d.re * (1 + r) ^ ⌈d.re⌉₊) :=
        mul_le_mul (mul_le_mul hexp_le hrc (by positivity) (by positivity))
          hw_cpow (by positivity) (by positivity)
    _ = Real.exp (π * |d.im|) * (Real.cos (α / 2)) ^ min 0 d.re *
          ((1 + r) ^ (c + ⌈d.re⌉₊) * Real.exp (-(η + η) * r)) := by
        rw [pow_add]; ring
    _ ≤ Real.exp (π * |d.im|) * (Real.cos (α / 2)) ^ min 0 d.re *
          ((((c + ⌈d.re⌉₊)! : ℝ) * Real.exp η / η ^ (c + ⌈d.re⌉₊)) * Real.exp (-η * r)) :=
        mul_le_mul_of_nonneg_left
          (TauCeti.one_add_pow_mul_exp_neg_add_mul_le hη (by linarith) _) (by positivity)
    _ = kummerLaplaceMajorantConst c d α η * Real.exp (-η * r) :=
        (mul_assoc _ _ _).symm

private theorem continuousOn_kummerLaplaceRayIntegrand (c : ℕ) (d z : ℂ) {θ : ℝ}
    (hθ : |θ| < π) :
    ContinuousOn (kummerLaplaceRayIntegrand c d z θ) (Ici 0) := by
  intro r hr
  unfold kummerLaplaceRayIntegrand
  refine (((continuousAt_const.mul (continuous_ofReal.continuousAt.mul continuousAt_const)).cexp.mul
    ((continuous_ofReal.continuousAt.mul continuousAt_const).pow c)).mul ?_).continuousWithinAt
  exact ((continuousAt_const.add (continuous_ofReal.continuousAt.mul continuousAt_const)).cpow
    continuousAt_const
    (one_add_ofReal_mul_exp_mul_I_mem_slitPlane hθ hr))

/-- Along any ray `r * exp (θ * I)` avoiding the negative real axis (`|θ| < π`) on which
`0 < Re (z * exp (θ * I))`, the Kummer-Laplace ray integrand is Bochner-integrable on `(0, ∞)`. -/
theorem integrableOn_exp_neg_mul_mul_exp_mul_I_mul_pow_mul_one_add_cpow_Ioi (c : ℕ) (d : ℂ)
    {z : ℂ} {θ : ℝ} (hθ : |θ| < π) (hre : 0 < (z * cexp (θ * I)).re) :
    IntegrableOn
      (fun r : ℝ =>
        cexp (-z * (r * cexp (θ * I))) * (r * cexp (θ * I)) ^ c * (1 + r * cexp (θ * I)) ^ d)
      (Ioi 0) := by
  set η := (z * cexp (θ * I)).re / 2
  have hη : 0 < η := half_pos hre
  refine Integrable.mono'
    ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hη) 0).const_mul
      (kummerLaplaceMajorantConst c d |θ| η))
    ((continuousOn_kummerLaplaceRayIntegrand c d z hθ).mono Ioi_subset_Ici_self
      |>.aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_)
  exact norm_kummerLaplaceRayIntegrand_le c d hθ le_rfl hη (by dsimp only [η]; linarith) hr.out.le

/-- For `0 < z.re`, the Kummer-Laplace integrand `t ↦ cexp (-z * t) * t ^ c * (1 + t) ^ d` is
Bochner-integrable on `(0, ∞)`. -/
theorem integrableOn_exp_neg_mul_mul_pow_mul_one_add_cpow_Ioi (c : ℕ) (d : ℂ) {z : ℂ}
    (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => cexp (-z * t) * (t : ℂ) ^ c * (1 + (t : ℂ)) ^ d) (Ioi 0) := by
  simpa using integrableOn_exp_neg_mul_mul_exp_mul_I_mul_pow_mul_one_add_cpow_Ioi c d
    (θ := 0) (by rw [abs_zero]; exact Real.pi_pos) (by simpa using hz)

private theorem continuousOn_kummerLaplaceRayIntegrand_neg_arg_div_two (c : ℕ) (d w z : ℂ) :
    ContinuousOn (kummerLaplaceRayIntegrand c d w (-(z.arg / 2))) (Ici 0) :=
  continuousOn_kummerLaplaceRayIntegrand c d w (abs_neg_arg_div_two_lt_pi z)

private theorem integrableOn_kummerLaplaceRayIntegrand_neg_arg_div_two (c : ℕ) (d : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    IntegrableOn (kummerLaplaceRayIntegrand c d z (-(z.arg / 2))) (Ioi 0) :=
  integrableOn_exp_neg_mul_mul_exp_mul_I_mul_pow_mul_one_add_cpow_Ioi c d
    (abs_neg_arg_div_two_lt_pi z) (re_mul_exp_neg_arg_div_two_mul_I_pos hz)

/-! ### Cauchy-Goursat ray independence -/

private theorem kummerLaplaceLogIntegrand_eq_ray (c : ℕ) (d z : ℂ) (θ x : ℝ) :
    kummerLaplaceLogIntegrand c d z ((x : ℂ) + (θ : ℂ) * I) =
      cexp (θ * I) * (Real.exp x • kummerLaplaceRayIntegrand c d z θ (Real.exp x)) := by
  unfold kummerLaplaceLogIntegrand kummerLaplaceRayIntegrand
  have hexp : cexp ((x : ℂ) + (θ : ℂ) * I) = (Real.exp x : ℂ) * cexp (θ * I) := by
    rw [Complex.exp_add, ofReal_exp]
  have hlin : ((c : ℂ) + 1) * ((x : ℂ) + (θ : ℂ) * I) - z * cexp ((x : ℂ) + (θ : ℂ) * I) =
      ((x : ℂ) + (θ : ℂ) * I) + ↑c * ((x : ℂ) + (θ : ℂ) * I) +
        (-z * ((Real.exp x : ℂ) * cexp (θ * I))) := by
    rw [hexp]; ring
  rw [hlin, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul, hexp, real_smul]
  ring

private theorem integrable_kummerLaplaceLogIntegrand_horizontal (c : ℕ) (d : ℂ) {z : ℂ} {θ : ℝ}
    (hθ : |θ| < π) (hre : 0 < (z * cexp (θ * I)).re) :
    Integrable fun x : ℝ => kummerLaplaceLogIntegrand c d z ((x : ℂ) + θ * I) := by
  simp_rw [kummerLaplaceLogIntegrand_eq_ray]
  exact ((integrable_comp_exp _).mpr
    (integrableOn_exp_neg_mul_mul_exp_mul_I_mul_pow_mul_one_add_cpow_Ioi c d hθ hre)).const_mul _

private theorem integral_kummerLaplaceLogIntegrand_horizontal (c : ℕ) (d z : ℂ) (θ : ℝ) :
    (∫ x : ℝ, kummerLaplaceLogIntegrand c d z ((x : ℂ) + θ * I)) =
      cexp (θ * I) * ∫ r in Ioi (0 : ℝ), kummerLaplaceRayIntegrand c d z θ r := by
  simp_rw [kummerLaplaceLogIntegrand_eq_ray, integral_const_mul, integral_comp_exp]

private theorem differentiableOn_kummerLaplaceLogIntegrand (c : ℕ) (d z : ℂ) :
    DifferentiableOn ℂ (kummerLaplaceLogIntegrand c d z) {w : ℂ | |w.im| < π} := by
  intro w hw
  unfold kummerLaplaceLogIntegrand
  have hslit : 1 + cexp w ∈ slitPlane := by
    simpa using TauCeti.ofReal_add_mem_slitPlane (exp_mem_slitPlane_of_abs_im_lt hw) zero_le_one
  exact ((((differentiableAt_id.const_mul _).sub
    (differentiableAt_id.cexp.const_mul z)).cexp).mul
    ((differentiableAt_const (1 : ℂ)).add differentiableAt_id.cexp |>.cpow_const hslit))
    |>.differentiableWithinAt

private theorem norm_integral_kummerLaplaceLogIntegrand_vertical_le (c : ℕ) (d : ℂ) {z : ℂ}
    {θ₁ θ₂ α η : ℝ} (hα : α < π) (hη : 0 < η)
    (hstrip : ∀ θ ∈ [[θ₁, θ₂]], |θ| ≤ α ∧ 2 * η ≤ (z * cexp (θ * I)).re) (x : ℝ) :
    ‖∫ y in θ₁..θ₂, kummerLaplaceLogIntegrand c d z ((x : ℂ) + y * I)‖ ≤
      kummerLaplaceMajorantConst c d α η * |θ₂ - θ₁| * Real.exp x *
        Real.exp (-η * Real.exp x) := by
  calc ‖∫ y in θ₁..θ₂, kummerLaplaceLogIntegrand c d z ((x : ℂ) + y * I)‖
      ≤ (Real.exp x * (kummerLaplaceMajorantConst c d α η * Real.exp (-η * Real.exp x))) *
          |θ₂ - θ₁| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
        obtain ⟨hy_abs, hy_re⟩ := hstrip y (uIoc_subset_uIcc hy)
        rw [kummerLaplaceLogIntegrand_eq_ray, norm_mul, norm_exp_ofReal_mul_I, one_mul,
          norm_smul, Real.norm_of_nonneg (Real.exp_pos x).le]
        exact mul_le_mul_of_nonneg_left
          (norm_kummerLaplaceRayIntegrand_le c d hα hy_abs hη hy_re (Real.exp_pos x).le)
          (Real.exp_pos x).le
    _ = kummerLaplaceMajorantConst c d α η * |θ₂ - θ₁| * Real.exp x *
          Real.exp (-η * Real.exp x) := by ring

private theorem tendsto_vertical_right_kummerLaplaceLogIntegrand (c : ℕ) (d : ℂ) {z : ℂ}
    {θ₁ θ₂ α η : ℝ} (hα : α < π) (hη : 0 < η)
    (hstrip : ∀ θ ∈ [[θ₁, θ₂]], |θ| ≤ α ∧ 2 * η ≤ (z * cexp (θ * I)).re) :
    Tendsto (fun R : ℝ => ∫ y in θ₁..θ₂, kummerLaplaceLogIntegrand c d z ((R : ℂ) + y * I))
      atTop (𝓝 0) := by
  have hdecay : Tendsto (fun R : ℝ => Real.exp R * Real.exp (-η * Real.exp R)) atTop (𝓝 0) := by
    simpa [Function.comp_def, Real.rpow_one, ← neg_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 η hη).comp Real.tendsto_exp_atTop
  refine squeeze_zero_norm (fun R => ?_)
    (by simpa [mul_assoc] using
      hdecay.const_mul (kummerLaplaceMajorantConst c d α η * |θ₂ - θ₁|))
  simpa only [mul_assoc, neg_mul] using
    norm_integral_kummerLaplaceLogIntegrand_vertical_le c d hα hη hstrip R

private theorem tendsto_vertical_left_kummerLaplaceLogIntegrand (c : ℕ) (d : ℂ) {z : ℂ}
    {θ₁ θ₂ α η : ℝ} (hα0 : 0 ≤ α) (hα : α < π) (hη : 0 < η)
    (hstrip : ∀ θ ∈ [[θ₁, θ₂]], |θ| ≤ α ∧ 2 * η ≤ (z * cexp (θ * I)).re) :
    Tendsto (fun R : ℝ => ∫ y in θ₁..θ₂, kummerLaplaceLogIntegrand c d z (-(R : ℂ) + y * I))
      atTop (𝓝 0) := by
  have hzero : Tendsto
      (fun R : ℝ => kummerLaplaceMajorantConst c d α η * |θ₂ - θ₁| * Real.exp (-R))
      atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul
      (kummerLaplaceMajorantConst c d α η * |θ₂ - θ₁|)
  refine squeeze_zero_norm (fun R => ?_) hzero
  rw [show -(R : ℂ) = ((-R : ℝ) : ℂ) by push_cast; rfl]
  refine (norm_integral_kummerLaplaceLogIntegrand_vertical_le c d hα hη hstrip (-R)).trans ?_
  have hcos_pos : 0 < Real.cos (α / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hM : 0 ≤ kummerLaplaceMajorantConst c d α η := by
    unfold kummerLaplaceMajorantConst; positivity
  exact mul_le_of_le_one_right (by positivity)
    (Real.exp_le_one_iff.mpr (by nlinarith [Real.exp_pos (-R)]))

private theorem tendsto_sub_horizontal_kummerLaplaceLogIntegrand (c : ℕ) (d : ℂ) {z : ℂ}
    {θ₁ θ₂ : ℝ} (hθ₁ : |θ₁| < π) (hre₁ : 0 < (z * cexp (θ₁ * I)).re)
    (hθ₂ : |θ₂| < π) (hre₂ : 0 < (z * cexp (θ₂ * I)).re) (hθ₁₂ : |θ₁ - θ₂| ≤ π) :
    Tendsto (fun R : ℝ =>
      (∫ x in (-R)..R, kummerLaplaceLogIntegrand c d z ((x : ℂ) + θ₁ * I)) -
        (∫ x in (-R)..R, kummerLaplaceLogIntegrand c d z ((x : ℂ) + θ₂ * I)))
      atTop (𝓝 0) := by
  set α : ℝ := max |θ₁| |θ₂|
  have hα0 : 0 ≤ α := (abs_nonneg θ₁).trans (le_max_left _ _)
  have hα : α < π := max_lt hθ₁ hθ₂
  obtain ⟨θm, hθm_mem, hθm_min⟩ := isCompact_uIcc.exists_isMinOn nonempty_uIcc
    (f := fun y : ℝ => (z * cexp (y * I)).re) (by fun_prop)
  set η := (z * cexp (θm * I)).re / 2
  have hη : 0 < η := half_pos (re_mul_exp_mul_I_pos_of_mem_uIcc hθ₁₂ hre₁ hre₂ hθm_mem)
  have hstrip : ∀ y ∈ [[θ₁, θ₂]], |y| ≤ α ∧ 2 * η ≤ (z * cexp (y * I)).re := fun y hy => by
    obtain ⟨h₁l, h₁r⟩ := abs_le.mp (le_max_left |θ₁| |θ₂|)
    obtain ⟨h₂l, h₂r⟩ := abs_le.mp (le_max_right |θ₁| |θ₂|)
    have hy_abs : |y| ≤ α := by
      rcases mem_uIcc.mp hy with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;>
        exact abs_le.mpr ⟨by linarith, by linarith⟩
    exact ⟨hy_abs, by dsimp only [η]; linarith [show (z * cexp (θm * I)).re ≤ _ from hθm_min hy]⟩
  have hrect : ∀ R : ℝ,
      ((∫ x in (-R)..R, kummerLaplaceLogIntegrand c d z ((x : ℂ) + θ₁ * I)) -
        (∫ x in (-R)..R, kummerLaplaceLogIntegrand c d z ((x : ℂ) + θ₂ * I))) +
        I • (∫ y in θ₁..θ₂, kummerLaplaceLogIntegrand c d z ((R : ℂ) + y * I)) -
        I • (∫ y in θ₁..θ₂, kummerLaplaceLogIntegrand c d z (-(R : ℂ) + y * I)) = 0 := fun R => by
    simpa using integral_boundary_rect_eq_zero_of_differentiableOn
      (kummerLaplaceLogIntegrand c d z) ((-R : ℝ) + θ₁ * I) ((R : ℝ) + θ₂ * I)
      ((differentiableOn_kummerLaplaceLogIntegrand c d z).mono fun w hw =>
        (hstrip w.im (by simpa using hw.2)).1.trans_lt hα)
  have hcomb :=
    ((tendsto_vertical_left_kummerLaplaceLogIntegrand c d hα0 hα hη hstrip).const_smul I).sub
      ((tendsto_vertical_right_kummerLaplaceLogIntegrand c d hα hη hstrip).const_smul I)
  rw [sub_self] at hcomb
  exact hcomb.congr fun R => by linear_combination -(hrect R)

/-- **Ray independence of `kummerLaplace` across the slit-plane Stokes sector.**
For `z ∈ slitPlane` and any ray angle `|θ| < π` in the Stokes sector `|arg z + θ| < π / 2`
(in particular along the steepest-descent ray `θ = -arg z`), the rotated Laplace integral along
`r e^{iθ}` (`r > 0`) equals `kummerLaplace c d z`. -/
theorem kummerLaplace_eq_ray_integral (c : ℕ) (d : ℂ) {z : ℂ} (hz : z ∈ slitPlane) {θ : ℝ}
    (hθ : |θ| < π) (harg : |z.arg + θ| < π / 2) :
    kummerLaplace c d z =
      cexp (θ * I) *
        ∫ r in Ioi (0 : ℝ),
          cexp (-z * (r * cexp (θ * I))) * (r * cexp (θ * I)) ^ c *
            (1 + r * cexp (θ * I)) ^ d := by
  -- Express both ray integrals as horizontal integrals in logarithmic coordinates.
  have hθ₀ : |-(z.arg / 2)| < π := abs_neg_arg_div_two_lt_pi z
  have hre₀ : 0 < (z * cexp ((-(z.arg / 2) : ℝ) * I)).re := re_mul_exp_neg_arg_div_two_mul_I_pos hz
  have hre : 0 < (z * cexp (θ * I)).re := by
    rw [re_mul_exp_ofReal_mul_I_eq_norm_mul_cos]
    exact mul_pos (norm_pos_iff.2 (slitPlane_ne_zero hz))
      (Real.cos_pos_of_mem_Ioo (abs_lt.mp harg))
  have hsep : |-(z.arg / 2) - θ| ≤ π := by
    calc |-(z.arg / 2) - θ| = |-(z.arg + θ) + z.arg / 2| := by ring_nf
      _ ≤ |-(z.arg + θ)| + |z.arg / 2| := abs_add_le _ _
      _ ≤ π := by rw [abs_neg]; linarith [harg.le, abs_arg_div_two_le_pi_div_two z]
  -- Exhaust both horizontal lines by `[-R, R]` and cancel their difference via Cauchy-Goursat.
  have hlim₀ := intervalIntegral_tendsto_integral
    (integrable_kummerLaplaceLogIntegrand_horizontal c d hθ₀ hre₀)
    tendsto_neg_atTop_atBot tendsto_id
  have hlim₁ := intervalIntegral_tendsto_integral
    (integrable_kummerLaplaceLogIntegrand_horizontal c d hθ hre)
    tendsto_neg_atTop_atBot tendsto_id
  have hline : (∫ x : ℝ, kummerLaplaceLogIntegrand c d z ((x : ℂ) + (-(z.arg / 2) : ℝ) * I)) =
      ∫ x : ℝ, kummerLaplaceLogIntegrand c d z ((x : ℂ) + θ * I) :=
    sub_eq_zero.mp (tendsto_nhds_unique (hlim₀.sub hlim₁)
      (tendsto_sub_horizontal_kummerLaplaceLogIntegrand c d hθ₀ hre₀ hθ hre hsep))
  exact (kummerLaplace_eq_canonical_ray c d z).trans <|
    (integral_kummerLaplaceLogIntegrand_horizontal c d z _).symm.trans <|
      hline.trans (integral_kummerLaplaceLogIntegrand_horizontal c d z θ)

/-- Along any ray in the closed right half-plane (`|θ| ≤ π / 2`) on which `0 < Re (z e^{iθ})`,
`z` automatically lies in `slitPlane` with `|arg z + θ| < π / 2`, and the rotated Laplace integral
along `r e^{iθ}` equals `kummerLaplace c d z`. -/
theorem kummerLaplace_eq_ray_integral_of_abs_le_of_re_mul_exp_mul_I_pos (c : ℕ) (d : ℂ) {z : ℂ}
    {θ : ℝ} (hθ : |θ| ≤ π / 2) (hre : 0 < (z * cexp (θ * I)).re) :
    kummerLaplace c d z =
      cexp (θ * I) *
        ∫ r in Ioi (0 : ℝ),
          cexp (-z * (r * cexp (θ * I))) * (r * cexp (θ * I)) ^ c *
            (1 + r * cexp (θ * I)) ^ d :=
  kummerLaplace_eq_ray_integral c d (mem_slitPlane_of_abs_le_of_re_mul_exp_mul_I_pos hθ hre)
    (hθ.trans_lt (half_lt_self Real.pi_pos))
    (abs_arg_add_lt_pi_div_two_of_abs_le_of_re_mul_exp_mul_I_pos hθ hre)

/-- On the open right half-plane `0 < Re z`, `kummerLaplace c d z` equals the unrotated Laplace
integral along `(0, ∞)`. -/
theorem kummerLaplace_eq_integral_of_re_pos (c : ℕ) (d : ℂ) {z : ℂ} (hz : 0 < z.re) :
    kummerLaplace c d z =
      ∫ t in Ioi (0 : ℝ), cexp (-z * t) * (t : ℂ) ^ c * (1 + (t : ℂ)) ^ d := by
  simpa using kummerLaplace_eq_ray_integral_of_abs_le_of_re_mul_exp_mul_I_pos c d (z := z) (θ := 0)
    (by rw [abs_zero]; positivity) (by simpa using hz)

/-- For a positive real argument `x > 0` and any complex `a`, `kummerLaplace 0 (a - 1) x` is
`x ^ (-a) * exp x` times Euler's upper incomplete Gamma integral `∫_x^∞ t^{a-1} e^{-t} dt`. -/
theorem kummerLaplace_zero_ofReal_eq_cpow_neg_mul_exp_mul_integral (a : ℂ) {x : ℝ} (hx : 0 < x) :
    kummerLaplace 0 (a - 1) x =
      (x : ℂ) ^ (-a) * cexp x * ∫ t in Ioi x, (t : ℂ) ^ (a - 1) * cexp (-t) := by
  rw [kummerLaplace_eq_integral_of_re_pos 0 (a - 1) (by simpa using hx)]
  have hsub : (∫ t in Ioi x, (t : ℂ) ^ (a - 1) * cexp (-t)) =
      x • ∫ r in Ioi (0 : ℝ),
        (((x + x * r : ℝ) : ℂ) ^ (a - 1) * cexp (-((x + x * r : ℝ) : ℂ))) := by
    simpa using (TauCeti.integral_comp_add_mul_left_Ioi'
      (fun t : ℝ => (t : ℂ) ^ (a - 1) * cexp (-t)) 0 x hx).symm
  rw [hsub, real_smul, ← mul_assoc, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hexp : cexp (x : ℂ) * cexp (-(x : ℂ)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hpow : (x : ℂ) ^ (-a) * (x : ℂ) * (x : ℂ) ^ (a - 1) = 1 := by
    nth_rw 2 [← cpow_one (x : ℂ)]
    rw [← cpow_add _ _ hx0, ← cpow_add _ _ hx0]; simp
  rw [show (x + x * r : ℝ) = x * (1 + r) by ring, ofReal_mul, TauCeti.ofReal_mul_cpow hx.le,
    ofReal_add, ofReal_one,
    show -((x : ℂ) * (1 + (r : ℂ))) = -(x : ℂ) + -(x : ℂ) * (r : ℂ) by ring,
    Complex.exp_add, pow_zero, mul_one]
  linear_combination -(cexp (-(x : ℂ) * (r : ℂ)) * (1 + (r : ℂ)) ^ (a - 1)) *
    (cexp (x : ℂ) * cexp (-(x : ℂ)) * hpow + hexp)

/-! ### Holomorphy in `z` and `d` -/

/-- On `slitPlane`, `z ↦ kummerLaplace c d z` has complex derivative
`-kummerLaplace (c + 1) d z`. -/
theorem hasDerivAt_kummerLaplace (c : ℕ) (d : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (kummerLaplace c d) (-kummerLaplace (c + 1) d z) z := by
  set θ₀ : ℝ := -(z.arg / 2)
  have hθ₀ : |θ₀| ≤ π / 2 := abs_neg_arg_div_two_le_pi_div_two z
  have hθ₀_lt : |θ₀| < π := abs_neg_arg_div_two_lt_pi z
  have hre₀ : 0 < (z * cexp (θ₀ * I)).re := re_mul_exp_neg_arg_div_two_mul_I_pos hz
  set η := (z * cexp (θ₀ * I)).re / 4
  have hη : 0 < η := by dsimp only [η]; linarith
  set U : Set ℂ := {w : ℂ | 2 * η < (w * cexp (θ₀ * I)).re}
  have hU_open : IsOpen U :=
    isOpen_lt continuous_const (continuous_re.comp (continuous_id.mul continuous_const))
  have hzU : 2 * η < (z * cexp (θ₀ * I)).re := by dsimp only [η]; linarith
  have heq : kummerLaplace c d =ᶠ[𝓝 z]
      fun w => cexp (θ₀ * I) * ∫ r in Ioi (0 : ℝ), kummerLaplaceRayIntegrand c d w θ₀ r := by
    filter_upwards [hU_open.mem_nhds hzU] with w hw
    have hw' : 2 * η < (w * cexp (θ₀ * I)).re := hw
    exact kummerLaplace_eq_ray_integral_of_abs_le_of_re_mul_exp_mul_I_pos c d hθ₀ (by linarith)
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := U)
    (F := fun w r => kummerLaplaceRayIntegrand c d w θ₀ r)
    (F' := fun w r => -kummerLaplaceRayIntegrand (c + 1) d w θ₀ r)
    (bound := fun r => kummerLaplaceMajorantConst (c + 1) d |θ₀| η * Real.exp (-η * r))
    (hU_open.mem_nhds hzU)
    (.of_forall fun w => (continuousOn_kummerLaplaceRayIntegrand_neg_arg_div_two c d w z).mono
      Ioi_subset_Ici_self |>.aestronglyMeasurable measurableSet_Ioi)
    (integrableOn_kummerLaplaceRayIntegrand_neg_arg_div_two c d hz)
    ((continuousOn_kummerLaplaceRayIntegrand_neg_arg_div_two (c + 1) d z z).neg.mono
      Ioi_subset_Ici_self |>.aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr w hw => ?_)
    ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hη) 0).const_mul
      (kummerLaplaceMajorantConst (c + 1) d |θ₀| η))
    (ae_restrict_of_forall_mem measurableSet_Ioi fun r _ w _ => ?_)
  · have hmul := (hderiv.2.const_mul (cexp (θ₀ * I))).congr_of_eventuallyEq heq
    convert hmul using 1
    rw [integral_neg, mul_neg, kummerLaplace_eq_canonical_ray]
  · rw [norm_neg]
    exact norm_kummerLaplaceRayIntegrand_le (c + 1) d hθ₀_lt le_rfl hη (le_of_lt hw) hr.out.le
  · unfold kummerLaplaceRayIntegrand
    set t : ℂ := (r : ℂ) * cexp (θ₀ * I)
    have hd := (((hasDerivAt_id w).neg.mul_const t).cexp.mul_const (t ^ c)).mul_const ((1 + t) ^ d)
    refine hd.congr_deriv ?_
    simp only [Pi.neg_apply, id_eq, pow_succ]
    ring

/-- On `slitPlane`, the complex derivative of `kummerLaplace c d` at `z` is
`-kummerLaplace (c + 1) d z`. -/
@[simp, grind =]
theorem deriv_kummerLaplace (c : ℕ) (d : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (kummerLaplace c d) z = -kummerLaplace (c + 1) d z :=
  (hasDerivAt_kummerLaplace c d hz).deriv

/-- For every `c : ℕ` and `d : ℂ`, `kummerLaplace c d` is holomorphic on `slitPlane`. -/
theorem differentiableOn_kummerLaplace (c : ℕ) (d : ℂ) :
    DifferentiableOn ℂ (kummerLaplace c d) slitPlane :=
  fun _ hz => (hasDerivAt_kummerLaplace c d hz).differentiableAt.differentiableWithinAt

private theorem norm_kummerLaplaceRayIntegrand_le_mul_exp (c m : ℕ) {d z : ℂ} {θ B μ r : ℝ}
    (hθ : |θ| ≤ π / 2) (hr : 0 ≤ r) (hd_im : |d.im| ≤ B) (hd_re : d.re ≤ m)
    (hre : μ ≤ (z * cexp (θ * I)).re) :
    ‖kummerLaplaceRayIntegrand c d z θ r‖ ≤
      Real.exp (π * B) * (1 + r) ^ (c + m) * Real.exp (-μ * r) := by
  unfold kummerLaplaceRayIntegrand
  set t : ℂ := (r : ℂ) * cexp (θ * I)
  have ht_re : 0 ≤ t.re := by
    rw [re_ofReal_mul, exp_ofReal_mul_I_re]
    exact mul_nonneg hr (Real.cos_nonneg_of_mem_Icc ⟨(abs_le.mp hθ).1, (abs_le.mp hθ).2⟩)
  have ht_norm : ‖t‖ = r := by
    rw [norm_mul, norm_real, Real.norm_of_nonneg hr, norm_exp_ofReal_mul_I, mul_one]
  have hw_cpow : ‖(1 + t) ^ d‖ ≤ Real.exp (π * B) * (1 + r) ^ m := by
    refine (norm_one_add_cpow_le ht_re d).trans ?_
    rw [ht_norm, ← Real.rpow_natCast]
    exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd_im Real.pi_pos.le))
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (max_le (Nat.cast_nonneg m) hd_re))
      (by positivity) (by positivity)
  have hexp_re : (-z * t).re = -r * (z * cexp (θ * I)).re := by
    rw [show -z * t = -(r : ℂ) * (z * cexp (θ * I)) by dsimp only [t]; ring, neg_mul, neg_re,
      re_ofReal_mul]
    ring
  rw [norm_mul, norm_mul, norm_exp, hexp_re, norm_pow, ht_norm, pow_add]
  calc Real.exp (-r * (z * cexp (θ * I)).re) * r ^ c * ‖(1 + t) ^ d‖
      ≤ Real.exp (-μ * r) * (1 + r) ^ c * (Real.exp (π * B) * (1 + r) ^ m) :=
        mul_le_mul (mul_le_mul (Real.exp_le_exp.mpr (by nlinarith))
          (pow_le_pow_left₀ hr (by linarith) c) (by positivity) (by positivity))
          hw_cpow (by positivity) (by positivity)
    _ = Real.exp (π * B) * ((1 + r) ^ c * (1 + r) ^ m) * Real.exp (-μ * r) := by ring

private theorem norm_kummerLaplaceRayIntegrand_mul_log_le (c m : ℕ) {d d₀ z : ℂ} {θ η r : ℝ}
    (hθ : |θ| ≤ π / 2) (hη : 0 < η) (hre : 2 * η ≤ (z * cexp (θ * I)).re) (hr : 0 ≤ r)
    (hd : ‖d - d₀‖ < 1) (hm : ⌈|d₀.re| + 1⌉₊ ≤ m) :
    ‖kummerLaplaceRayIntegrand c d z θ r * log (1 + r * cexp (θ * I))‖ ≤
      ((1 + π) * Real.exp (π * (|d₀.im| + 1)) *
        (((c + 1 + m)! : ℝ) * Real.exp η / η ^ (c + 1 + m))) * Real.exp (-η * r) := by
  obtain ⟨hd_re₁, hd_re₂⟩ := abs_lt.mp ((abs_re_le_norm (d - d₀)).trans_lt hd)
  obtain ⟨hd_im₁, hd_im₂⟩ := abs_lt.mp ((abs_im_le_norm (d - d₀)).trans_lt hd)
  rw [sub_re] at hd_re₁ hd_re₂; rw [sub_im] at hd_im₁ hd_im₂
  have hd_re : d.re ≤ m :=
    (by linarith [le_abs_self d₀.re] : d.re ≤ |d₀.re| + 1).trans
      ((Nat.le_ceil _).trans (Nat.cast_le.mpr hm))
  have hd_im : |d.im| ≤ |d₀.im| + 1 :=
    abs_le.mpr ⟨by linarith [neg_abs_le d₀.im], by linarith [le_abs_self d₀.im]⟩
  have ht_re : 0 ≤ ((r : ℂ) * cexp (θ * I)).re := by
    rw [re_ofReal_mul, exp_ofReal_mul_I_re]
    exact mul_nonneg hr (Real.cos_nonneg_of_mem_Icc ⟨(abs_le.mp hθ).1, (abs_le.mp hθ).2⟩)
  set w : ℂ := 1 + r * cexp (θ * I)
  have hw1 : 1 ≤ ‖w‖ := one_le_norm_one_add ht_re
  have hwu : ‖w‖ ≤ 1 + r :=
    (norm_one_add_ofReal_mul_exp_mul_I_le θ r).trans_eq (by rw [abs_of_nonneg hr])
  have hlog_le : ‖log w‖ ≤ (1 + π) * (1 + r) := by
    have hlr : |Real.log ‖w‖| ≤ r := by
      rw [abs_of_nonneg (Real.log_nonneg hw1)]
      exact (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hw1)).trans (by linarith [hwu])
    calc ‖log w‖ ≤ |(log w).re| + |(log w).im| := norm_le_abs_re_add_abs_im (log w)
      _ = |Real.log ‖w‖| + |w.arg| := by rw [log_re, log_im]
      _ ≤ (1 + π) * (1 + r) := by nlinarith [abs_arg_le_pi w, Real.pi_pos]
  have hneg : -(η + η) * r = -(2 * η) * r := by ring
  have hidx : c + 1 + m = (c + m) + 1 := by omega
  rw [norm_mul]
  calc ‖kummerLaplaceRayIntegrand c d z θ r‖ * ‖log w‖
      ≤ (Real.exp (π * (|d₀.im| + 1)) * (1 + r) ^ (c + m) * Real.exp (-(η + η) * r)) *
          ((1 + π) * (1 + r)) := by
        rw [hneg]
        exact mul_le_mul (norm_kummerLaplaceRayIntegrand_le_mul_exp c m hθ hr hd_im hd_re hre)
          hlog_le (norm_nonneg _) (by positivity)
    _ = (1 + π) * Real.exp (π * (|d₀.im| + 1)) *
          ((1 + r) ^ (c + 1 + m) * Real.exp (-(η + η) * r)) := by
        rw [hidx, pow_succ]; ring
    _ ≤ (1 + π) * Real.exp (π * (|d₀.im| + 1)) *
          ((((c + 1 + m)! : ℝ) * Real.exp η / η ^ (c + 1 + m)) * Real.exp (-η * r)) :=
        mul_le_mul_of_nonneg_left (TauCeti.one_add_pow_mul_exp_neg_add_mul_le hη (by linarith) _)
          (by positivity)
    _ = _ := (mul_assoc _ _ _).symm

private theorem hasDerivAt_kummerLaplaceRayIntegrand_middle (c : ℕ) (d z : ℂ) {θ r : ℝ}
    (hθ : |θ| < π) (hr : 0 ≤ r) :
    HasDerivAt (fun w => kummerLaplaceRayIntegrand c w z θ r)
      (kummerLaplaceRayIntegrand c d z θ r * log (1 + r * cexp (θ * I))) d := by
  unfold kummerLaplaceRayIntegrand
  have hw0 : 1 + (r : ℂ) * cexp (θ * I) ≠ 0 :=
    slitPlane_ne_zero (one_add_ofReal_mul_exp_mul_I_mem_slitPlane hθ hr)
  simpa [mul_assoc] using
    ((hasDerivAt_id d).const_cpow (Or.inl hw0)).const_mul
      (cexp (-z * (r * cexp (θ * I))) * (r * cexp (θ * I)) ^ c)

/-- For every `c : ℕ` and `z ∈ slitPlane`, `d ↦ kummerLaplace c d z` is entire. -/
theorem differentiable_kummerLaplace_middle (c : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    Differentiable ℂ fun d => kummerLaplace c d z := by
  intro d₀
  set θ₀ : ℝ := -(z.arg / 2)
  have hθ₀ : |θ₀| ≤ π / 2 := abs_neg_arg_div_two_le_pi_div_two z
  have hθ₀_lt : |θ₀| < π := abs_neg_arg_div_two_lt_pi z
  have hre₀ : 0 < (z * cexp (θ₀ * I)).re := re_mul_exp_neg_arg_div_two_mul_I_pos hz
  set η := (z * cexp (θ₀ * I)).re / 4
  have hη : 0 < η := by dsimp only [η]; linarith
  have h2η : 2 * η ≤ (z * cexp (θ₀ * I)).re := by dsimp only [η]; linarith
  set m : ℕ := ⌈|d₀.re| + 1⌉₊
  set K : ℝ := (1 + π) * Real.exp (π * (|d₀.im| + 1)) *
    (((c + 1 + m)! : ℝ) * Real.exp η / η ^ (c + 1 + m))
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Metric.ball d₀ 1)
    (F := fun d r => kummerLaplaceRayIntegrand c d z θ₀ r)
    (F' := fun d r => kummerLaplaceRayIntegrand c d z θ₀ r * log (1 + r * cexp (θ₀ * I)))
    (bound := fun r => K * Real.exp (-η * r))
    (Metric.ball_mem_nhds d₀ one_pos)
    (.of_forall fun d => (continuousOn_kummerLaplaceRayIntegrand_neg_arg_div_two c d z z).mono
      Ioi_subset_Ici_self |>.aestronglyMeasurable measurableSet_Ioi)
    (integrableOn_kummerLaplaceRayIntegrand_neg_arg_div_two c d₀ hz)
    (((continuousOn_kummerLaplaceRayIntegrand_neg_arg_div_two c d₀ z z).mul fun r hr =>
        ((continuousAt_const.add (continuous_ofReal.continuousAt.mul continuousAt_const)).clog
          (one_add_ofReal_mul_exp_mul_I_mem_slitPlane hθ₀_lt hr)).continuousWithinAt).mono
      Ioi_subset_Ici_self |>.aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr d hd =>
      norm_kummerLaplaceRayIntegrand_mul_log_le c m hθ₀ hη h2η hr.out.le
        (by simpa [dist_eq_norm] using hd) le_rfl)
    ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hη) 0).const_mul K)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr d _ =>
      hasDerivAt_kummerLaplaceRayIntegrand_middle c d z hθ₀_lt hr.out.le)
  simp_rw [kummerLaplace_eq_canonical_ray]
  exact (hderiv.2.const_mul (cexp (θ₀ * I))).differentiableAt

/-! ### Contiguous and integration-by-parts recurrences -/

private theorem kummerLaplaceRayIntegrand_sub_sub_one (c : ℕ) (d z : ℂ) {θ r : ℝ}
    (hθ : |θ| < π) (hr : 0 ≤ r) :
    kummerLaplaceRayIntegrand c d z θ r - kummerLaplaceRayIntegrand c (d - 1) z θ r =
      kummerLaplaceRayIntegrand (c + 1) (d - 1) z θ r := by
  unfold kummerLaplaceRayIntegrand
  set t : ℂ := (r : ℂ) * cexp (θ * I)
  have ht1 : 1 + t ≠ 0 :=
    slitPlane_ne_zero (one_add_ofReal_mul_exp_mul_I_mem_slitPlane hθ hr)
  have hd_eq : d = d - 1 + 1 := by ring
  have hpow : (1 + t) ^ d = (1 + t) ^ (d - 1) * (1 + t) := by
    nth_rw 1 [hd_eq]
    rw [cpow_add _ _ ht1, cpow_one]
  rw [hpow, pow_succ]
  ring

/-- **Contiguous difference relation**:
`K(c, d; z) - K(c, d - 1; z) = K(c + 1, d - 1; z)` on `slitPlane`. -/
theorem kummerLaplace_sub_kummerLaplace_sub_one (c : ℕ) (d : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    kummerLaplace c d z - kummerLaplace c (d - 1) z = kummerLaplace (c + 1) (d - 1) z := by
  rw [kummerLaplace_eq_canonical_ray, kummerLaplace_eq_canonical_ray,
    kummerLaplace_eq_canonical_ray, ← mul_sub]
  congr 1
  rw [← integral_sub (integrableOn_kummerLaplaceRayIntegrand_neg_arg_div_two c d hz)
    (integrableOn_kummerLaplaceRayIntegrand_neg_arg_div_two c (d - 1) hz)]
  exact setIntegral_congr_fun measurableSet_Ioi fun r hr =>
    kummerLaplaceRayIntegrand_sub_sub_one c d z (abs_neg_arg_div_two_lt_pi z) hr.out.le

private theorem tendsto_kummerLaplaceRayIntegrand_atTop (c : ℕ) (d : ℂ) {z : ℂ} {θ : ℝ}
    (hθ : |θ| < π) (hre : 0 < (z * cexp (θ * I)).re) :
    Tendsto (kummerLaplaceRayIntegrand c d z θ) atTop (𝓝 0) := by
  set η := (z * cexp (θ * I)).re / 2
  have hη : 0 < η := half_pos hre
  have h2η : 2 * η ≤ (z * cexp (θ * I)).re := by dsimp only [η]; linarith
  have hzero : Tendsto (fun r : ℝ => kummerLaplaceMajorantConst c d |θ| η * Real.exp (-η * r))
      atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hη))).const_mul
      (kummerLaplaceMajorantConst c d |θ| η)
  refine squeeze_zero_norm' ?_ hzero
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  exact norm_kummerLaplaceRayIntegrand_le c d hθ le_rfl hη h2η hr

private theorem hasDerivAt_kummerLaplaceRayIntegrand_zero (d z : ℂ) {θ r : ℝ}
    (hθ : |θ| < π) (hr : 0 ≤ r) :
    HasDerivAt (kummerLaplaceRayIntegrand 0 d z θ)
      (cexp (θ * I) * (-z * kummerLaplaceRayIntegrand 0 d z θ r +
        d * kummerLaplaceRayIntegrand 0 (d - 1) z θ r)) r := by
  set ω : ℂ := cexp (θ * I)
  unfold kummerLaplaceRayIntegrand
  simp only [pow_zero, mul_one]
  have hd1 : HasDerivAt (fun s : ℝ => cexp (-z * ((s : ℂ) * ω)))
      ((-z * ω) * cexp (-z * ((r : ℂ) * ω))) r := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (((hasDerivAt_id (r : ℂ)).mul_const ω).const_mul (-z)).cexp.comp_ofReal
  have hd2 : HasDerivAt (fun s : ℝ => (1 + (s : ℂ) * ω) ^ d)
      (d * (1 + (r : ℂ) * ω) ^ (d - 1) * ω) r := by
    simpa [mul_assoc] using
      (((hasDerivAt_id (r : ℂ)).mul_const ω).const_add 1 |>.cpow_const
        (one_add_ofReal_mul_exp_mul_I_mem_slitPlane hθ hr)).comp_ofReal
  refine (hd1.fun_mul hd2).congr_deriv ?_
  ring

/-- **Integration by parts at `c = 0`**:
`z * K(0, d; z) = 1 + d * K(0, d - 1; z)` on `slitPlane`. -/
theorem mul_kummerLaplace_zero (d : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    z * kummerLaplace 0 d z = 1 + d * kummerLaplace 0 (d - 1) z := by
  set θ₀ : ℝ := -(z.arg / 2)
  have hθ₀ : |θ₀| < π := abs_neg_arg_div_two_lt_pi z
  have hint_0 := (integrableOn_kummerLaplaceRayIntegrand_neg_arg_div_two 0 d hz).const_mul (-z)
  have hint_d :=
    (integrableOn_kummerLaplaceRayIntegrand_neg_arg_div_two 0 (d - 1) hz).const_mul d
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun r hr => hasDerivAt_kummerLaplaceRayIntegrand_zero d z hθ₀ hr)
    ((hint_0.add hint_d).const_mul (cexp (θ₀ * I)))
    (tendsto_kummerLaplaceRayIntegrand_atTop 0 d hθ₀ (re_mul_exp_neg_arg_div_two_mul_I_pos hz))
  have h0 : kummerLaplaceRayIntegrand 0 d z θ₀ 0 = 1 := by simp [kummerLaplaceRayIntegrand]
  rw [h0, zero_sub, integral_const_mul, integral_add hint_0 hint_d,
    integral_const_mul, integral_const_mul] at hftc
  rw [kummerLaplace_eq_canonical_ray, kummerLaplace_eq_canonical_ray]
  linear_combination -hftc

/-- **Integration by parts at `c + 1`**:
`z * K(c + 1, d; z) = (c + 1) * K(c, d; z) + d * K(c + 1, d - 1; z)` on `slitPlane`. -/
theorem mul_kummerLaplace_add_one (c : ℕ) (d : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    z * kummerLaplace (c + 1) d z =
      ((c : ℂ) + 1) * kummerLaplace c d z + d * kummerLaplace (c + 1) (d - 1) z := by
  induction c generalizing d with
  | zero =>
    have hdiff1 := kummerLaplace_sub_kummerLaplace_sub_one 0 (d + 1) hz
    have hdiff0 := kummerLaplace_sub_kummerLaplace_sub_one 0 d hz
    have hmul1 := mul_kummerLaplace_zero (d + 1) hz
    have hmul0 := mul_kummerLaplace_zero d hz
    simp only [add_sub_cancel_right] at hdiff1 hmul1
    simp only [Nat.cast_zero, zero_add]
    linear_combination hmul1 - hmul0 - z * hdiff1 + d * hdiff0
  | succ c ih =>
    have hdiff1 := kummerLaplace_sub_kummerLaplace_sub_one (c + 1) (d + 1) hz
    have hdiff0 := kummerLaplace_sub_kummerLaplace_sub_one (c + 1) d hz
    have hdiff_c := kummerLaplace_sub_kummerLaplace_sub_one c (d + 1) hz
    have ih1 := ih (d + 1)
    have ih0 := ih d
    simp only [add_sub_cancel_right] at hdiff1 hdiff_c ih1
    push_cast
    linear_combination ih1 - ih0 - z * hdiff1 + ((c : ℂ) + 1) * hdiff_c + d * hdiff0

/-- At `d = 0`, `kummerLaplace c 0 z` reduces to the elementary Laplace moment `c! * z⁻¹ ^ (c + 1)`
on `slitPlane`. -/
@[simp, grind =]
theorem kummerLaplace_zero_middle (c : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    kummerLaplace c 0 z = (c ! : ℂ) * z⁻¹ ^ (c + 1) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  induction c with
  | zero =>
    have h := mul_kummerLaplace_zero 0 hz
    simp only [zero_mul, add_zero] at h
    simpa using eq_inv_of_mul_eq_one_right h
  | succ c ih =>
    have h := congr_arg (z⁻¹ * ·) (mul_kummerLaplace_add_one c 0 hz)
    simp only [zero_mul, add_zero, ih, ← mul_assoc, inv_mul_cancel₀ hz0, one_mul] at h
    rw [h, Nat.factorial_succ, pow_succ]
    push_cast
    ring

end Complex
