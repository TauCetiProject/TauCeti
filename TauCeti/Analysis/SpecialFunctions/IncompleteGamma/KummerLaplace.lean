/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

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

* `Complex.kummerLaplace_eq_ray_integral` — Cauchy-Goursat ray independence: for any angle
  `|θ| < π / 2` with `0 < Re (z e^{iθ})`, the integral along `r e^{iθ}` agrees with
  `kummerLaplace c d z`.
* `Complex.kummerLaplace_eq_integral_of_re_pos` — on `0 < Re z`, `kummerLaplace c d z` equals the
  unrotated positive-axis integral `∫ t in Ioi 0, cexp (-z * t) * t ^ c * (1 + t) ^ d`.
* `Complex.kummerLaplace_zero_eq_ofReal_cpow_mul_integral` — for real `x > 0` and any `a : ℂ`,
  `kummerLaplace 0 (a - 1) x = x ^ (-a) * exp x * ∫ t in Ioi x, t ^ (a - 1) * exp (-t)`.
* `Complex.hasDerivAt_kummerLaplace`, `Complex.differentiableOn_kummerLaplace`,
  `Complex.differentiable_kummerLaplace_middle` — holomorphy on `slitPlane` in `z` (with derivative
  `-kummerLaplace (c + 1) d z`) and entirety in `d`.
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

private theorem one_add_mul_exp_I_re_ge_one {θ r : ℝ} (hθ : |θ| < π / 2) (hr : 0 ≤ r) :
    1 ≤ (1 + r * cexp (θ * I)).re := by
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  have hre : (1 + (r : ℂ) * cexp (θ * I)).re = 1 + r * Real.cos θ := by
    simp [Complex.mul_re, exp_ofReal_mul_I_re]
  rw [hre]
  nlinarith

private theorem one_add_mul_exp_I_mem_slitPlane {θ r : ℝ} (hθ : |θ| < π / 2) (hr : 0 ≤ r) :
    1 + r * cexp (θ * I) ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inl (lt_of_lt_of_le zero_lt_one (one_add_mul_exp_I_re_ge_one hθ hr)))

private theorem norm_one_add_mul_exp_I_cpow_le {θ r : ℝ} (hθ : |θ| < π / 2) (hr : 0 ≤ r)
    (d : ℂ) :
    ‖(1 + r * cexp (θ * I)) ^ d‖ ≤ Real.exp (π * |d.im|) * (1 + r) ^ ⌈d.re⌉₊ := by
  set w : ℂ := 1 + r * cexp (θ * I)
  have hw1 : 1 ≤ ‖w‖ := (one_add_mul_exp_I_re_ge_one hθ hr).trans (re_le_norm w)
  have hwu : ‖w‖ ≤ 1 + r := by
    calc ‖w‖ ≤ ‖(1 : ℂ)‖ + ‖(r : ℂ) * cexp (θ * I)‖ := norm_add_le _ _
      _ = 1 + r := by simp [norm_exp_ofReal_mul_I, abs_of_nonneg hr]
  have hrpow : ‖w‖ ^ d.re ≤ (1 + r) ^ ⌈d.re⌉₊ := by
    rcases le_or_gt d.re 0 with hd | hd
    · calc ‖w‖ ^ d.re ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hw1 hd
        _ ≤ (1 + r) ^ ⌈d.re⌉₊ := one_le_pow₀ (by linarith)
    · calc ‖w‖ ^ d.re ≤ (1 + r) ^ d.re := Real.rpow_le_rpow (norm_nonneg _) hwu hd.le
        _ ≤ (1 + r) ^ (⌈d.re⌉₊ : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil _)
        _ = (1 + r) ^ ⌈d.re⌉₊ := Real.rpow_natCast _ _
  calc ‖w ^ d‖ ≤ ‖w‖ ^ d.re / Real.exp (w.arg * d.im) := norm_cpow_le w d
    _ = ‖w‖ ^ d.re * (Real.exp (w.arg * d.im))⁻¹ := div_eq_mul_inv _ _
    _ ≤ (1 + r) ^ ⌈d.re⌉₊ * Real.exp (π * |d.im|) :=
        mul_le_mul hrpow (inv_exp_arg_mul_le_exp_pi_mul_abs w d.im) (by positivity) (by positivity)
    _ = Real.exp (π * |d.im|) * (1 + r) ^ ⌈d.re⌉₊ := mul_comm _ _

private theorem norm_kummerLaplaceRayIntegrand_le (c : ℕ) (d : ℂ) {z : ℂ} {θ η r : ℝ}
    (hθ : |θ| < π / 2) (hη : 0 < η) (hre : 2 * η ≤ (z * cexp (θ * I)).re) (hr : 0 ≤ r) :
    ‖kummerLaplaceRayIntegrand c d z θ r‖ ≤
      (Real.exp (π * |d.im|) * (((c + ⌈d.re⌉₊)! : ℝ) * Real.exp η / η ^ (c + ⌈d.re⌉₊))) *
        Real.exp (-η * r) := by
  have hexp_re : (-z * (r * cexp (θ * I))).re = -r * (z * cexp (θ * I)).re := by
    have : -z * ((r : ℂ) * cexp (θ * I)) = -(r : ℂ) * (z * cexp (θ * I)) := by ring
    rw [this, neg_mul, neg_re, re_ofReal_mul]; ring
  have hpow_exp : (1 + r) ^ (c + ⌈d.re⌉₊) ≤
      (((c + ⌈d.re⌉₊)! : ℝ) * Real.exp η / η ^ (c + ⌈d.re⌉₊)) * Real.exp (η * r) := by
    set n := c + ⌈d.re⌉₊
    have hle := Real.pow_div_factorial_le_exp (x := η * (1 + r)) (by positivity) n
    rw [mul_pow, div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos n)),
      show η * (1 + r) = η + η * r by ring, Real.exp_add] at hle
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  have hrc : ‖((r : ℂ) * cexp (θ * I)) ^ c‖ ≤ (1 + r) ^ c := by
    rw [norm_pow, norm_mul, norm_real, Real.norm_of_nonneg hr, norm_exp_ofReal_mul_I, mul_one]
    exact pow_le_pow_left₀ hr (by linarith) c
  rw [kummerLaplaceRayIntegrand, norm_mul, norm_mul, norm_exp, hexp_re]
  have hexp_le : Real.exp (-r * (z * cexp (θ * I)).re) ≤ Real.exp (-2 * η * r) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc Real.exp (-r * (z * cexp (θ * I)).re) * ‖((r : ℂ) * cexp (θ * I)) ^ c‖ *
        ‖(1 + (r : ℂ) * cexp (θ * I)) ^ d‖
      ≤ Real.exp (-2 * η * r) * (1 + r) ^ c * (Real.exp (π * |d.im|) * (1 + r) ^ ⌈d.re⌉₊) := by
        refine mul_le_mul (mul_le_mul hexp_le hrc (by positivity) (by positivity))
          (norm_one_add_mul_exp_I_cpow_le hθ hr d) (by positivity) (by positivity)
    _ = Real.exp (π * |d.im|) * ((1 + r) ^ (c + ⌈d.re⌉₊) * Real.exp (-2 * η * r)) := by
        rw [pow_add]; ring
    _ ≤ Real.exp (π * |d.im|) *
          ((((c + ⌈d.re⌉₊)! : ℝ) * Real.exp η / η ^ (c + ⌈d.re⌉₊)) * Real.exp (η * r) *
            Real.exp (-2 * η * r)) := by
        gcongr
    _ = (Real.exp (π * |d.im|) * (((c + ⌈d.re⌉₊)! : ℝ) * Real.exp η / η ^ (c + ⌈d.re⌉₊))) *
          Real.exp (-η * r) := by
        rw [mul_assoc _ (Real.exp (η * r)), ← Real.exp_add]
        ring_nf

private theorem continuousOn_kummerLaplaceRayIntegrand (c : ℕ) (d z : ℂ) {θ : ℝ}
    (hθ : |θ| < π / 2) :
    ContinuousOn (kummerLaplaceRayIntegrand c d z θ) (Ici 0) := by
  intro r hr
  unfold kummerLaplaceRayIntegrand
  refine (((continuousAt_const.mul (continuous_ofReal.continuousAt.mul continuousAt_const)).cexp.mul
    ((continuous_ofReal.continuousAt.mul continuousAt_const).pow c)).mul ?_).continuousWithinAt
  exact ((continuousAt_const.add (continuous_ofReal.continuousAt.mul continuousAt_const)).cpow
    continuousAt_const (one_add_mul_exp_I_mem_slitPlane hθ hr))

private theorem integrableOn_kummerLaplaceRayIntegrand (c : ℕ) (d : ℂ) {z : ℂ} {θ : ℝ}
    (hθ : |θ| < π / 2) (hre : 0 < (z * cexp (θ * I)).re) :
    IntegrableOn (kummerLaplaceRayIntegrand c d z θ) (Ioi 0) := by
  set η := (z * cexp (θ * I)).re / 2
  have hη : 0 < η := half_pos hre
  set C := Real.exp (π * |d.im|) * (((c + ⌈d.re⌉₊)! : ℝ) * Real.exp η / η ^ (c + ⌈d.re⌉₊))
  refine Integrable.mono' ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hη) 0).const_mul C)
    ((continuousOn_kummerLaplaceRayIntegrand c d z hθ).mono Ioi_subset_Ici_self
      |>.aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_)
  exact norm_kummerLaplaceRayIntegrand_le c d hθ hη (by dsimp only [η]; linarith) hr.out.le

private theorem canonical_angle_abs_lt {z : ℂ} (hz : z ∈ slitPlane) :
    |-(z.arg / 2)| < π / 2 := by
  rw [abs_neg, abs_div, abs_two, div_lt_div_iff_of_pos_right two_pos]
  exact abs_arg_lt_pi_of_mem_slitPlane hz

private theorem canonical_angle_re_pos {z : ℂ} (hz : z ∈ slitPlane) :
    0 < (z * cexp (((-(z.arg / 2) : ℝ) : ℂ) * I)).re := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hcos : 0 < Real.cos (z.arg / 2) :=
    Real.cos_pos_of_mem_Ioo (abs_lt.mp (by simpa using canonical_angle_abs_lt hz))
  have hpolar : z = (‖z‖ : ℂ) * cexp (z.arg * I) := (norm_mul_exp_arg_mul_I z).symm
  nth_rw 1 [hpolar]
  rw [mul_assoc, ← Complex.exp_add,
    show (z.arg : ℂ) * I + ((-(z.arg / 2) : ℝ) : ℂ) * I = ((z.arg / 2 : ℝ) : ℂ) * I by
      push_cast; ring,
    re_ofReal_mul, exp_ofReal_mul_I_re]
  exact mul_pos (norm_pos_iff.mpr hz0) hcos

/-! ### Cauchy-Goursat ray independence -/

private theorem mem_slitPlane_of_abs_lt_of_re_mul_exp_pos {z : ℂ} {θ : ℝ}
    (hθ : |θ| < π / 2) (hre : 0 < (z * cexp (θ * I)).re) : z ∈ slitPlane := by
  by_contra hz
  rw [mem_slitPlane_iff, not_or, not_lt, not_ne_iff] at hz
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo (abs_lt.mp hθ)
  have hmul : (z * cexp (θ * I)).re = z.re * Real.cos θ := by
    simp [Complex.mul_re, hz.2, exp_ofReal_mul_I_re]
  linarith [mul_nonpos_of_nonpos_of_nonneg hz.1 hcos.le]

private theorem re_mul_exp_pos_on_uIcc {z : ℂ} {θ₁ θ₂ : ℝ}
    (hθ₁ : |θ₁| < π / 2) (hre₁ : 0 < (z * cexp (θ₁ * I)).re)
    (hθ₂ : |θ₂| < π / 2) (hre₂ : 0 < (z * cexp (θ₂ * I)).re) :
    ∀ θ ∈ [[θ₁, θ₂]], |θ| < π / 2 ∧ 0 < (z * cexp (θ * I)).re := by
  have hz : z ∈ slitPlane := mem_slitPlane_of_abs_lt_of_re_mul_exp_pos hθ₁ hre₁
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have harg := abs_arg_lt_pi_of_mem_slitPlane hz
  have polar_re : ∀ θ : ℝ, (z * cexp (θ * I)).re = ‖z‖ * Real.cos (z.arg + θ) := fun θ => by
    nth_rw 1 [(norm_mul_exp_arg_mul_I z).symm]
    rw [mul_assoc, ← Complex.exp_add,
      show (z.arg : ℂ) * I + (θ : ℂ) * I = ((z.arg + θ : ℝ) : ℂ) * I by push_cast; ring,
      re_ofReal_mul, exp_ofReal_mul_I_re]
  have angle_lt : ∀ {θ : ℝ}, |θ| < π / 2 → 0 < (z * cexp (θ * I)).re → |z.arg + θ| < π / 2 := by
    intro θ hθ hpos
    rw [polar_re, mul_pos_iff_of_pos_left (norm_pos_iff.mpr hz0)] at hpos
    by_contra hge
    rw [not_lt] at hge
    have hub : |z.arg + θ| < 3 * π / 2 := by
      calc |z.arg + θ| ≤ |z.arg| + |θ| := abs_add_le _ _
        _ < π + π / 2 := add_lt_add harg hθ
        _ = 3 * π / 2 := by ring
    have hsin : 0 ≤ Real.sin (|z.arg + θ| - π / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    rw [Real.sin_sub_pi_div_two, Real.cos_abs] at hsin
    linarith
  obtain ⟨h₁l, h₁r⟩ := abs_lt.mp (angle_lt hθ₁ hre₁)
  obtain ⟨h₂l, h₂r⟩ := abs_lt.mp (angle_lt hθ₂ hre₂)
  obtain ⟨hθ₁l, hθ₁r⟩ := abs_lt.mp hθ₁
  obtain ⟨hθ₂l, hθ₂r⟩ := abs_lt.mp hθ₂
  intro θ hθ
  have hbetw : (θ₁ ≤ θ ∧ θ ≤ θ₂) ∨ (θ₂ ≤ θ ∧ θ ≤ θ₁) := by
    rcases le_total θ₁ θ₂ with hle | hle
    · left; simpa [uIcc_of_le hle] using hθ
    · right; simpa [uIcc_of_ge hle] using hθ
  rcases hbetw with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · refine ⟨abs_lt.mpr ⟨by linarith, by linarith⟩, ?_⟩
    rw [polar_re]
    exact mul_pos (norm_pos_iff.mpr hz0) (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
  · refine ⟨abs_lt.mpr ⟨by linarith, by linarith⟩, ?_⟩
    rw [polar_re]
    exact mul_pos (norm_pos_iff.mpr hz0) (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)

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

private theorem differentiableOn_kummerLaplaceLogIntegrand (c : ℕ) (d z : ℂ) :
    DifferentiableOn ℂ (kummerLaplaceLogIntegrand c d z) {w : ℂ | |w.im| < π / 2} := by
  intro w hw
  unfold kummerLaplaceLogIntegrand
  have hslit : 1 + cexp w ∈ slitPlane := by
    have : cexp w = (Real.exp w.re : ℂ) * cexp (w.im * I) := by
      conv_lhs => rw [← re_add_im w, Complex.exp_add, ← ofReal_exp]
    rw [this]
    exact one_add_mul_exp_I_mem_slitPlane hw (Real.exp_pos w.re).le
  exact ((((differentiableAt_id.const_mul _).sub
    (differentiableAt_id.cexp.const_mul z)).cexp).mul
    ((differentiableAt_const (1 : ℂ)).add differentiableAt_id.cexp |>.cpow_const hslit))
    |>.differentiableWithinAt

private theorem tendsto_vertical_right_kummerLaplaceLogIntegrand (c : ℕ) (d : ℂ) {z : ℂ}
    {θ₁ θ₂ η : ℝ} (hη : 0 < η)
    (hstrip : ∀ θ ∈ [[θ₁, θ₂]], |θ| < π / 2 ∧ 2 * η ≤ (z * cexp (θ * I)).re) :
    Tendsto (fun R : ℝ => ∫ y in θ₁..θ₂, kummerLaplaceLogIntegrand c d z ((R : ℂ) + y * I))
      atTop (𝓝 0) := by
  set C := Real.exp (π * |d.im|) * (((c + ⌈d.re⌉₊)! : ℝ) * Real.exp η / η ^ (c + ⌈d.re⌉₊))
  have hzero : Tendsto (fun R : ℝ => (C * |θ₂ - θ₁|) * Real.exp (R - η * Real.exp R))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => R - η * Real.exp R) atTop atBot := by
      have := (Real.tendsto_exp_div_pow_atTop 1).const_mul_atTop hη
      refine tendsto_atBot.mpr fun B => ?_
      filter_upwards [eventually_gt_atTop (max 0 (-B)),
        this.eventually_gt_atTop 2] with R hRB hR
      have hR0 : 0 < R := (le_max_left 0 (-B)).trans_lt hRB
      have hRB' : -B < R := (le_max_right 0 (-B)).trans_lt hRB
      rw [pow_one, mul_div_assoc', lt_div_iff₀ hR0] at hR
      linarith
    simpa using (Real.tendsto_exp_atBot.comp h1).const_mul (C * |θ₂ - θ₁|)
  refine squeeze_zero_norm' ?_ hzero
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R _
  calc ‖∫ y in θ₁..θ₂, kummerLaplaceLogIntegrand c d z ((R : ℂ) + y * I)‖
      ≤ (C * Real.exp (R - η * Real.exp R)) * |θ₂ - θ₁| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
        have hy' := uIoc_subset_uIcc hy
        rw [kummerLaplaceLogIntegrand_eq_ray, norm_mul, norm_exp_ofReal_mul_I, one_mul,
          norm_smul, Real.norm_of_nonneg (Real.exp_pos R).le]
        calc Real.exp R * ‖kummerLaplaceRayIntegrand c d z y (Real.exp R)‖
            ≤ Real.exp R * (C * Real.exp (-η * Real.exp R)) := by
              gcongr
              exact norm_kummerLaplaceRayIntegrand_le c d (hstrip y hy').1 hη (hstrip y hy').2
                (Real.exp_pos R).le
          _ = C * Real.exp (R - η * Real.exp R) := by
              rw [mul_left_comm, ← Real.exp_add]; ring_nf
    _ = (C * |θ₂ - θ₁|) * Real.exp (R - η * Real.exp R) := by ring

private theorem tendsto_vertical_left_kummerLaplaceLogIntegrand (c : ℕ) (d : ℂ) {z : ℂ}
    {θ₁ θ₂ η : ℝ} (hη : 0 < η)
    (hstrip : ∀ θ ∈ [[θ₁, θ₂]], |θ| < π / 2 ∧ 2 * η ≤ (z * cexp (θ * I)).re) :
    Tendsto (fun R : ℝ => ∫ y in θ₁..θ₂, kummerLaplaceLogIntegrand c d z (-(R : ℂ) + y * I))
      atTop (𝓝 0) := by
  set C := Real.exp (π * |d.im|) * (((c + ⌈d.re⌉₊)! : ℝ) * Real.exp η / η ^ (c + ⌈d.re⌉₊))
  have hzero : Tendsto (fun R : ℝ => (C * |θ₂ - θ₁|) * Real.exp (-R)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul (C * |θ₂ - θ₁|)
  refine squeeze_zero_norm' ?_ hzero
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R _
  calc ‖∫ y in θ₁..θ₂, kummerLaplaceLogIntegrand c d z (-(R : ℂ) + y * I)‖
      ≤ (C * Real.exp (-R)) * |θ₂ - θ₁| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
        have hy' := uIoc_subset_uIcc hy
        rw [show -(R : ℂ) = ((-R : ℝ) : ℂ) by push_cast; rfl,
          kummerLaplaceLogIntegrand_eq_ray, norm_mul, norm_exp_ofReal_mul_I, one_mul,
          norm_smul, Real.norm_of_nonneg (Real.exp_pos (-R)).le]
        calc Real.exp (-R) * ‖kummerLaplaceRayIntegrand c d z y (Real.exp (-R))‖
            ≤ Real.exp (-R) * (C * Real.exp (-η * Real.exp (-R))) := by
              gcongr
              exact norm_kummerLaplaceRayIntegrand_le c d (hstrip y hy').1 hη (hstrip y hy').2
                (Real.exp_pos (-R)).le
          _ ≤ Real.exp (-R) * (C * 1) := by
              gcongr
              exact Real.exp_le_one_iff.mpr (by nlinarith [Real.exp_pos (-R)])
          _ = C * Real.exp (-R) := by ring
    _ = (C * |θ₂ - θ₁|) * Real.exp (-R) := by ring

/-- **Ray independence of `kummerLaplace`.** For any angle `|θ| < π / 2` such that
`0 < Re (z e^{iθ})`, the rotated Laplace integral along the ray `r e^{iθ}` (`r > 0`) equals
`kummerLaplace c d z`. Note that `0 < Re (z e^{iθ})` together with `|θ| < π / 2` forces
`z ∈ slitPlane`. -/
theorem kummerLaplace_eq_ray_integral (c : ℕ) (d : ℂ) {z : ℂ} {θ : ℝ}
    (hθ : |θ| < π / 2) (hre : 0 < (z * cexp (θ * I)).re) :
    kummerLaplace c d z =
      cexp (θ * I) *
        ∫ r in Ioi (0 : ℝ),
          cexp (-z * (r * cexp (θ * I))) * (r * cexp (θ * I)) ^ c *
            (1 + r * cexp (θ * I)) ^ d := by
  have hz : z ∈ slitPlane := mem_slitPlane_of_abs_lt_of_re_mul_exp_pos hθ hre
  set θ₀ : ℝ := -(z.arg / 2)
  have hθ₀ : |θ₀| < π / 2 := canonical_angle_abs_lt hz
  have hre₀ : 0 < (z * cexp (θ₀ * I)).re := canonical_angle_re_pos hz
  have huIcc := re_mul_exp_pos_on_uIcc hθ₀ hre₀ hθ hre
  obtain ⟨θm, hθm_mem, hθm_min⟩ := isCompact_uIcc.exists_isMinOn nonempty_uIcc
    (f := fun y : ℝ => (z * cexp (y * I)).re) (by fun_prop)
  set η := (z * cexp (θm * I)).re / 2
  have hη : 0 < η := half_pos (huIcc θm hθm_mem).2
  have hstrip : ∀ y ∈ [[θ₀, θ]], |y| < π / 2 ∧ 2 * η ≤ (z * cexp (y * I)).re := fun y hy => by
    have hmin : (z * cexp (θm * I)).re ≤ (z * cexp (y * I)).re := hθm_min hy
    exact ⟨(huIcc y hy).1, by dsimp only [η]; linarith⟩
  have hlog_int : ∀ y, |y| < π / 2 → 0 < (z * cexp (y * I)).re →
      Integrable (fun x : ℝ => kummerLaplaceLogIntegrand c d z ((x : ℂ) + y * I)) ∧
      (∫ x : ℝ, kummerLaplaceLogIntegrand c d z ((x : ℂ) + y * I)) =
        cexp (y * I) * ∫ r in Ioi (0 : ℝ), kummerLaplaceRayIntegrand c d z y r :=
    fun y hy hyre => by
      simp_rw [kummerLaplaceLogIntegrand_eq_ray]
      exact ⟨((integrable_comp_exp _).mpr
        (integrableOn_kummerLaplaceRayIntegrand c d hy hyre)).const_mul _,
        by rw [integral_const_mul, integral_comp_exp]⟩
  have h₀ := hlog_int θ₀ hθ₀ hre₀
  have h₁ := hlog_int θ hθ hre
  unfold kummerLaplaceRayIntegrand at h₁
  rw [kummerLaplace_eq_canonical_ray, ← h₀.2, ← h₁.2]
  have hlim₀ := intervalIntegral_tendsto_integral h₀.1 tendsto_neg_atTop_atBot tendsto_id
  have hlim₁ := intervalIntegral_tendsto_integral h₁.1 tendsto_neg_atTop_atBot tendsto_id
  have hrect : ∀ R : ℝ,
      ((∫ x in (-R)..R, kummerLaplaceLogIntegrand c d z ((x : ℂ) + θ₀ * I)) -
        (∫ x in (-R)..R, kummerLaplaceLogIntegrand c d z ((x : ℂ) + θ * I))) +
        I • (∫ y in θ₀..θ, kummerLaplaceLogIntegrand c d z ((R : ℂ) + y * I)) -
        I • (∫ y in θ₀..θ, kummerLaplaceLogIntegrand c d z (-(R : ℂ) + y * I)) = 0 := fun R => by
    have := integral_boundary_rect_eq_zero_of_differentiableOn
      (kummerLaplaceLogIntegrand c d z) ((-R : ℝ) + θ₀ * I) ((R : ℝ) + θ * I)
      ((differentiableOn_kummerLaplaceLogIntegrand c d z).mono fun w hw =>
        (hstrip w.im (by simpa using hw.2)).1)
    simpa using this
  have hdiff_zero : Tendsto (fun R : ℝ =>
      (∫ x in (-R)..R, kummerLaplaceLogIntegrand c d z ((x : ℂ) + θ₀ * I)) -
        (∫ x in (-R)..R, kummerLaplaceLogIntegrand c d z ((x : ℂ) + θ * I))) atTop (𝓝 0) := by
    have hcomb :=
      ((tendsto_vertical_left_kummerLaplaceLogIntegrand c d hη hstrip).const_smul I).sub
        ((tendsto_vertical_right_kummerLaplaceLogIntegrand c d hη hstrip).const_smul I)
    rw [sub_self] at hcomb
    exact hcomb.congr fun R => by linear_combination -(hrect R)
  exact sub_eq_zero.mp (tendsto_nhds_unique (hlim₀.sub hlim₁) hdiff_zero)

/-- On the open right half-plane `0 < Re z`, `kummerLaplace c d z` equals the unrotated Laplace
integral along `(0, ∞)`. -/
theorem kummerLaplace_eq_integral_of_re_pos (c : ℕ) (d : ℂ) {z : ℂ} (hz : 0 < z.re) :
    kummerLaplace c d z =
      ∫ t in Ioi (0 : ℝ), cexp (-z * t) * (t : ℂ) ^ c * (1 + (t : ℂ)) ^ d := by
  have h := kummerLaplace_eq_ray_integral c d (z := z) (θ := 0)
    (by simp [Real.pi_pos]) (by simpa using hz)
  simpa using h

/-- For a positive real argument `x > 0` and any complex `a`, `kummerLaplace 0 (a - 1) x` is
`x ^ (-a) * exp x` times Euler's upper incomplete Gamma integral `∫_x^∞ t^{a-1} e^{-t} dt`. -/
theorem kummerLaplace_zero_eq_ofReal_cpow_mul_integral (a : ℂ) {x : ℝ} (hx : 0 < x) :
    kummerLaplace 0 (a - 1) x =
      (x : ℂ) ^ (-a) * cexp x * ∫ t in Ioi x, (t : ℂ) ^ (a - 1) * cexp (-t) := by
  rw [kummerLaplace_eq_integral_of_re_pos 0 (a - 1) (by simpa using hx)]
  have hsub : (∫ t in Ioi x, (t : ℂ) ^ (a - 1) * cexp (-t)) =
      ∫ r in Ioi (0 : ℝ),
        x • (((x * (1 + r) : ℝ) : ℂ) ^ (a - 1) * cexp (-((x * (1 + r) : ℝ) : ℂ))) := by
    have h1 : Ioi x = (fun r : ℝ => x * (1 + r)) '' Ioi 0 := by
      ext t
      simp only [mem_Ioi, mem_image]
      refine ⟨fun ht => ⟨t / x - 1, by rw [sub_pos, one_lt_div hx]; exact ht, ?_⟩, ?_⟩
      · field_simp; ring
      · rintro ⟨r, hr, rfl⟩; nlinarith
    have hderiv : ∀ r ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun r : ℝ => x * (1 + r)) x (Ioi 0) r := by
      intro r _
      simpa using ((hasDerivAt_id r).const_add 1 |>.const_mul x).hasDerivWithinAt
    rw [h1, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv
      (fun r₁ _ r₂ _ h => add_left_cancel (mul_left_cancel₀ hx.ne' h))]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    simp [abs_of_pos hx]
  rw [hsub, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hexp : cexp (x : ℂ) * cexp (-(x : ℂ)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hpow : (x : ℂ) ^ (-a) * (x : ℂ) * (x : ℂ) ^ (a - 1) = 1 := by
    nth_rw 2 [← cpow_one (x : ℂ)]
    rw [← cpow_add _ _ hx0, ← cpow_add _ _ hx0]
    simp
  rw [real_smul, ofReal_mul, TauCeti.ofReal_mul_cpow hx.le, ofReal_add, ofReal_one,
    show -((x : ℂ) * (1 + (r : ℂ))) = -(x : ℂ) + (-(x : ℂ) * (r : ℂ)) by ring, Complex.exp_add]
  calc cexp (-(x : ℂ) * (r : ℂ)) * (r : ℂ) ^ 0 * (1 + (r : ℂ)) ^ (a - 1)
      = 1 * 1 * (cexp (-(x : ℂ) * (r : ℂ)) * (1 + (r : ℂ)) ^ (a - 1)) := by simp
    _ = ((x : ℂ) ^ (-a) * (x : ℂ) * (x : ℂ) ^ (a - 1)) * (cexp (x : ℂ) * cexp (-(x : ℂ))) *
          (cexp (-(x : ℂ) * (r : ℂ)) * (1 + (r : ℂ)) ^ (a - 1)) := by rw [hpow, hexp]
    _ = _ := by ring

/-! ### Holomorphy in `z` and `d` -/

/-- On `slitPlane`, `z ↦ kummerLaplace c d z` has complex derivative
`-kummerLaplace (c + 1) d z`. -/
theorem hasDerivAt_kummerLaplace (c : ℕ) (d : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (kummerLaplace c d) (-kummerLaplace (c + 1) d z) z := by
  set θ₀ : ℝ := -(z.arg / 2)
  have hθ₀ : |θ₀| < π / 2 := canonical_angle_abs_lt hz
  have hre₀ : 0 < (z * cexp (θ₀ * I)).re := canonical_angle_re_pos hz
  set η := (z * cexp (θ₀ * I)).re / 4
  have hη : 0 < η := by positivity
  set U : Set ℂ := {w : ℂ | 2 * η < (w * cexp (θ₀ * I)).re}
  have hU_open : IsOpen U :=
    isOpen_lt continuous_const (continuous_re.comp (continuous_id.mul continuous_const))
  have hzU : 2 * η < (z * cexp (θ₀ * I)).re := by dsimp only [η]; linarith
  have heq : kummerLaplace c d =ᶠ[𝓝 z]
      fun w => cexp (θ₀ * I) * ∫ r in Ioi (0 : ℝ), kummerLaplaceRayIntegrand c d w θ₀ r := by
    filter_upwards [hU_open.mem_nhds hzU] with w hw
    have hw' : 2 * η < (w * cexp (θ₀ * I)).re := hw
    exact kummerLaplace_eq_ray_integral c d hθ₀ (by linarith)
  set B := Real.exp (π * |d.im|) * (((c + 1 + ⌈d.re⌉₊)! : ℝ) * Real.exp η / η ^ (c + 1 + ⌈d.re⌉₊))
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := U)
    (F := fun w r => kummerLaplaceRayIntegrand c d w θ₀ r)
    (F' := fun w r => -kummerLaplaceRayIntegrand (c + 1) d w θ₀ r)
    (bound := fun r => B * Real.exp (-η * r))
    (hU_open.mem_nhds hzU)
    (.of_forall fun w => (continuousOn_kummerLaplaceRayIntegrand c d w hθ₀).mono
      Ioi_subset_Ici_self |>.aestronglyMeasurable measurableSet_Ioi)
    (integrableOn_kummerLaplaceRayIntegrand c d hθ₀ hre₀)
    ((continuousOn_kummerLaplaceRayIntegrand (c + 1) d z hθ₀).neg.mono
      Ioi_subset_Ici_self |>.aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr w hw => ?_)
    ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hη) 0).const_mul B)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun r _ w _ => ?_)
  · have hmul := (hderiv.2.const_mul (cexp (θ₀ * I))).congr_of_eventuallyEq heq
    convert hmul using 1
    rw [integral_neg, mul_neg, kummerLaplace_eq_canonical_ray]
  · rw [norm_neg]
    exact norm_kummerLaplaceRayIntegrand_le (c + 1) d hθ₀ hη (le_of_lt hw) hr.out.le
  · unfold kummerLaplaceRayIntegrand
    set t : ℂ := (r : ℂ) * cexp (θ₀ * I)
    have hd := (((hasDerivAt_id w).neg.mul_const t).cexp.mul_const (t ^ c)).mul_const ((1 + t) ^ d)
    refine hd.congr_deriv ?_
    simp only [Pi.neg_apply, id_eq, pow_succ]
    ring

/-- For every `c : ℕ` and `d : ℂ`, `kummerLaplace c d` is holomorphic on `slitPlane`. -/
theorem differentiableOn_kummerLaplace (c : ℕ) (d : ℂ) :
    DifferentiableOn ℂ (kummerLaplace c d) slitPlane :=
  fun _ hz => (hasDerivAt_kummerLaplace c d hz).differentiableAt.differentiableWithinAt

private theorem norm_kummerLaplaceRayIntegrand_mul_log_le (c m : ℕ) {d d₀ z : ℂ} {θ η r : ℝ}
    (hθ : |θ| < π / 2) (hη : 0 < η) (hre : 2 * η ≤ (z * cexp (θ * I)).re) (hr : 0 ≤ r)
    (hd : ‖d - d₀‖ < 1) (hm : ⌈|d₀.re| + 1⌉₊ ≤ m) :
    ‖kummerLaplaceRayIntegrand c d z θ r * log (1 + r * cexp (θ * I))‖ ≤
      ((1 + π) * Real.exp (π * (|d₀.im| + 1)) *
        (((c + 1 + m)! : ℝ) * Real.exp η / η ^ (c + 1 + m))) * Real.exp (-η * r) := by
  obtain ⟨hd_re₁, hd_re₂⟩ := abs_lt.mp ((abs_re_le_norm (d - d₀)).trans_lt hd)
  obtain ⟨hd_im₁, hd_im₂⟩ := abs_lt.mp ((abs_im_le_norm (d - d₀)).trans_lt hd)
  rw [sub_re] at hd_re₁ hd_re₂; rw [sub_im] at hd_im₁ hd_im₂
  have hd_re : ⌈d.re⌉₊ ≤ m := (Nat.ceil_mono (by linarith [le_abs_self d₀.re])).trans hm
  have hd_im : |d.im| ≤ |d₀.im| + 1 :=
    abs_le.mpr ⟨by linarith [neg_abs_le d₀.im], by linarith [le_abs_self d₀.im]⟩
  set w : ℂ := 1 + r * cexp (θ * I)
  have hw1 : 1 ≤ ‖w‖ := (one_add_mul_exp_I_re_ge_one hθ hr).trans (re_le_norm w)
  have hwu : ‖w‖ ≤ 1 + r :=
    (norm_add_le _ _).trans_eq (by simp [norm_exp_ofReal_mul_I, abs_of_nonneg hr])
  have hlog_le : ‖log w‖ ≤ (1 + π) * (1 + r) := by
    have hlr : |Real.log ‖w‖| ≤ r := by
      rw [abs_of_nonneg (Real.log_nonneg hw1)]
      exact (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hw1)).trans (by linarith)
    calc ‖log w‖ ≤ |(log w).re| + |(log w).im| := norm_le_abs_re_add_abs_im (log w)
      _ = |Real.log ‖w‖| + |w.arg| := by rw [log_re, log_im]
      _ ≤ (1 + π) * (1 + r) := by nlinarith [abs_arg_le_pi w, Real.pi_pos]
  have hexp_re : (-z * (r * cexp (θ * I))).re = -r * (z * cexp (θ * I)).re := by
    rw [show -z * ((r : ℂ) * cexp (θ * I)) = -(r : ℂ) * (z * cexp (θ * I)) by ring,
      neg_mul, neg_re, re_ofReal_mul]; ring
  have hpow_exp : (1 + r) ^ (c + 1 + m) ≤
      (((c + 1 + m)! : ℝ) * Real.exp η / η ^ (c + 1 + m)) * Real.exp (η * r) := by
    have hle := Real.pow_div_factorial_le_exp (x := η * (1 + r)) (by positivity) (c + 1 + m)
    rw [mul_pow, div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos _)),
      show η * (1 + r) = η + η * r by ring, Real.exp_add] at hle
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; linarith
  have hrc : ‖((r : ℂ) * cexp (θ * I)) ^ c‖ ≤ (1 + r) ^ c := by
    rw [norm_pow, norm_mul, norm_real, Real.norm_of_nonneg hr, norm_exp_ofReal_mul_I, mul_one]
    exact pow_le_pow_left₀ hr (by linarith) c
  have hw_cpow : ‖w ^ d‖ ≤ Real.exp (π * (|d₀.im| + 1)) * (1 + r) ^ m :=
    (norm_one_add_mul_exp_I_cpow_le hθ hr d).trans <|
      mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd_im Real.pi_pos.le))
        (pow_le_pow_right₀ (by linarith) hd_re) (by positivity) (by positivity)
  rw [norm_mul, kummerLaplaceRayIntegrand, norm_mul, norm_mul, norm_exp, hexp_re]
  calc Real.exp (-r * (z * cexp (θ * I)).re) * ‖((r : ℂ) * cexp (θ * I)) ^ c‖ * ‖w ^ d‖ * ‖log w‖
      ≤ Real.exp (-2 * η * r) * (1 + r) ^ c *
          (Real.exp (π * (|d₀.im| + 1)) * (1 + r) ^ m) * ((1 + π) * (1 + r)) :=
        mul_le_mul (mul_le_mul (mul_le_mul (Real.exp_le_exp.mpr (by nlinarith)) hrc
          (by positivity) (by positivity)) hw_cpow (by positivity) (by positivity))
          hlog_le (norm_nonneg _) (by positivity)
    _ = (1 + π) * Real.exp (π * (|d₀.im| + 1)) *
          ((1 + r) ^ (c + 1 + m) * Real.exp (-2 * η * r)) := by rw [pow_add, pow_add, pow_one]; ring
    _ ≤ (1 + π) * Real.exp (π * (|d₀.im| + 1)) *
          ((((c + 1 + m)! : ℝ) * Real.exp η / η ^ (c + 1 + m)) * Real.exp (η * r) *
            Real.exp (-2 * η * r)) := by gcongr
    _ = ((1 + π) * Real.exp (π * (|d₀.im| + 1)) *
          (((c + 1 + m)! : ℝ) * Real.exp η / η ^ (c + 1 + m))) * Real.exp (-η * r) := by
        rw [mul_assoc _ (Real.exp (η * r)), ← Real.exp_add]; ring_nf

/-- For every `c : ℕ` and `z ∈ slitPlane`, `d ↦ kummerLaplace c d z` is entire. -/
theorem differentiable_kummerLaplace_middle (c : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    Differentiable ℂ fun d => kummerLaplace c d z := by
  intro d₀
  set θ₀ : ℝ := -(z.arg / 2)
  have hθ₀ : |θ₀| < π / 2 := canonical_angle_abs_lt hz
  have hre₀ : 0 < (z * cexp (θ₀ * I)).re := canonical_angle_re_pos hz
  set η := (z * cexp (θ₀ * I)).re / 4
  have hη : 0 < η := by positivity
  have h2η : 2 * η ≤ (z * cexp (θ₀ * I)).re := by dsimp only [η]; linarith
  set m : ℕ := ⌈|d₀.re| + 1⌉₊
  set K : ℝ := (1 + π) * Real.exp (π * (|d₀.im| + 1)) *
    (((c + 1 + m)! : ℝ) * Real.exp η / η ^ (c + 1 + m))
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Metric.ball d₀ 1)
    (F := fun d r => kummerLaplaceRayIntegrand c d z θ₀ r)
    (F' := fun d r => kummerLaplaceRayIntegrand c d z θ₀ r * log (1 + r * cexp (θ₀ * I)))
    (bound := fun r => K * Real.exp (-η * r))
    (Metric.ball_mem_nhds d₀ one_pos)
    (.of_forall fun d => (continuousOn_kummerLaplaceRayIntegrand c d z hθ₀).mono
      Ioi_subset_Ici_self |>.aestronglyMeasurable measurableSet_Ioi)
    (integrableOn_kummerLaplaceRayIntegrand c d₀ hθ₀ hre₀)
    (((continuousOn_kummerLaplaceRayIntegrand c d₀ z hθ₀).mul fun r hr =>
        ((continuousAt_const.add (continuous_ofReal.continuousAt.mul continuousAt_const)).clog
          (one_add_mul_exp_I_mem_slitPlane hθ₀ hr)).continuousWithinAt).mono
      Ioi_subset_Ici_self |>.aestronglyMeasurable measurableSet_Ioi)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr d hd =>
      norm_kummerLaplaceRayIntegrand_mul_log_le c m hθ₀ hη h2η hr.out.le
        (by simpa [dist_eq_norm] using hd) le_rfl)
    ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hη) 0).const_mul K)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr d _ => ?_)
  · simp_rw [kummerLaplace_eq_canonical_ray]
    exact (hderiv.2.const_mul (cexp (θ₀ * I))).differentiableAt
  · unfold kummerLaplaceRayIntegrand
    have hw0 : 1 + (r : ℂ) * cexp (θ₀ * I) ≠ 0 :=
      slitPlane_ne_zero (one_add_mul_exp_I_mem_slitPlane hθ₀ hr.out.le)
    simpa [mul_assoc] using
      ((hasDerivAt_id d).const_cpow (Or.inl hw0)).const_mul
        (cexp (-z * (r * cexp (θ₀ * I))) * (r * cexp (θ₀ * I)) ^ c)

/-! ### Contiguous and integration-by-parts recurrences -/

/-- **Contiguous difference relation**:
`K(c, d; z) - K(c, d - 1; z) = K(c + 1, d - 1; z)` on `slitPlane`. -/
theorem kummerLaplace_sub_kummerLaplace_sub_one (c : ℕ) (d : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    kummerLaplace c d z - kummerLaplace c (d - 1) z = kummerLaplace (c + 1) (d - 1) z := by
  set θ₀ : ℝ := -(z.arg / 2)
  have hθ₀ : |θ₀| < π / 2 := canonical_angle_abs_lt hz
  have hre₀ : 0 < (z * cexp (θ₀ * I)).re := canonical_angle_re_pos hz
  rw [kummerLaplace_eq_canonical_ray, kummerLaplace_eq_canonical_ray,
    kummerLaplace_eq_canonical_ray, ← mul_sub]
  congr 1
  rw [← integral_sub (integrableOn_kummerLaplaceRayIntegrand c d hθ₀ hre₀)
    (integrableOn_kummerLaplaceRayIntegrand c (d - 1) hθ₀ hre₀)]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  unfold kummerLaplaceRayIntegrand
  set t : ℂ := (r : ℂ) * cexp (θ₀ * I)
  have ht1 : 1 + t ≠ 0 := slitPlane_ne_zero (one_add_mul_exp_I_mem_slitPlane hθ₀ hr.out.le)
  have hpow : (1 + t) ^ d = (1 + t) ^ (d - 1) * (1 + t) := by
    conv_lhs => rw [show d = d - 1 + 1 by ring]
    rw [cpow_add _ _ ht1, cpow_one]
  rw [hpow, pow_succ]
  ring

private theorem tendsto_kummerLaplaceRayIntegrand_atTop (c : ℕ) (d : ℂ) {z : ℂ} {θ : ℝ}
    (hθ : |θ| < π / 2) (hre : 0 < (z * cexp (θ * I)).re) :
    Tendsto (kummerLaplaceRayIntegrand c d z θ) atTop (𝓝 0) := by
  set η := (z * cexp (θ * I)).re / 2
  have hη : 0 < η := half_pos hre
  have h2η : 2 * η ≤ (z * cexp (θ * I)).re := by dsimp only [η]; linarith
  set C := Real.exp (π * |d.im|) * (((c + ⌈d.re⌉₊)! : ℝ) * Real.exp η / η ^ (c + ⌈d.re⌉₊))
  have hzero : Tendsto (fun r : ℝ => C * Real.exp (-η * r)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hη))).const_mul C
  refine squeeze_zero_norm' ?_ hzero
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  exact norm_kummerLaplaceRayIntegrand_le c d hθ hη h2η hr

/-- **Integration by parts at `c = 0`**:
`z * K(0, d; z) = 1 + d * K(0, d - 1; z)` on `slitPlane`. -/
theorem mul_kummerLaplace_zero (d : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    z * kummerLaplace 0 d z = 1 + d * kummerLaplace 0 (d - 1) z := by
  set θ₀ : ℝ := -(z.arg / 2)
  set ω : ℂ := cexp (θ₀ * I)
  have hθ₀ : |θ₀| < π / 2 := canonical_angle_abs_lt hz
  have hre₀ : 0 < (z * ω).re := canonical_angle_re_pos hz
  have hderiv : ∀ r ∈ Ici (0 : ℝ),
      HasDerivAt (kummerLaplaceRayIntegrand 0 d z θ₀)
        (ω * (-z * kummerLaplaceRayIntegrand 0 d z θ₀ r +
          d * kummerLaplaceRayIntegrand 0 (d - 1) z θ₀ r)) r := by
    intro r hr
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
          (one_add_mul_exp_I_mem_slitPlane hθ₀ hr)).comp_ofReal
    refine (hd1.fun_mul hd2).congr_deriv ?_
    ring
  have hint_0 := (integrableOn_kummerLaplaceRayIntegrand 0 d hθ₀ hre₀).const_mul (-z)
  have hint_d := (integrableOn_kummerLaplaceRayIntegrand 0 (d - 1) hθ₀ hre₀).const_mul d
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv ((hint_0.add hint_d).const_mul ω)
    (tendsto_kummerLaplaceRayIntegrand_atTop 0 d hθ₀ hre₀)
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
  set θ₀ : ℝ := -(z.arg / 2)
  set ω : ℂ := cexp (θ₀ * I)
  have hθ₀ : |θ₀| < π / 2 := canonical_angle_abs_lt hz
  have hre₀ : 0 < (z * ω).re := canonical_angle_re_pos hz
  have hderiv : ∀ r ∈ Ici (0 : ℝ),
      HasDerivAt (kummerLaplaceRayIntegrand (c + 1) d z θ₀)
        (ω * (-z * kummerLaplaceRayIntegrand (c + 1) d z θ₀ r +
          (((c : ℂ) + 1) * kummerLaplaceRayIntegrand c d z θ₀ r +
            d * kummerLaplaceRayIntegrand (c + 1) (d - 1) z θ₀ r))) r := by
    intro r hr
    unfold kummerLaplaceRayIntegrand
    have hd1 : HasDerivAt (fun s : ℝ => cexp (-z * ((s : ℂ) * ω)))
        ((-z * ω) * cexp (-z * ((r : ℂ) * ω))) r := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (((hasDerivAt_id (r : ℂ)).mul_const ω).const_mul (-z)).cexp.comp_ofReal
    have hd2 : HasDerivAt (fun s : ℝ => ((s : ℂ) * ω) ^ (c + 1))
        (((c : ℂ) + 1) * ((r : ℂ) * ω) ^ c * ω) r := by
      simpa [Nat.cast_add, Nat.cast_one] using
        (((hasDerivAt_id (r : ℂ)).mul_const ω).pow (c + 1)).comp_ofReal
    have hd3 : HasDerivAt (fun s : ℝ => (1 + (s : ℂ) * ω) ^ d)
        (d * (1 + (r : ℂ) * ω) ^ (d - 1) * ω) r := by
      simpa [mul_assoc] using
        (((hasDerivAt_id (r : ℂ)).mul_const ω).const_add 1 |>.cpow_const
          (one_add_mul_exp_I_mem_slitPlane hθ₀ hr)).comp_ofReal
    refine ((hd1.fun_mul hd2).fun_mul hd3).congr_deriv ?_
    simp only [pow_succ, show d - 1 = -1 + d by ring]
    ring
  have hint_c1 := (integrableOn_kummerLaplaceRayIntegrand (c + 1) d hθ₀ hre₀).const_mul (-z)
  have hint_c := (integrableOn_kummerLaplaceRayIntegrand c d hθ₀ hre₀).const_mul ((c : ℂ) + 1)
  have hint_d := (integrableOn_kummerLaplaceRayIntegrand (c + 1) (d - 1) hθ₀ hre₀).const_mul d
  have hint_cd : IntegrableOn
      (fun r => ((c : ℂ) + 1) * kummerLaplaceRayIntegrand c d z θ₀ r +
        d * kummerLaplaceRayIntegrand (c + 1) (d - 1) z θ₀ r) (Ioi 0) := hint_c.add hint_d
  have hftc := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    ((hint_c1.add hint_cd).const_mul ω)
    (tendsto_kummerLaplaceRayIntegrand_atTop (c + 1) d hθ₀ hre₀)
  have h0 : kummerLaplaceRayIntegrand (c + 1) d z θ₀ 0 = 0 := by
    simp [kummerLaplaceRayIntegrand]
  rw [h0, sub_zero, integral_const_mul, integral_add hint_c1 hint_cd,
    integral_add hint_c hint_d, integral_const_mul, integral_const_mul, integral_const_mul] at hftc
  rw [kummerLaplace_eq_canonical_ray, kummerLaplace_eq_canonical_ray,
    kummerLaplace_eq_canonical_ray]
  linear_combination -hftc

/-- At `d = 0`, `kummerLaplace c 0 z` reduces to the elementary Laplace moment `c! * z⁻¹ ^ (c + 1)`
on `slitPlane`. -/
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
