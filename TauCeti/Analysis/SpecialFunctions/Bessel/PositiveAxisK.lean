/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import TauCeti.Analysis.MellinTransform.Basic
import TauCeti.Analysis.SpecialFunctions.Hyperbolic
import TauCeti.Analysis.SpecialFunctions.MacdonaldIntegral

/-!
# The K-Bessel kernel on the positive axis

For a complex order `ν` and a real argument `c`, this file defines

`K_ν(c) = ½ ∫₀^∞ exp(−c (u + u⁻¹) / 2) exp(ν log u) du / u`,

the modified Bessel function of the second kind (Macdonald's function) on the positive axis
`c > 0`, in the integral form of DLMF 10.32.10 after the substitution `t = c / (2u)`. For `c > 0`
the integral converges absolutely, because the factor `exp(−c (u + u⁻¹) / 2)` vanishes to
infinite order at both ends of `(0, ∞)`; for `c ≤ 0` it diverges, and `K_ν(c) = 0`.

The definition is half the Mellin transform at `ν` of `u ↦ exp(−(c / 2)(u + u⁻¹))`, and most of
its theory is read off from that. The substitution `u = e^t` gives
`K_ν(c) = ½ ∫_ℝ e^{ν t} e^{−c cosh t} dt`, and pairing `t` with `−t` gives Schläfli's cosh
form `K_ν(c) = ∫₀^∞ e^{−c cosh t} cosh(ν t) dt` (DLMF 10.32.9). The symmetry `u ↦ u⁻¹` of the
kernel gives the evenness `K_{−ν} = K_ν` (DLMF 10.27.3). For real order the integrand is
positive, so `K_σ(c)` is real and positive for `c > 0`, and `|K_ν(c)| ≤ K_{Re ν}(c)`. With
`cosh t ≥ 1 + t² / 2` the full-line form is dominated by a Gaussian integral, which gives the
decay `|K_ν(c)| ≤ (π / (2c))^{1/2} e^{(Re ν)² / (2c) − c}`, and the substitution
`s = 2 sinh(t / 2)` evaluates the half-integer order `K_{1/2}(c) = (π / (2c))^{1/2} e^{−c}`
(DLMF 10.39.2). Finally, the Mellin transform is holomorphic in its variable wherever it
converges, so `ν ↦ K_ν(c)` is entire, and its `j`-th derivative inserts `(log u)^j` into the
defining integral.

The kernel `K_ν(c)` at `c = 2π |n| y` is the Bessel factor of the nonconstant Fourier
coefficients of the nonholomorphic Eisenstein series for `SL₂(ℤ)`. On the positive axis it agrees
with Macdonald's function `K_ν(z)`, which is holomorphic on the plane cut along `(−∞, 0]`.

## Main definitions

* `Complex.positiveAxisBesselK`: the K-Bessel kernel `K_ν(c)`.

## Main results

* `Complex.integrableOn_positiveAxisBesselK_integrand`, `Complex.positiveAxisBesselK_of_nonpos`:
  the defining integral converges absolutely for `c > 0`, and `K_ν(c) = 0` for `c ≤ 0`.
* `Complex.positiveAxisBesselK_eq_mellin`, `Complex.positiveAxisBesselK_eq_integral`,
  `Complex.positiveAxisBesselK_eq_integral_cosh`: the Mellin form, the full-line form
  `½ ∫_ℝ e^{ν t} e^{−c cosh t} dt` and the cosh form (DLMF 10.32.9).
* `Complex.positiveAxisBesselK_neg`: `K_{−ν}(c) = K_ν(c)` (DLMF 10.27.3).
* `Complex.positiveAxisBesselK_ofReal_eq_integral`, `Complex.im_positiveAxisBesselK_ofReal`,
  `Complex.re_positiveAxisBesselK_ofReal_pos`: `K_σ(c)` is real for real `σ`, and positive for
  `c > 0`.
* `Complex.norm_positiveAxisBesselK_le`: `|K_ν(c)| ≤ K_{Re ν}(c)`.
* `Complex.norm_positiveAxisBesselK_le_sqrt_mul_exp`,
  `Complex.norm_positiveAxisBesselK_le_rpow_mul_exp`, `Complex.exists_norm_positiveAxisBesselK_le`:
  the decay `|K_ν(x)| ≤ C x^{−1/2} e^{−x}` for `x ≥ 1`, uniformly for `ν` with bounded real part.
* `Complex.positiveAxisBesselK_one_half`: `K_{1/2}(c) = (π / (2c))^{1/2} e^{−c}` (DLMF 10.39.2).
* `Complex.differentiable_positiveAxisBesselK`, `Complex.hasDerivAt_positiveAxisBesselK`,
  `Complex.iteratedDeriv_positiveAxisBesselK`: `ν ↦ K_ν(c)` is entire, and its `j`-th
  derivative is `½ ∫₀^∞ (log u)^j exp(−c (u + u⁻¹) / 2) exp(ν log u) du / u`.

## References

* NIST *Digital Library of Mathematical Functions*, equations 10.27.3, 10.32.9, 10.32.10 and
  10.39.2, <https://dlmf.nist.gov/10.27>, <https://dlmf.nist.gov/10.32>,
  <https://dlmf.nist.gov/10.39>.
* G. N. Watson, *A Treatise on the Theory of Bessel Functions*, 2nd ed., Cambridge University
  Press, 1944, §§3.7, 6.22.
-/

public section

noncomputable section

open Real Set MeasureTheory Filter Topology Asymptotics
open Complex hiding exp continuous_exp

namespace Complex

/-- The **K-Bessel kernel** `K_ν(c) = ½ ∫₀^∞ exp(−c (u + u⁻¹) / 2) exp(ν log u) du / u` for a
complex order `ν` and a real argument `c`, with the real logarithm on `u > 0`. This is the modified
Bessel function of the second kind on the positive axis `c > 0`; for `c ≤ 0` the integral
diverges and the value is `0`. -/
def positiveAxisBesselK (ν : ℂ) (c : ℝ) : ℂ :=
  (1 / 2 : ℂ) * ∫ u : ℝ in Ioi 0,
    cexp (-(c : ℂ) * ((u : ℂ) + (u : ℂ)⁻¹) / 2) * cexp (ν * (Real.log u : ℂ)) / (u : ℂ)

theorem positiveAxisBesselK_def (ν : ℂ) (c : ℝ) :
    positiveAxisBesselK ν c = (1 / 2 : ℂ) * ∫ u : ℝ in Ioi 0,
      cexp (-(c : ℂ) * ((u : ℂ) + (u : ℂ)⁻¹) / 2) * cexp (ν * (Real.log u : ℂ)) / (u : ℂ) :=
  (rfl)

/-- On `(0, ∞)` the integrand of `positiveAxisBesselK` is the Mellin integrand of
`u ↦ exp(−(c / 2)(u + u⁻¹))` at `ν`. -/
private lemma integrand_eq_cpow_smul (ν : ℂ) (c : ℝ) {u : ℝ} (hu : 0 < u) :
    cexp (-(c : ℂ) * ((u : ℂ) + (u : ℂ)⁻¹) / 2) * cexp (ν * (Real.log u : ℂ)) / (u : ℂ) =
      (u : ℂ) ^ (ν - 1) • ((Real.exp (-(c / 2 * (u + u⁻¹))) : ℝ) : ℂ) := by
  have hu' : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
  rw [smul_eq_mul, cpow_sub _ _ hu', cpow_one, cpow_def_of_ne_zero hu', ← ofReal_log hu.le,
    ofReal_exp]
  push_cast
  ring_nf

/-- **The Mellin form.** `K_ν(c)` is half the Mellin transform at `ν` of
`u ↦ exp(−(c / 2)(u + u⁻¹))`. -/
theorem positiveAxisBesselK_eq_mellin (ν : ℂ) (c : ℝ) :
    positiveAxisBesselK ν c =
      1 / 2 * mellin (fun u : ℝ ↦ ((Real.exp (-(c / 2 * (u + u⁻¹))) : ℝ) : ℂ)) ν := by
  rw [positiveAxisBesselK, mellin]
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ integrand_eq_cpow_smul ν c hu

/-- For `c > 0` the integral defining `K_ν(c)` converges absolutely. -/
theorem integrableOn_positiveAxisBesselK_integrand (ν : ℂ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun u : ℝ ↦
      cexp (-(c : ℂ) * ((u : ℂ) + (u : ℂ)⁻¹) / 2) * cexp (ν * (Real.log u : ℂ)) / (u : ℂ))
      (Ioi 0) :=
  IntegrableOn.congr_fun (mellinConvergent_exp_neg_mul_add_inv hc ν)
    (fun _ hu ↦ (integrand_eq_cpow_smul ν c hu).symm) measurableSet_Ioi

/-- **The full-line form.** The substitution `u = e^t` gives
`K_ν(c) = ½ ∫_ℝ e^{ν t} e^{−c cosh t} dt`, for every `c`. -/
theorem positiveAxisBesselK_eq_integral (ν : ℂ) (c : ℝ) :
    positiveAxisBesselK ν c =
      1 / 2 * ∫ t : ℝ, cexp (ν * t) * cexp (-((c : ℂ) * Real.cosh t)) := by
  rw [positiveAxisBesselK_eq_mellin, mellin_exp_neg_mul_add_inv, ← integral_neg_eq_self]
  simp only [ofReal_neg, Real.cosh_neg, neg_mul_neg]

/-- **Schläfli's cosh form** (DLMF 10.32.9): for `c > 0`,
`K_ν(c) = ∫₀^∞ e^{−c cosh t} cosh(ν t) dt`. -/
theorem positiveAxisBesselK_eq_integral_cosh (ν : ℂ) {c : ℝ} (hc : 0 < c) :
    positiveAxisBesselK ν c =
      ∫ t in Ioi (0 : ℝ), cexp (-((c : ℂ) * Real.cosh t)) * Complex.cosh (ν * t) := by
  rw [positiveAxisBesselK_eq_integral,
    integral_exp_mul_mul_exp_neg_mul_cosh (by simpa using hc)]
  ring

/-- **Evenness in the order** (DLMF 10.27.3): `K_{−ν}(c) = K_ν(c)`, from the symmetry
`u ↦ u⁻¹` of the kernel `exp(−(c / 2)(u + u⁻¹))`. -/
@[simp]
theorem positiveAxisBesselK_neg (ν : ℂ) (c : ℝ) :
    positiveAxisBesselK (-ν) c = positiveAxisBesselK ν c := by
  rw [positiveAxisBesselK_eq_mellin, positiveAxisBesselK_eq_mellin, ← mellin_comp_inv]
  simp only [inv_inv, add_comm]

/-! ### The kernels `(log u)^j e^{−(c / 2)(u + u⁻¹)}` -/

/-- The Mellin integrand `(log u)^j e^{−(c / 2)(u + u⁻¹)}` of the `j`-th derivative in the order of
`2 K_ν(c)`. -/
private def logPowKernel (j : ℕ) (c : ℝ) (u : ℝ) : ℂ :=
  Real.log u ^ j • ((Real.exp (-(c / 2 * (u + u⁻¹))) : ℝ) : ℂ)

private lemma logPowKernel_zero (c : ℝ) :
    logPowKernel 0 c = fun u : ℝ ↦ ((Real.exp (-(c / 2 * (u + u⁻¹))) : ℝ) : ℂ) := by
  ext u
  simp [logPowKernel]

/-- The Mellin transform of `logPowKernel j c` is the defining integral of `2 K_ν(c)` with
`(log u)^j` inserted. -/
private lemma mellin_logPowKernel (j : ℕ) (ν : ℂ) (c : ℝ) :
    mellin (logPowKernel j c) ν = ∫ u : ℝ in Ioi 0, (Real.log u : ℂ) ^ j *
      (cexp (-(c : ℂ) * ((u : ℂ) + (u : ℂ)⁻¹) / 2) * cexp (ν * (Real.log u : ℂ)) / (u : ℂ)) := by
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ ?_
  rw [integrand_eq_cpow_smul ν c hu, logPowKernel, smul_comm, real_smul, ofReal_pow]

/-- For `c ≤ 0` the Mellin transform of `logPowKernel j c` diverges everywhere, so it is `0`: in
logarithmic coordinates `u = e^{−t}` its integrand has modulus at least `1` on a half-line. -/
private lemma mellin_logPowKernel_of_nonpos (j : ℕ) {c : ℝ} (hc : c ≤ 0) (ν : ℂ) :
    mellin (logPowKernel j c) ν = 0 := by
  rw [TauCeti.mellin_eq_integral_exp_smul]
  refine integral_undef fun hF ↦ ?_
  set S : Set ℝ := if 0 ≤ ν.re then Iic (-1) else Ici 1
  have hsub : S ⊆ {t | 1 ≤ ‖cexp (-ν * t) • logPowKernel j c (Real.exp (-t))‖} := by
    intro t ht
    have h1 : 1 ≤ |t| ∧ 0 ≤ -(ν.re * t) := by
      simp only [S] at ht
      split_ifs at ht with h
      · exact ⟨by rw [abs_of_neg (by linarith [mem_Iic.mp ht])]; linarith [mem_Iic.mp ht],
          by nlinarith [mem_Iic.mp ht]⟩
      · exact ⟨by rw [abs_of_pos (by linarith [mem_Ici.mp ht])]; exact mem_Ici.mp ht,
          by nlinarith [mem_Ici.mp ht]⟩
    have hexp : 0 ≤ -(c / 2 * (Real.exp (-t) + (Real.exp (-t))⁻¹)) :=
      neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity))
    simp only [mem_ofPred_eq, logPowKernel, norm_smul, Complex.norm_exp, neg_mul, neg_re, mul_re,
      ofReal_re, ofReal_im, mul_zero, sub_zero, Real.log_exp, norm_pow, Real.norm_eq_abs, abs_neg,
      norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_exp h1.2)
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ h1.1) (Real.one_le_exp hexp))
  have h := (measure_mono hsub).trans_lt (hF.measure_norm_ge_lt_top one_pos)
  simp only [S] at h
  split_ifs at h <;> simp [Real.volume_Ici, Real.volume_Iic] at h

/-- For `c ≤ 0` the defining integral diverges, and `K_ν(c) = 0`. -/
theorem positiveAxisBesselK_of_nonpos (ν : ℂ) {c : ℝ} (hc : c ≤ 0) :
    positiveAxisBesselK ν c = 0 := by
  rw [positiveAxisBesselK_eq_mellin, ← logPowKernel_zero, mellin_logPowKernel_of_nonpos 0 hc,
    mul_zero]

/-- `(π / (c / 2))^{1/2} = 2 (π / (2c))^{1/2}`, the constant of the Gaussian integrals below. -/
private lemma sqrt_pi_div_half (c : ℝ) : √(π / (c / 2)) = 2 * √(π / (2 * c)) := by
  rw [show π / (c / 2) = 2 ^ 2 * (π / (2 * c)) by field_simp,
    Real.sqrt_mul (by positivity), Real.sqrt_sq zero_le_two]

/-- For a real order `σ`, `K_σ(c)` is the real number `½ ∫_ℝ e^{σ t} e^{−c cosh t} dt`. -/
theorem positiveAxisBesselK_ofReal_eq_integral (σ c : ℝ) :
    positiveAxisBesselK σ c =
      ((1 / 2 * ∫ t : ℝ, Real.exp (σ * t) * Real.exp (-(c * Real.cosh t)) : ℝ) : ℂ) := by
  rw [positiveAxisBesselK_eq_integral, ofReal_mul, ← integral_complex_ofReal]
  push_cast
  ring_nf

/-- For a real order `σ`, `K_σ(c)` is real. -/
@[simp]
theorem im_positiveAxisBesselK_ofReal (σ c : ℝ) : (positiveAxisBesselK σ c).im = 0 := by
  rw [positiveAxisBesselK_ofReal_eq_integral, ofReal_im]

/-- For a real order `σ` and `c > 0`, `K_σ(c)` is positive. -/
theorem re_positiveAxisBesselK_ofReal_pos (σ : ℝ) {c : ℝ} (hc : 0 < c) :
    0 < (positiveAxisBesselK σ c).re := by
  rw [positiveAxisBesselK_ofReal_eq_integral, ofReal_re]
  refine mul_pos one_half_pos ((integral_pos_iff_support_of_nonneg (fun _ ↦ by positivity)
    (Real.integrable_exp_mul_mul_exp_neg_mul_cosh σ hc)).mpr ?_)
  rw [Function.support_eq_univ (fun t ↦ by positivity), Measure.measure_univ_pos]
  exact NeZero.ne volume

/-- `|K_ν(c)| ≤ K_{Re ν}(c)`: the modulus of the kernel is bounded by the kernel of the real
part of the order. -/
theorem norm_positiveAxisBesselK_le (ν : ℂ) (c : ℝ) :
    ‖positiveAxisBesselK ν c‖ ≤ (positiveAxisBesselK ν.re c).re := by
  rw [positiveAxisBesselK_ofReal_eq_integral, ofReal_re, positiveAxisBesselK_eq_integral,
    norm_mul]
  refine (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)).trans_eq ?_
  congr 1
  · norm_num
  · refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    simp [Complex.norm_exp]

/-- **Decay of the kernel.** `|K_ν(c)| ≤ (π / (2c))^{1/2} e^{(Re ν)² / (2c) − c}`: for `c > 0`,
by `cosh t ≥ 1 + t² / 2`, the full-line form is dominated by a Gaussian integral. -/
theorem norm_positiveAxisBesselK_le_sqrt_mul_exp (ν : ℂ) (c : ℝ) :
    ‖positiveAxisBesselK ν c‖ ≤ √(π / (2 * c)) * Real.exp (ν.re ^ 2 / (2 * c) - c) := by
  rcases le_or_gt c 0 with hc | hc
  · rw [positiveAxisBesselK_of_nonpos ν hc, norm_zero]
    positivity
  refine (norm_positiveAxisBesselK_le ν c).trans ?_
  rw [positiveAxisBesselK_ofReal_eq_integral, ofReal_re]
  set σ := ν.re
  set E := Real.exp (σ ^ 2 / (2 * c) - c)
  have hg : Integrable fun t : ℝ ↦ E * Real.exp (-(c / 2) * (t - σ / c) ^ 2) :=
    ((integrable_exp_neg_mul_sq (half_pos hc)).comp_sub_right (σ / c)).const_mul _
  calc 1 / 2 * ∫ t, Real.exp (σ * t) * Real.exp (-(c * Real.cosh t))
      ≤ 1 / 2 * ∫ t, E * Real.exp (-(c / 2) * (t - σ / c) ^ 2) := by
        refine mul_le_mul_of_nonneg_left (integral_mono
          (Real.integrable_exp_mul_mul_exp_neg_mul_cosh σ hc) hg fun t ↦ ?_) one_half_pos.le
        have h : σ ^ 2 / (2 * c) - c + -(c / 2) * (t - σ / c) ^ 2 =
            σ * t - c * (1 + t ^ 2 / 2) := by
          field_simp
          ring
        rw [← Real.exp_add, ← Real.exp_add, h, Real.exp_le_exp]
        nlinarith [Real.one_add_sq_div_two_le_cosh t]
    _ = √(π / (2 * c)) * E := by
        rw [integral_const_mul,
          integral_sub_right_eq_self (fun t ↦ Real.exp (-(c / 2) * t ^ 2)) (σ / c),
          integral_gaussian, sqrt_pi_div_half]
        ring

/-- **Decay of the kernel for `x ≥ 1`.**
`|K_ν(x)| ≤ (π / 2)^{1/2} e^{(Re ν)² / 2} x^{−1/2} e^{−x}`. -/
theorem norm_positiveAxisBesselK_le_rpow_mul_exp (ν : ℂ) {x : ℝ} (hx : 1 ≤ x) :
    ‖positiveAxisBesselK ν x‖ ≤
      √(π / 2) * Real.exp (ν.re ^ 2 / 2) * x ^ (-(1 / 2) : ℝ) * Real.exp (-x) := by
  have hx0 : 0 < x := one_pos.trans_le hx
  have hsqrt : √(π / (2 * x)) = √(π / 2) * x ^ (-(1 / 2) : ℝ) := by
    rw [Real.rpow_neg hx0.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv, ← Real.sqrt_div' _ hx0.le,
      div_div]
  have hexp : Real.exp (ν.re ^ 2 / (2 * x)) ≤ Real.exp (ν.re ^ 2 / 2) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (sq_nonneg _) two_pos (by linarith))
  calc ‖positiveAxisBesselK ν x‖ ≤ √(π / (2 * x)) * Real.exp (ν.re ^ 2 / (2 * x) - x) :=
        norm_positiveAxisBesselK_le_sqrt_mul_exp ν x
    _ = √(π / 2) * Real.exp (ν.re ^ 2 / (2 * x)) * x ^ (-(1 / 2) : ℝ) * Real.exp (-x) := by
        rw [hsqrt, sub_eq_add_neg, Real.exp_add]
        ring
    _ ≤ _ := by gcongr

/-- **Uniform decay of the kernel.** For `ν` in a set with bounded real parts, such as a
vertical strip, there is `C` with `|K_ν(x)| ≤ C x^{−1/2} e^{−x}` for all `x ≥ 1`. -/
theorem exists_norm_positiveAxisBesselK_le {s : Set ℂ} (hs : Bornology.IsBounded (re '' s)) :
    ∃ C, ∀ ν ∈ s, ∀ x : ℝ, 1 ≤ x →
      ‖positiveAxisBesselK ν x‖ ≤ C * x ^ (-(1 / 2) : ℝ) * Real.exp (-x) := by
  obtain ⟨R, hR⟩ := hs.exists_norm_le
  refine ⟨√(π / 2) * Real.exp (R ^ 2 / 2), fun ν hν x hx ↦
    (norm_positiveAxisBesselK_le_rpow_mul_exp ν hx).trans ?_⟩
  have h : ν.re ^ 2 ≤ R ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hR _ (mem_image_of_mem re hν)) 2
  gcongr

/-- `∫_ℝ cosh(t / 2) e^{−c cosh t} dt = 2 (π / (2c))^{1/2} e^{−c}`, by the substitution
`s = 2 sinh(t / 2)`, under which `cosh t = 1 + s² / 2`. -/
private lemma integral_cosh_half_mul_exp_neg_mul_cosh (c : ℝ) :
    ∫ t : ℝ, Real.cosh (t / 2) * Real.exp (-(c * Real.cosh t)) =
      2 * √(π / (2 * c)) * Real.exp (-c) := by
  set f : ℝ → ℝ := fun t ↦ 2 * Real.sinh (t / 2)
  have hf (t : ℝ) : HasDerivAt f (Real.cosh (t / 2)) t :=
    ((((hasDerivAt_id' t).div_const 2).sinh).const_mul 2).congr_deriv (by ring)
  have hinj : Function.Injective f := fun t u h ↦ by
    have h' : t / 2 = u / 2 := Real.sinh_injective (by simpa [f] using h)
    linarith
  have hrange : f '' univ = univ := by
    rw [image_univ, range_eq_univ]
    intro s
    refine ⟨2 * Real.arsinh (s / 2), ?_⟩
    simp only [f]
    rw [mul_div_cancel_left₀ _ two_ne_zero, Real.sinh_arsinh]
    ring
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun t _ ↦ (hf t).hasDerivWithinAt) hinj.injOn
    (fun s : ℝ ↦ Real.exp (-c) * Real.exp (-(c / 2) * s ^ 2))
  rw [hrange, Measure.restrict_univ, integral_const_mul, integral_gaussian,
    sqrt_pi_div_half] at h
  rw [show 2 * √(π / (2 * c)) * Real.exp (-c) = Real.exp (-c) * (2 * √(π / (2 * c))) by ring, h]
  refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
  simp only [f, smul_eq_mul, abs_of_pos (Real.cosh_pos _)]
  rw [← Real.exp_add, Real.cosh_eq_one_add_two_mul_sinh_half_sq t]
  ring_nf

/-- **The half-integer order** (DLMF 10.39.2): `K_{1/2}(c) = (π / (2c))^{1/2} e^{−c}`. -/
theorem positiveAxisBesselK_one_half (c : ℝ) :
    positiveAxisBesselK (1 / 2) c = ((√(π / (2 * c)) * Real.exp (-c) : ℝ) : ℂ) := by
  rcases le_or_gt c 0 with hc | hc
  · rw [positiveAxisBesselK_of_nonpos _ hc,
      Real.sqrt_eq_zero'.mpr (div_nonpos_of_nonneg_of_nonpos pi_pos.le (by linarith)), zero_mul,
      ofReal_zero]
  -- `K_{±1/2}(c) = ½ I(±1/2)` with `I(σ) = ∫_ℝ e^{σ t} e^{−c cosh t} dt`
  have hK := positiveAxisBesselK_ofReal_eq_integral (1 / 2) c
  have hK' := positiveAxisBesselK_ofReal_eq_integral (-(1 / 2)) c
  -- evenness makes `I(1/2) = I(−1/2)`, and `I(1/2) + I(−1/2) = 2 ∫_ℝ cosh(t / 2) e^{−c cosh t} dt`
  rw [ofReal_neg, positiveAxisBesselK_neg, hK, ofReal_inj] at hK'
  have hsum : (∫ t : ℝ, Real.exp (1 / 2 * t) * Real.exp (-(c * Real.cosh t))) +
      ∫ t : ℝ, Real.exp (-(1 / 2) * t) * Real.exp (-(c * Real.cosh t)) =
      2 * ∫ t : ℝ, Real.cosh (t / 2) * Real.exp (-(c * Real.cosh t)) := by
    rw [← integral_add (Real.integrable_exp_mul_mul_exp_neg_mul_cosh _ hc)
      (Real.integrable_exp_mul_mul_exp_neg_mul_cosh _ hc), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    dsimp only
    rw [Real.cosh_eq (t / 2)]
    ring_nf
  rw [integral_cosh_half_mul_exp_neg_mul_cosh c] at hsum
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, hK, ofReal_inj]
  linarith

/-! ### Holomorphy in the order -/

private lemma continuousOn_logPowKernel (j : ℕ) (c : ℝ) :
    ContinuousOn (logPowKernel j c) (Ioi 0) := by
  unfold logPowKernel
  fun_prop (disch := exact fun u hu ↦ ne_of_gt hu)

/-- `(log u)^j e^{−(c / 2)(u + u⁻¹)} = O(u^{−a})` as `u → ∞`, for every `a`. -/
private lemma isBigO_logPowKernel_atTop (j : ℕ) {c : ℝ} (hc : 0 < c) (a : ℝ) :
    logPowKernel j c =O[atTop] (· ^ (-a)) := by
  -- for `u ≥ 1` the kernel is at most `u^j e^{−(c / 2) u}`, which is `O(u^{−a})`
  have hb : (fun u : ℝ ↦ u ^ j * Real.exp (-(c / 2) * u)) =O[atTop] (· ^ (-a)) := by
    refine ((isBigO_refl (fun u : ℝ ↦ u ^ j) atTop).mul
      (isLittleO_exp_neg_mul_rpow_atTop (half_pos hc) (-a - j)).isBigO).congr' ?_ ?_
    · exact EventuallyEq.rfl
    · filter_upwards [eventually_gt_atTop 0] with u hu
      rw [← Real.rpow_natCast, ← Real.rpow_add hu]
      ring_nf
  refine IsBigO.trans (IsBigO.of_bound 1 ?_) hb
  filter_upwards [eventually_ge_atTop 1] with u hu
  have hu0 : 0 < u := one_pos.trans_le hu
  have hlog : |Real.log u| ≤ u := by
    rw [abs_of_nonneg (Real.log_nonneg hu)]
    exact Real.log_le_self hu0.le
  rw [one_mul, logPowKernel, norm_smul, norm_pow, Real.norm_eq_abs, norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (by positivity)]
  gcongr
  nlinarith [inv_pos.mpr hu0]

/-- `(log u)^j e^{−(c / 2)(u + u⁻¹)} = O(u^{−b})` as `u → 0⁺`, for every `b`: the kernel is
invariant under `u ↦ u⁻¹` up to the sign `(−1)^j`. -/
private lemma isBigO_logPowKernel_nhdsGT (j : ℕ) {c : ℝ} (hc : 0 < c) (b : ℝ) :
    logPowKernel j c =O[𝓝[>] 0] (· ^ (-b)) := by
  have h := (isBigO_logPowKernel_atTop j hc (-b)).comp_tendsto tendsto_inv_nhdsGT_zero
  refine (IsBigO.of_bound 1 (Eventually.of_forall fun u ↦ ?_)).trans (h.congr' EventuallyEq.rfl ?_)
  · simp only [Function.comp_apply, logPowKernel, Real.log_inv, inv_inv, norm_smul, norm_pow,
      Real.norm_eq_abs, abs_neg, add_comm u⁻¹, one_mul, le_refl]
  · filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
    rw [Function.comp_apply, Real.inv_rpow hu.le, Real.rpow_neg hu.le, inv_inv]

/-- The Mellin transform of `logPowKernel j c` has derivative the Mellin transform of
`logPowKernel (j + 1) c`, at every `ν`. -/
private lemma hasDerivAt_mellin_logPowKernel (j : ℕ) (c : ℝ) (ν : ℂ) :
    HasDerivAt (mellin (logPowKernel j c)) (mellin (logPowKernel (j + 1) c) ν) ν := by
  rcases le_or_gt c 0 with hc | hc
  · rw [show mellin (logPowKernel j c) = fun _ ↦ 0 from funext (mellin_logPowKernel_of_nonpos j hc),
      mellin_logPowKernel_of_nonpos (j + 1) hc]
    exact hasDerivAt_const ν 0
  have h := (mellin_hasDerivAt_of_isBigO_rpow
    ((continuousOn_logPowKernel j c).locallyIntegrableOn measurableSet_Ioi)
    (isBigO_logPowKernel_atTop j hc (ν.re + 1)) (lt_add_one _)
    (isBigO_logPowKernel_nhdsGT j hc (ν.re - 1)) (sub_one_lt _)).2
  have hlog : (fun u : ℝ ↦ Real.log u • logPowKernel j c u) = logPowKernel (j + 1) c := by
    ext u
    rw [logPowKernel, logPowKernel, smul_smul, pow_succ']
  rwa [hlog] at h

/-- The `j`-th derivative of `ν ↦ K_ν(c)` is half the Mellin transform of `logPowKernel j c`. -/
private lemma iteratedDeriv_positiveAxisBesselK_eq_mellin (j : ℕ) (c : ℝ) :
    iteratedDeriv j (fun ν ↦ positiveAxisBesselK ν c) =
      fun ν ↦ 1 / 2 * mellin (logPowKernel j c) ν := by
  induction j with
  | zero =>
    ext ν
    rw [iteratedDeriv_zero, positiveAxisBesselK_eq_mellin, logPowKernel_zero]
  | succ j ih =>
    ext ν
    rw [iteratedDeriv_succ, ih]
    exact ((hasDerivAt_mellin_logPowKernel j c ν).const_mul (1 / 2)).deriv

/-- **Holomorphy in the order.** `ν ↦ K_ν(c)` is entire. -/
theorem differentiable_positiveAxisBesselK (c : ℝ) :
    Differentiable ℂ fun ν ↦ positiveAxisBesselK ν c := by
  have h := iteratedDeriv_positiveAxisBesselK_eq_mellin 0 c
  rw [iteratedDeriv_zero] at h
  rw [h]
  exact fun ν ↦ ((hasDerivAt_mellin_logPowKernel 0 c ν).const_mul (1 / 2)).differentiableAt

/-- **The derivative in the order.**
`∂_ν K_ν(c) = ½ ∫₀^∞ log u exp(−c (u + u⁻¹) / 2) exp(ν log u) du / u`. -/
theorem hasDerivAt_positiveAxisBesselK (ν : ℂ) (c : ℝ) :
    HasDerivAt (fun ν ↦ positiveAxisBesselK ν c) (1 / 2 * ∫ u : ℝ in Ioi 0, (Real.log u : ℂ) *
      (cexp (-(c : ℂ) * ((u : ℂ) + (u : ℂ)⁻¹) / 2) * cexp (ν * (Real.log u : ℂ)) / (u : ℂ))) ν := by
  have h := iteratedDeriv_positiveAxisBesselK_eq_mellin 0 c
  rw [iteratedDeriv_zero] at h
  rw [h]
  simpa only [mellin_logPowKernel, zero_add, pow_one] using
    (hasDerivAt_mellin_logPowKernel 0 c ν).const_mul (1 / 2 : ℂ)

/-- **The derivatives in the order.** For every `j`, the `j`-th derivative of `ν ↦ K_ν(c)` is
`½ ∫₀^∞ (log u)^j exp(−c (u + u⁻¹) / 2) exp(ν log u) du / u`. -/
theorem iteratedDeriv_positiveAxisBesselK (j : ℕ) (ν : ℂ) (c : ℝ) :
    iteratedDeriv j (fun ν ↦ positiveAxisBesselK ν c) ν =
      1 / 2 * ∫ u : ℝ in Ioi 0, (Real.log u : ℂ) ^ j *
        (cexp (-(c : ℂ) * ((u : ℂ) + (u : ℂ)⁻¹) / 2) * cexp (ν * (Real.log u : ℂ)) / (u : ℂ)) := by
  rw [iteratedDeriv_positiveAxisBesselK_eq_mellin j c]
  exact congrArg (1 / 2 * ·) (mellin_logPowKernel j ν c)

end Complex
