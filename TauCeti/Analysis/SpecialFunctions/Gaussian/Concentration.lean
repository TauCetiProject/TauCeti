/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import TauCeti.Analysis.PDE.HeatKernel.ApproximateIdentity

/-!
# Gaussian densities and complex-kernel estimates

For `c > 0`, the function `t ↦ c exp (-(c t)²) / √π` is the density of the centred Gaussian law
of variance `(2 c²)⁻¹`, that is, of width `c⁻¹`. This file identifies the density with
Mathlib’s Gaussian probability density and records that its total mass is one.

This file also defines the complex translated Gaussian kernel
`Complex.gaussianKernel c t z = (c / √π) exp (-(c (t - z))²)` and records the estimates,
integrability, entire differentiation under the integral sign
(`Complex.differentiable_integral_gaussianKernel_smul`), and concentration limit as `c → ∞`
(`Complex.tendsto_integral_gaussianKernel_smul`) for integrals of bounded continuous vector-valued
functions against this kernel.

## Main definitions

* `Real.gaussianDensity`: the function `t ↦ c exp (-(c t)²) / √π`.
* `Complex.gaussianKernel`: the complex translated kernel `t, z ↦ (c / √π) exp (-(c (t - z))²)`.

## Main statements

* `Real.gaussianDensity_eq_gaussianPDFReal`: for `c > 0` it is Mathlib's Gaussian
  density `ProbabilityTheory.gaussianPDFReal` with mean `0` and variance `(2 c²)⁻¹`.
* `Real.integral_gaussianDensity`: for `c > 0` it has total mass one.
* `Complex.norm_cexp_neg_mul_sub_sq_le`: the Gaussian bound
  `‖exp (-(c (t - z))²)‖ ≤ exp (c² D²) exp (-(c² / 2) t²)` for `‖z‖ ≤ D`.
* `Complex.hasDerivAt_cexp_neg_mul_sub_sq`: the complex derivative of
  `z ↦ exp (-(c (t - z))²)`.
* `Complex.differentiable_integral_gaussianKernel_smul`: integrating a bounded continuous function
  against `Complex.gaussianKernel c · z` yields an entire function of `z`.
* `Complex.tendsto_integral_gaussianKernel_smul`: as `c → ∞`, integrating a bounded continuous
  function `f` against `Complex.gaussianKernel c · 0` converges to `f 0`.
-/

public section

noncomputable section

open Complex MeasureTheory Filter Topology Real
open scoped ComplexConjugate Convolution

namespace Real

/-- The real Gaussian density `t ↦ c exp (-(c t)²) / √π` of width `c⁻¹`. It is odd in `c`, and
for `c > 0` it is the density of the centred Gaussian law of variance `(2 c²)⁻¹`. -/
def gaussianDensity (c t : ℝ) : ℝ := c * ((√π)⁻¹ * rexp (-(c * t) ^ 2))

/-- The defining formula of the Gaussian density. -/
theorem gaussianDensity_def (c t : ℝ) :
    gaussianDensity c t = c * ((√π)⁻¹ * rexp (-(c * t) ^ 2)) := by
  rw [gaussianDensity]

/-- For `c ≥ 0` the Gaussian density is nonnegative. -/
theorem gaussianDensity_nonneg {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : 0 ≤ gaussianDensity c t := by
  rw [gaussianDensity]
  positivity

/-- For `c > 0`, the Gaussian density of width `c⁻¹` is the centred Gaussian probability density
of variance `(2 c²)⁻¹`. -/
theorem gaussianDensity_eq_gaussianPDFReal {c : ℝ} (hc : 0 < c) :
    gaussianDensity c = ProbabilityTheory.gaussianPDFReal 0 (2 * c ^ 2)⁻¹.toNNReal := by
  ext t
  have hv : (0 : ℝ) ≤ (2 * c ^ 2)⁻¹ := by positivity
  -- Normalize the variance factor before simplifying its square root.
  have hvariance : 2 * π * (2 * c ^ 2)⁻¹ = π / c ^ 2 := by field_simp
  -- Express the Gaussian exponent in terms of the scaled variable.
  have hexponent : -t ^ 2 / (2 * (2 * c ^ 2)⁻¹) = -(c * t) ^ 2 := by field_simp
  rw [gaussianDensity, ProbabilityTheory.gaussianPDFReal, Real.coe_toNNReal _ hv, sub_zero]
  rw [hvariance, Real.sqrt_div' _ (sq_nonneg c), Real.sqrt_sq hc.le]
  rw [hexponent]
  field_simp

/-- For `c > 0`, the Gaussian density of width `c⁻¹` has total mass one. -/
theorem integral_gaussianDensity {c : ℝ} (hc : 0 < c) : ∫ t, gaussianDensity c t = 1 := by
  rw [gaussianDensity_eq_gaussianPDFReal hc]
  refine ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 ?_
  simpa using pow_pos hc 2


end Real

namespace Complex

/-- The Gaussian bound `‖exp (-(c (t - z))²)‖ ≤ exp (c² D²) exp (-(c² / 2) t²)`
for `‖z‖ ≤ D`. -/
theorem norm_cexp_neg_mul_sub_sq_le (c t : ℝ) {z : ℂ} {D : ℝ} (hz : ‖z‖ ≤ D) :
    ‖cexp (-(c * (t - z)) ^ 2)‖ ≤ rexp (c ^ 2 * D ^ 2) * rexp (-(c ^ 2 / 2) * t ^ 2) := by
  have hz' : ‖z‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
  rw [norm_exp, ← Real.exp_add, Real.exp_le_exp]
  rw [Complex.sq_norm, normSq_apply] at hz'
  simp only [sq, neg_re, mul_re, mul_im, sub_re, sub_im, ofReal_re, ofReal_im] at hz' ⊢
  nlinarith [mul_nonneg (sq_nonneg c) (sq_nonneg (t - 2 * z.re)), mul_le_mul_of_nonneg_left hz'
    (sq_nonneg c)]

/-- The complex derivative of the translated Gaussian `z ↦ exp (-(c (t - z))²)`. -/
theorem hasDerivAt_cexp_neg_mul_sub_sq (c t : ℝ) (z : ℂ) :
    HasDerivAt (fun z : ℂ => cexp (-(c * (t - z)) ^ 2))
      (cexp (-(c * (t - z)) ^ 2) * (2 * c ^ 2 * (t - z))) z := by
  convert (((hasDerivAt_id' z).const_sub (t : ℂ)).const_mul (c : ℂ)).fun_pow 2 |>.fun_neg.cexp
    using 1; ring

/-- Complex translated Gaussian kernel `(c / √π) * exp (-(c * (t - z))²)`. -/
def gaussianKernel (c t : ℝ) (z : ℂ) : ℂ :=
  ((c : ℂ) / √π) * cexp (-((c : ℂ) * (t - z)) ^ 2)

/-- The defining formula of `Complex.gaussianKernel`. -/
theorem gaussianKernel_def (c t : ℝ) (z : ℂ) :
    gaussianKernel c t z = ((c : ℂ) / √π) * cexp (-((c : ℂ) * (t - z)) ^ 2) := by
  rw [gaussianKernel]

/-- `Complex.gaussianKernel c · z` is continuous on `ℝ`. -/
theorem continuous_gaussianKernel (c : ℝ) (z : ℂ) :
    Continuous fun t : ℝ => gaussianKernel c t z := by simp only [gaussianKernel_def]; fun_prop

/-- The complex Gaussian kernel vanishes at parameter `0`. -/
@[simp] theorem gaussianKernel_zero_param (t : ℝ) (z : ℂ) :
    gaussianKernel 0 t z = 0 := by simp [gaussianKernel]

/-- Reflecting the complex parameter under conjugation conjugates the Gaussian kernel. -/
@[simp] theorem gaussianKernel_conj (c t : ℝ) (z : ℂ) :
    conj (gaussianKernel c t (conj z)) = gaussianKernel c t z := by
  simp [gaussianKernel, ← Complex.exp_conj]

/-- Uniform-in-ball Gaussian upper bound for `Complex.gaussianKernel`. -/
theorem norm_gaussianKernel_le (c t : ℝ) {z : ℂ} {D : ℝ} (hz : ‖z‖ ≤ D) :
    ‖gaussianKernel c t z‖ ≤
      ‖(c : ℂ) / √π‖ * rexp (c ^ 2 * D ^ 2) * rexp (-(c ^ 2 / 2) * t ^ 2) := by
  rw [gaussianKernel, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_cexp_neg_mul_sub_sq_le c t hz) (norm_nonneg _)

/-- The norm of `Complex.gaussianKernel c · z` is integrable on `ℝ`. -/
theorem integrable_norm_gaussianKernel (c : ℝ) (z : ℂ) :
    Integrable fun t : ℝ => ‖gaussianKernel c t z‖ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  refine ((integrable_exp_neg_mul_sq (by positivity : 0 < c ^ 2 / 2)).const_mul
    (‖(c : ℂ) / √π‖ * rexp (c ^ 2 * ‖z‖ ^ 2))).mono'
    (Continuous.norm (by unfold gaussianKernel; fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  simpa only [Real.norm_of_nonneg (norm_nonneg _)] using norm_gaussianKernel_le c t (le_refl ‖z‖)

/-- Integrating a bounded continuous function against `Complex.gaussianKernel` yields an entire
function. -/
theorem differentiable_integral_gaussianKernel_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℝ → E} (hf : Continuous f) {B : ℝ} (hB : ∀ t, ‖f t‖ ≤ B) (c : ℝ) :
    Differentiable ℂ fun z : ℂ => ∫ t : ℝ, gaussianKernel c t z • f t := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  intro z₀
  have hb : 0 < c ^ 2 / 2 := by positivity
  set D := ‖z₀‖ + 1
  have hD (z : ℂ) (hz : z ∈ Metric.ball z₀ 1) : ‖z‖ ≤ D := (norm_lt_of_mem_ball hz).le
  have hG := integrable_exp_neg_mul_sq hb
  have hG' : Integrable fun t : ℝ => (|t| + D) * rexp (-(c ^ 2 / 2) * t ^ 2) :=
    ((integrable_mul_exp_neg_mul_sq hb).norm.add (hG.const_mul D)).congr (ae_of_all _ fun t => by
      simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]; ring)
  have hcontF (z : ℂ) : Continuous fun t : ℝ => gaussianKernel c t z • f t :=
    (continuous_gaussianKernel c z).smul hf
  have hcontF' : Continuous fun t : ℝ =>
      (gaussianKernel c t z₀ * (2 * (c : ℂ) ^ 2 * (t - z₀))) • f t :=
    ((continuous_gaussianKernel c z₀).mul (by fun_prop)).smul hf
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z₀ one_pos)
    (F := fun z t => gaussianKernel c t z • f t)
    (F' := fun z t => (gaussianKernel c t z * (2 * (c : ℂ) ^ 2 * (t - z))) • f t)
    (bound := fun t => ‖(c : ℂ) / √π‖ * rexp (c ^ 2 * D ^ 2) * (2 * c ^ 2) * B *
      ((|t| + D) * rexp (-(c ^ 2 / 2) * t ^ 2)))
    (.of_forall fun z => (hcontF z).aestronglyMeasurable) ?_ hcontF'.aestronglyMeasurable
    (ae_of_all _ fun t z hz => ?_) (hG'.const_mul _)
    (ae_of_all _ fun t z _ => by
      simpa only [gaussianKernel, mul_assoc] using
        ((hasDerivAt_cexp_neg_mul_sub_sq c t z).const_mul ((c : ℂ) / √π)).smul_const
          (f t))).2.differentiableAt
  · refine (hG.const_mul (‖(c : ℂ) / √π‖ * rexp (c ^ 2 * D ^ 2) * B)).mono'
      (hcontF z₀).aestronglyMeasurable (ae_of_all _ fun t => ?_)
    rw [norm_smul]
    exact (mul_le_mul (norm_gaussianKernel_le c t (hD z₀ (Metric.mem_ball_self one_pos))) (hB t)
      (norm_nonneg _) (by positivity)).trans_eq (by ring)
  · have hlin : ‖2 * (c : ℂ) ^ 2 * (t - z)‖ ≤ 2 * c ^ 2 * (|t| + D) := by
      rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        Complex.norm_two]
      gcongr; exact (norm_sub_le _ _).trans
        (by rw [Complex.norm_real, Real.norm_eq_abs]; gcongr; exact hD z hz)
    rw [norm_smul, norm_mul]
    exact (mul_le_mul (mul_le_mul (norm_gaussianKernel_le c t (hD z hz)) hlin
      (norm_nonneg _) (by positivity)) (hB t) (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- As `c → ∞`, integrating a bounded continuous function against `Complex.gaussianKernel c · 0`
tends to `f 0`. -/
theorem tendsto_integral_gaussianKernel_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f : ℝ → E} (hf : Continuous f) {B : ℝ}
    (hB : ∀ t, ‖f t‖ ≤ B) :
    Tendsto (fun c : ℝ => ∫ t : ℝ, gaussianKernel c t 0 • f t) atTop (𝓝 (f 0)) := by
  let g : ℝ → E := fun u => f (-u); have hg : Continuous g := hf.comp continuous_neg
  have htime : Tendsto (fun c : ℝ => 4 * c ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by decide : 2 ≠ 0)).const_mul_atTop (by norm_num : 0 < (4 : ℝ))
  have ht : Tendsto (fun c : ℝ => 1 / (4 * c ^ 2)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa only [one_div] using! htime.inv_tendsto_atTop,
      (eventually_gt_atTop 0).mono fun c hc => Set.mem_Ioi.mpr (by positivity)⟩
  have hlim := (TauCeti.tendsto_heatKernel_convolution hg.aestronglyMeasurable
    (ae_of_all _ fun u => hB (-u)) (x₀ := 0) hg.continuousAt).comp (ht.prodMk tendsto_const_nhds)
  rw [show g 0 = f 0 by simp [g]] at hlim
  refine hlim.congr' ((eventually_gt_atTop 0).mono fun c hc => ?_)
  have hkernel (t : ℝ) : TauCeti.heatKernel (1 / (4 * c ^ 2)) t = Real.gaussianDensity c t := by
    rw [TauCeti.heatKernel_apply]; simp only [Module.finrank_self, Nat.cast_one, Real.norm_eq_abs,
      sq_abs]
    rw [neg_div, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
      show 4 * π * (1 / (4 * c ^ 2)) = π / c ^ 2 by field_simp, Real.sqrt_div' _ (sq_nonneg c),
      Real.sqrt_sq hc.le, show -t ^ 2 / (4 * (1 / (4 * c ^ 2))) = -(c * t) ^ 2 by field_simp,
      Real.gaussianDensity_def]; simp only [inv_div]; ring
  simp only [Function.comp_apply, convolution_def, ContinuousLinearMap.lsmul_apply, zero_sub,
    hkernel, g, neg_neg]
  congr 1 with t; rw [gaussianKernel, Real.gaussianDensity_def, ← Complex.coe_smul]
  congr 1; push_cast; ring_nf

end Complex
