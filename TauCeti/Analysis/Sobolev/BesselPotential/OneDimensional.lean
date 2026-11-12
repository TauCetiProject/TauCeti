/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.BesselPotential.LineDeriv
public import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import TauCeti.Analysis.SpecialFunctions.Gaussian.Moment
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The space `H^{1,2}(ℝ)`: the Gaussian and the indicator of `[0, 1]`

Two computations on the real line test the identification of Mathlib's Bessel-potential space
`H^{1,2}(ℝ)` with the weak-derivative space `W^{1,2}(ℝ)`.

**The factor `2π`.** Mathlib's Bessel potential is the multiplier `(1 + ξ²)^{s/2}`, while the
derivative has the symbol `2πi ξ`, so by the Plancherel identity
(`BesselPotentialSpace.norm_sq_eq_norm_inclusion_sq_add_sum_norm_lineDerivCLM_sq`)

`‖u‖²_{H^{1,2}} = ‖u‖²_{L²} + (2π)⁻² ‖u'‖²_{L²}`.

For the Gaussian `g(x) = exp(-π x²)` this is `(1 + 1 / (4π)) / √2`
(`TauCeti.norm_toBesselPotentialSpaceCLM_one_gaussian_sq`), whereas the sum of the squared `L²`
norms of `g` and `g'` is `(1 + π) / √2` (`TauCeti.norm_toLp_gaussian_sq_add_norm_toLp_deriv_sq`).
The two norms are equivalent, with constants `1` and `(2π)²` on the derivative term, but not equal.

**A jump is not in `H^{1,2}`.** The indicator `1_{[0,1]}` lies in `L²(ℝ)` but not in `H^{1,2}(ℝ)`
(`TauCeti.not_memSobolev_one_of_ae_eq_indicator_Icc`). Its distributional derivative is
`δ₀ - δ₁`, and `H^{1,2}` membership would make this an `L²` function `w`. Testing against the
Gaussians `φₙ(x) = exp(-π n² x²)` gives `1 - exp(-π n²) = ∫ φₙ w`, while Cauchy–Schwarz bounds the
right side by `‖φₙ‖₂ ‖w‖₂`, and `‖φₙ‖₂² = 1 / (n √2) → 0`.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V, §3.
* M. Taylor, *Partial Differential Equations I*, Chapter 4, Section 1.
-/

public section

noncomputable section

open MeasureTheory FourierTransform TemperedDistribution Set
open scoped ENNReal SchwartzMap BesselPotentialSpace LineDeriv Real InnerProductSpace

namespace TauCeti

/-- A real Gaussian `x ↦ exp(-b x²)` on `ℝ`, `b > 0`, as a complex Schwartz function. -/
private theorem gaussian_apply_real {b : ℝ} (hb : 0 < (b : ℂ).re) (x : ℝ) :
    SchwartzMap.gaussian (V := ℝ) hb x = ((Real.exp (-b * x ^ 2) : ℝ) : ℂ) := by
  rw [SchwartzMap.gaussian_apply, Real.norm_eq_abs]
  push_cast
  rw [← Complex.ofReal_pow, sq_abs]
  push_cast
  rfl

/-- The squared modulus of a real Gaussian. -/
private theorem norm_gaussian_sq {b : ℝ} (hb : 0 < (b : ℂ).re) (x : ℝ) :
    ‖SchwartzMap.gaussian (V := ℝ) hb x‖ ^ 2 = Real.exp (-(2 * b) * x ^ 2) := by
  rw [gaussian_apply_real, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _), sq,
    ← Real.exp_add]
  ring_nf

/-- The derivative of a real Gaussian: `∂ₓ exp(-b x²) = -2 b x exp(-b x²)`. -/
private theorem lineDerivOp_one_gaussian_apply {b : ℝ} (hb : 0 < (b : ℂ).re) (x : ℝ) :
    ∂_{(1 : ℝ)} (SchwartzMap.gaussian (V := ℝ) hb) x =
      ((-2 * b * x * Real.exp (-b * x ^ 2) : ℝ) : ℂ) := by
  have hfun : (SchwartzMap.gaussian (V := ℝ) hb : ℝ → ℂ) =
      fun y ↦ ((Real.exp (-b * y ^ 2) : ℝ) : ℂ) := funext (gaussian_apply_real hb)
  have hd : HasDerivAt (fun y : ℝ ↦ Real.exp (-b * y ^ 2))
      (Real.exp (-b * x ^ 2) * (-b * (2 * x))) x := by
    simpa using ((hasDerivAt_pow 2 x).const_mul (-b)).exp
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, fderiv_apply_one_eq_deriv, hfun,
    hd.ofReal_comp.deriv]
  push_cast
  ring

/-- The squared modulus of the derivative of a real Gaussian. -/
private theorem norm_lineDerivOp_one_gaussian_sq {b : ℝ} (hb : 0 < (b : ℂ).re) (x : ℝ) :
    ‖∂_{(1 : ℝ)} (SchwartzMap.gaussian (V := ℝ) hb) x‖ ^ 2 =
      4 * b ^ 2 * (x ^ 2 * Real.exp (-(2 * b) * x ^ 2)) := by
  rw [lineDerivOp_one_gaussian_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
    sq (Real.exp _), ← Real.exp_add]
  ring_nf

/-- The squared `L²` norm of a Schwartz function. -/
private theorem norm_toLp_sq (f : 𝓢(ℝ, ℂ)) : ‖f.toLp 2‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  exact integral_congr_ae ((f.coeFn_toLp 2 volume).mono fun x hx ↦ by simp only [hx])

/-- `∫ exp(-2π x²) dx = 1 / √2`. -/
private theorem integral_exp_neg_two_pi_mul_sq : ∫ x : ℝ, Real.exp (-(2 * π) * x ^ 2) = (√2)⁻¹ := by
  rw [integral_gaussian, show π / (2 * π) = 2⁻¹ by field_simp, Real.sqrt_inv]

/-- `∫ x² exp(-2π x²) dx = 1 / (4π √2)`. -/
private theorem integral_sq_mul_exp_neg_two_pi_mul_sq :
    ∫ x : ℝ, x ^ 2 * Real.exp (-(2 * π) * x ^ 2) = (4 * π * √2)⁻¹ := by
  rw [integral_sq_mul_exp_neg_mul_sq (by positivity), Real.sqrt_mul zero_le_two]
  have : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  field_simp
  ring

/-- **The `H^{1,2}` norm of the Gaussian.** For `g(x) = exp(-π x²)` on `ℝ`,
`‖g‖²_{H^{1,2}} = ∫ (1 + ξ²) exp(-2π ξ²) dξ = (1 + 1 / (4π)) / √2`. Mathlib's Bessel potential has
the symbol `(1 + ξ²)^{1/2}`, not `(1 + 4π² ξ²)^{1/2}`. -/
theorem norm_toBesselPotentialSpaceCLM_one_gaussian_sq (hb : 0 < ((π : ℝ) : ℂ).re) :
    ‖SchwartzMap.toBesselPotentialSpaceCLM (1 : ℝ) 2
        (SchwartzMap.gaussian (V := ℝ) hb)‖ ^ 2 = (1 + (4 * π)⁻¹) / √2 := by
  set g := SchwartzMap.gaussian (V := ℝ) hb
  have key := BesselPotentialSpace.norm_sq_eq_norm_inclusion_sq_add_sum_norm_lineDerivCLM_sq
    (OrthonormalBasis.singleton (Fin 1) ℝ) (SchwartzMap.toBesselPotentialSpaceCLM (0 + 1) 2 g)
  simp only [BesselPotentialSpace.inclusion_toBesselPotentialSpaceCLM,
    OrthonormalBasis.singleton_apply, BesselPotentialSpace.lineDerivCLM_toBesselPotentialSpaceCLM,
    Finset.univ_unique, Finset.sum_singleton,
    ← BesselPotentialSpace.norm_toLp_eq, SchwartzMap.toLp_toBesselPotentialSpaceCLM_zero,
    norm_toLp_sq] at key
  rw [zero_add] at key
  rw [← BesselPotentialSpace.norm_toLp_eq, key]
  simp only [g, norm_gaussian_sq, norm_lineDerivOp_one_gaussian_sq, integral_const_mul,
    integral_exp_neg_two_pi_mul_sq, integral_sq_mul_exp_neg_two_pi_mul_sq]
  field_simp
  ring

/-- **The `W^{1,2}` norm of the Gaussian.** For `g(x) = exp(-π x²)` on `ℝ`,
`‖g‖²_{L²} + ‖g'‖²_{L²} = ∫ (1 + 4π² ξ²) exp(-2π ξ²) dξ = (1 + π) / √2`. Compared with
`TauCeti.norm_toBesselPotentialSpaceCLM_one_gaussian_sq`, the derivative term carries the factor
`(2π)²`. -/
theorem norm_toLp_gaussian_sq_add_norm_toLp_deriv_sq (hb : 0 < ((π : ℝ) : ℂ).re) :
    ‖(SchwartzMap.gaussian (V := ℝ) hb).toLp 2‖ ^ 2 +
        ‖(∂_{(1 : ℝ)} (SchwartzMap.gaussian (V := ℝ) hb)).toLp 2‖ ^ 2 =
      (1 + π) / √2 := by
  simp only [norm_toLp_sq, norm_gaussian_sq, norm_lineDerivOp_one_gaussian_sq, integral_const_mul,
    integral_exp_neg_two_pi_mul_sq, integral_sq_mul_exp_neg_two_pi_mul_sq]
  field_simp

/-- The distributional derivative of `1_{[0,1]}` is `δ₀ - δ₁`. -/
private theorem lineDerivOp_one_apply_of_ae_eq_indicator_Icc {u : Lp ℂ 2 (volume : Measure ℝ)}
    (hu : u =ᵐ[volume] (Icc (0 : ℝ) 1).indicator 1) (φ : 𝓢(ℝ, ℂ)) :
    ∂_{(1 : ℝ)} (u : 𝓢'(ℝ, ℂ)) φ = φ 0 - φ 1 := by
  rw [lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply]
  have hcongr : (fun x ↦ (-∂_{(1 : ℝ)} φ) x • u x) =ᵐ[volume]
      (Icc (0 : ℝ) 1).indicator fun x ↦ -∂_{(1 : ℝ)} φ x := hu.mono fun x hx ↦ by
    by_cases h : x ∈ Icc (0 : ℝ) 1 <;> simp [hx, h]
  rw [integral_congr_ae hcongr, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_neg,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := φ)
      (fun x _ ↦ by
        simpa [SchwartzMap.lineDerivOp_apply_eq_fderiv] using
          (φ.differentiableAt (x := x)).hasFDerivAt.hasDerivAt)
      ((∂_{(1 : ℝ)} φ).continuous.intervalIntegrable 0 1)]
  ring

/-- **The indicator of `[0, 1]` is not in `H^{1,2}(ℝ)`.** An `L²` function equal almost everywhere
to `1_{[0,1]}` does not lie in Mathlib's Bessel-potential space of order `1`: its distributional
derivative `δ₀ - δ₁` is not an `L²` function. -/
theorem not_memSobolev_one_of_ae_eq_indicator_Icc {u : Lp ℂ 2 (volume : Measure ℝ)}
    (hu : u =ᵐ[volume] (Icc (0 : ℝ) 1).indicator 1) : ¬ MemSobolev 1 2 (u : 𝓢'(ℝ, ℂ)) := by
  intro h
  have h' := h.lineDerivOp (m := (1 : ℝ))
  rw [sub_self, memSobolev_zero_iff] at h'
  obtain ⟨w, hw⟩ := h'
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * ‖w‖ ^ 2)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  have hn1 : (1 : ℝ) ≤ n := by
    have hn' : 0 < n := by exact_mod_cast hn0
    exact_mod_cast hn'
  have hnn : (n : ℝ) ≤ n ^ 2 := by
    rw [sq]
    exact le_mul_of_one_le_left hn0.le hn1
  -- Test `δ₀ - δ₁ = w` against the Gaussian `φ(x) = exp(-π n² x²)`.
  have hb : 0 < ((π * n ^ 2 : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    positivity
  set φ := SchwartzMap.gaussian (V := ℝ) hb
  have hφ : φ 0 - φ 1 = ⟪φ.toLp 2, w⟫_ℂ := by
    rw [← lineDerivOp_one_apply_of_ae_eq_indicator_Icc hu, hw, Lp.toTemperedDistribution_apply,
      L2.inner_def]
    refine integral_congr_ae ((φ.coeFn_toLp 2 volume).mono fun x hx ↦ ?_)
    dsimp only
    rw [hx, gaussian_apply_real, RCLike.inner_apply, Complex.conj_ofReal, smul_eq_mul, mul_comm]
  -- `‖φ‖₂² = 1 / (n √2) ≤ 1 / n`.
  have hnorm : ‖φ.toLp 2‖ ^ 2 ≤ (n : ℝ)⁻¹ := by
    rw [norm_toLp_sq]
    simp only [φ, norm_gaussian_sq, integral_gaussian]
    rw [show π / (2 * (π * n ^ 2)) = ((n : ℝ) ^ 2 * 2)⁻¹ by field_simp,
      Real.sqrt_le_left (by positivity), inv_pow]
    exact inv_anti₀ (by positivity) (by linarith)
  -- `|φ 0 - φ 1| = 1 - exp(-π n²) ≥ 1 / 2`.
  have hlow : (1 / 2 : ℝ) ≤ ‖φ 0 - φ 1‖ := by
    have hpi : 1 ≤ π * n ^ 2 := by
      have := mul_le_mul Real.two_le_pi (hn1.trans hnn) zero_le_one Real.pi_pos.le
      linarith
    have he : Real.exp (-(π * n ^ 2)) ≤ 1 / 2 := by
      calc Real.exp (-(π * n ^ 2)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
        _ ≤ 1 / 2 := by
          rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
          linarith [Real.add_one_le_exp (1 : ℝ)]
    rw [gaussian_apply_real, gaussian_apply_real, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, zero_pow two_ne_zero, mul_zero, Real.exp_zero, one_pow, mul_one]
    rw [abs_of_nonneg] <;> linarith
  -- Cauchy–Schwarz bounds it by `‖φ‖₂ ‖w‖₂`, and `‖φ‖₂² ‖w‖₂² ≤ ‖w‖₂² / n < 1 / 4`.
  have hcs : (1 / 2 : ℝ) ≤ ‖φ.toLp 2‖ * ‖w‖ :=
    hlow.trans (hφ ▸ norm_inner_le_norm (𝕜 := ℂ) (φ.toLp 2) w)
  have ha := norm_nonneg (φ.toLp 2)
  generalize ‖φ.toLp 2‖ = a at hnorm hcs ha
  generalize ‖w‖ = c at hn hcs
  have h1 : (1 / 2 : ℝ) ^ 2 ≤ a ^ 2 * c ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by norm_num) hcs 2
  have h2 : a ^ 2 * c ^ 2 ≤ c ^ 2 / n := by
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right hnorm (sq_nonneg c)
  have h3 : c ^ 2 / n < 1 / 4 := by
    rw [div_lt_iff₀ hn0]
    linarith
  linarith

end TauCeti
