/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv
import TauCeti.Analysis.SpecialFunctions.Gaussian.Basic
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Complex Gaussians as Schwartz functions

For `b : ℂ` with `0 < b.re`, the Gaussian `x ↦ exp (-b ‖x‖²)` on a real inner product space is a
Schwartz function, `SchwartzMap.gaussian`. The parameter is complex, so this covers both the real
heat-kernel Gaussians and the oscillating Gaussians `x ↦ exp (π i τ ‖x‖²)`, `0 < τ.im`, whose
lattice sums are theta series. The normalisation `-b * ‖x‖ ^ 2` is the one of Mathlib's
`fourier_gaussian_innerProductSpace`, which computes the Fourier transform of this function;
`SchwartzMap.fourierInv_gaussian` restates it for the inverse Fourier transform of the Schwartz
Gaussian.
Translates of the Gaussian are Schwartz functions through Mathlib's
`SchwartzMap.compSubConstCLM`.

The decay estimate writes the Gaussian as `Complex.exp` composed with `x ↦ -b * ‖x‖ ^ 2`. Every
real iterated derivative of `Complex.exp` at `z` has norm `‖exp z‖`, and the inner function has
temperate growth (Mathlib's `Function.hasTemperateGrowth_norm_sq`), so the Faà di Bruno bound
`norm_iteratedFDeriv_comp_le` bounds the `n`-th derivative by a polynomial in `‖x‖` times
`exp (-b.re * ‖x‖ ^ 2)`. The two scalar inputs, `TauCeti.norm_iteratedFDeriv_real_cexp` and
`TauCeti.one_add_pow_mul_exp_neg_mul_sq_le`, live in `TauCeti.Analysis.SpecialFunctions.Exp.Deriv`
and `TauCeti.Analysis.SpecialFunctions.Gaussian.Basic`.

## Main declarations

* `SchwartzMap.gaussian`: the Gaussian `x ↦ exp (-b ‖x‖²)`, `0 < b.re`, as a Schwartz function.
* `SchwartzMap.gaussian_apply`, `SchwartzMap.coe_gaussian`, `SchwartzMap.coe_gaussian_ofReal`:
  its values.
* `SchwartzMap.norm_gaussian_apply`: its modulus `exp (-b.re ‖x‖²)`.
* `SchwartzMap.fourierInv_gaussian`: its inverse Fourier transform
  `(π / b)^(n/2) exp (-π² ‖x‖² / b)`, where `n` is the dimension.
* `SchwartzMap.eLpNorm_gaussian`, `SchwartzMap.eLpNorm_gaussian_top`: its `Lᵖ` norms
  `(π / (p b.re))^(n/(2p))`, `0 < p < ∞`, and its `L^∞` norm `1`.
* `SchwartzMap.eLpNorm_fourier_gaussian`: the `L^q` norms
  `π^(n/2) (π b.re q)^(-n/(2q)) ‖b‖^(n/q - n/2)`, `0 < q < ∞`, of its Fourier transform. For fixed
  `b.re` they grow with `‖b‖` exactly when `q < 2`, while the norms of the Gaussian itself depend
  only on `b.re`.
* `Function.hasTemperateGrowth_exp_neg_mul_norm_sq`: the real Gaussian `x ↦ exp (-c ‖x‖²)`,
  `0 ≤ c`, has temperate growth, so it is a Fourier multiplier symbol on tempered distributions.
-/

public section

noncomputable section

open Complex Function
open scoped ContDiff FourierTransform Nat SchwartzMap

namespace SchwartzMap

open TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Gaussian `x ↦ exp (-b ‖x‖²)` on a real inner product space, for `0 < b.re`, as a
Schwartz function. Its Fourier transform is computed by Mathlib's
`fourier_gaussian_innerProductSpace`. -/
def gaussian {b : ℂ} (hb : 0 < b.re) : 𝓢(V, ℂ) where
  toFun x := cexp (-b * ‖x‖ ^ 2)
  smooth' := by
    have h : ContDiff ℝ ∞ fun x : V ↦ ((‖x‖ ^ 2 : ℝ) : ℂ) :=
      ofRealCLM.contDiff.comp (contDiff_norm_sq ℝ)
    simp only [ofReal_pow] at h
    exact contDiff_exp.comp (contDiff_const.mul h)
  decay' k n := by
    -- The exponent `x ↦ -b * ‖x‖ ^ 2` has temperate growth.
    set f : V → ℂ := fun x ↦ -b * (‖x‖ : ℂ) ^ 2
    have hf : f.HasTemperateGrowth := by
      have : f = fun x ↦ (-b) * ((‖x‖ ^ 2 : ℝ) : ℂ) := by ext; simp [f]
      rw [this]
      exact (HasTemperateGrowth.const _).mul
        (Complex.hasTemperateGrowth_ofReal.comp (hasTemperateGrowth_norm_sq V))
    obtain ⟨k₁, C₁, hC₁, h₁⟩ := hf.norm_iteratedFDeriv_le_uniform n
    set m := k + k₁ * n
    refine ⟨n ! * (1 + C₁) ^ n * (m ! / (b.re / 2) ^ m * Real.exp b.re), fun x ↦ ?_⟩
    have hfx : ‖cexp (f x)‖ = Real.exp (-b.re * ‖x‖ ^ 2) := by
      rw [Complex.norm_exp]
      congr 1
      simp [f, ← ofReal_pow]
    -- Faà di Bruno for `Complex.exp ∘ f`, as in `Function.HasTemperateGrowth.comp'`.
    have hD : ∀ i, 1 ≤ i → i ≤ n →
        ‖iteratedFDeriv ℝ i f x‖ ≤ ((1 + C₁) * (1 + ‖x‖) ^ k₁) ^ i := by
      intro i hi hin
      calc ‖iteratedFDeriv ℝ i f x‖ ≤ C₁ * (1 + ‖x‖) ^ k₁ := h₁ i hin x
        _ ≤ (1 + C₁) * (1 + ‖x‖) ^ k₁ := by gcongr; simp
        _ ≤ _ := le_self_pow₀ (one_le_mul_of_one_le_of_one_le (by simp [hC₁])
            (one_le_pow₀ (by simp))) (by omega)
    have hcomp := norm_iteratedFDeriv_comp_le contDiff_exp hf.1 (mod_cast le_top) x
      (fun i _ ↦ (norm_iteratedFDeriv_real_cexp i (f x)).le) hD
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x ↦ cexp (-b * ‖x‖ ^ 2)) x‖
        ≤ (1 + ‖x‖) ^ k *
            (n ! * Real.exp (-b.re * ‖x‖ ^ 2) * ((1 + C₁) * (1 + ‖x‖) ^ k₁) ^ n) := by
          rw [← hfx]
          gcongr
          · simp
          · exact hcomp
      _ = n ! * (1 + C₁) ^ n * ((1 + ‖x‖) ^ m * Real.exp (-b.re * ‖x‖ ^ 2)) := by
          simp only [m, mul_pow, ← pow_mul, pow_add]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (one_add_pow_mul_exp_neg_mul_sq_le hb m) (by positivity)

/-- The value of the Schwartz Gaussian at `x` is `exp (-b ‖x‖²)`. -/
@[simp]
theorem gaussian_apply {b : ℂ} (hb : 0 < b.re) (x : V) :
    gaussian hb x = cexp (-b * ‖x‖ ^ 2) :=
  (rfl)

/-- The modulus of the Schwartz Gaussian at `x` is the real Gaussian `exp (-b.re ‖x‖²)`. -/
theorem norm_gaussian_apply {b : ℂ} (hb : 0 < b.re) (x : V) :
    ‖gaussian hb x‖ = Real.exp (-b.re * ‖x‖ ^ 2) := by
  rw [gaussian_apply]
  exact norm_cexp_neg_mul_sq b ‖x‖

/-- The Schwartz Gaussian, as a function, is `x ↦ exp (-b ‖x‖²)`. -/
theorem coe_gaussian {b : ℂ} (hb : 0 < b.re) :
    ((gaussian hb : 𝓢(V, ℂ)) : V → ℂ) = fun x ↦ cexp (-b * ‖x‖ ^ 2) :=
  funext (gaussian_apply hb)

/-- At a real parameter `c`, the Schwartz Gaussian is the real Gaussian `x ↦ exp (-c ‖x‖²)`,
viewed as a complex function. -/
theorem coe_gaussian_ofReal {c : ℝ} (hb : 0 < (c : ℂ).re) :
    ((gaussian hb : 𝓢(V, ℂ)) : V → ℂ) = fun x ↦ ((Real.exp (-(c * ‖x‖ ^ 2)) : ℝ) : ℂ) := by
  funext x
  rw [gaussian_apply, Complex.ofReal_exp]
  push_cast
  ring_nf

/-- The inverse Fourier transform of the Schwartz Gaussian `exp (-b ‖ξ‖²)`, `0 < b.re`, on a
real inner product space of dimension `n` is the Gaussian `(π / b)^(n/2) exp (-π² ‖x‖² / b)`. -/
theorem fourierInv_gaussian [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {b : ℂ}
    (hb : 0 < b.re) (x : V) :
    𝓕⁻ (gaussian hb : 𝓢(V, ℂ)) x =
      (Real.pi / b) ^ (Module.finrank ℝ V / 2 : ℂ) * cexp (-Real.pi ^ 2 * ‖x‖ ^ 2 / b) := by
  rw [fourierInv_coe, Real.fourierInv_eq_fourier_neg, coe_gaussian,
    fourier_gaussian_innerProductSpace hb, norm_neg]

open MeasureTheory Filter in
open scoped ENNReal in
/-- **The Lebesgue norms of the Gaussian.** For `0 < b.re` and `0 < p < ∞`, the Gaussian
`exp (-b ‖x‖²)` on a real inner product space of dimension `n` has `Lᵖ` norm
`(π / (p b.re))^(n/(2p))`. For `b = π` this is `p^(-n/(2p))`, in particular `1` for `p = 1`. -/
theorem eLpNorm_gaussian [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {b : ℂ}
    (hb : 0 < b.re) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ (⊤ : ℝ≥0∞)) :
    eLpNorm (gaussian hb : 𝓢(V, ℂ)) p volume =
      ENNReal.ofReal ((Real.pi / (b.re * p.toReal)) ^
        ((Module.finrank ℝ V : ℝ) / (2 * p.toReal))) := by
  have hp' : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hbp : 0 < b.re * p.toReal := mul_pos hb hp'
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp
    (gaussian hb).continuous.aestronglyMeasurable]
  have hpow (x : V) : ‖gaussian hb x‖ₑ ^ p.toReal =
      ENNReal.ofReal (Real.exp (-(b.re * p.toReal) * ‖x‖ ^ 2)) := by
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp'.le,
      norm_gaussian_apply, ← Real.exp_mul]
    congr 2
    ring
  have hint : Integrable (fun x : V ↦ Real.exp (-(b.re * p.toReal) * ‖x‖ ^ 2)) := by
    have hb' : 0 < ((b.re * p.toReal : ℝ) : ℂ).re := by simpa using hbp
    refine (gaussian (V := V) hb').integrable.norm.congr (Eventually.of_forall fun x ↦ ?_)
    simp only [norm_gaussian_apply, ofReal_re]
  simp_rw [hpow]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun x ↦ (Real.exp_pos _).le),
    GaussianFourier.integral_rexp_neg_mul_sq_norm hbp,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), ← Real.rpow_mul (by positivity)]
  congr 2
  field_simp

open MeasureTheory Filter in
open scoped ENNReal in
/-- **The supremum of the Gaussian.** For `0 < b.re`, the Gaussian `exp (-b ‖x‖²)` has `L^∞`
norm `1`, its modulus at the origin, for every measure positive on open sets. -/
theorem eLpNorm_gaussian_top [MeasurableSpace V] [OpensMeasurableSpace V] {b : ℂ}
    (hb : 0 < b.re) (μ : Measure V) [μ.IsOpenPosMeasure] :
    eLpNorm (gaussian hb : 𝓢(V, ℂ)) ∞ μ = 1 := by
  have hbound (x : V) : ‖gaussian hb x‖ ≤ 1 := by
    rw [norm_gaussian_apply, Real.exp_le_one_iff]
    nlinarith [sq_nonneg ‖x‖]
  have hm : MemLp (gaussian hb : 𝓢(V, ℂ)) ∞ μ :=
    memLp_top_of_bound (gaussian hb).continuous.aestronglyMeasurable 1
      (Eventually.of_forall hbound)
  rw [eLpNorm_exponent_top (gaussian hb).continuous.aestronglyMeasurable]
  refine le_antisymm (by simpa using eLpNormEssSup_le_of_ae_bound (Eventually.of_forall hbound)) ?_
  -- The bound is attained at the origin, where the Gaussian is continuous.
  have h0 : ‖gaussian hb (0 : V)‖ = 1 := by simp [gaussian_apply]
  rw [← ENNReal.ofReal_one, ← h0, ← eLpNorm_exponent_top
    (gaussian hb).continuous.aestronglyMeasurable]
  refine ENNReal.ofReal_le_of_le_toReal ?_
  rw [← Lp.norm_toLp _ hm]
  exact Lp.norm_le_norm_top_of_ae_eq_of_continuousAt hm.coeFn_toLp
    (gaussian hb).continuous.continuousAt

open MeasureTheory in
open scoped ENNReal in
/-- **The Lebesgue norms of the Fourier transform of the Gaussian.** For `0 < b.re` and
`0 < q < ∞`, the Fourier transform of the Gaussian `exp (-b ‖x‖²)` on a real inner product space
of dimension `n` has `L^q` norm `π^(n/2) (π b.re q)^(-n/(2q)) ‖b‖^(n/q - n/2)`. Indeed it is
`(π / b)^(n/2)` times the Gaussian of parameter `π² / b`, whose real part is `π² b.re / ‖b‖²`.
For `b = π` this is `q^(-n/(2q))`, the norm of the Gaussian itself, which is its own Fourier
transform. -/
theorem eLpNorm_fourier_gaussian [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {b : ℂ} (hb : 0 < b.re) {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ (⊤ : ℝ≥0∞)) :
    eLpNorm (𝓕 ⇑(gaussian hb : 𝓢(V, ℂ))) q volume =
      ENNReal.ofReal (Real.pi ^ ((Module.finrank ℝ V : ℝ) / 2) /
        (Real.pi * b.re * q.toReal) ^ ((Module.finrank ℝ V : ℝ) / (2 * q.toReal)) *
          ‖b‖ ^ ((Module.finrank ℝ V : ℝ) / q.toReal - (Module.finrank ℝ V : ℝ) / 2)) := by
  have hnb : 0 < ‖b‖ := norm_pos_iff.2 fun h ↦ by simp [h] at hb
  have hq' : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  have hre : ((Real.pi : ℂ) ^ 2 / b).re = Real.pi ^ 2 * b.re / ‖b‖ ^ 2 := by
    rw [div_re, normSq_eq_norm_sq]
    simp [← ofReal_pow]
  have hb' : 0 < ((Real.pi : ℂ) ^ 2 / b).re := by
    rw [hre]
    positivity
  -- The Fourier transform is `(π / b)^(n/2)` times the Gaussian of parameter `π² / b`.
  have hF : 𝓕 ⇑(gaussian hb : 𝓢(V, ℂ)) =
      ((Real.pi : ℂ) / b) ^ ((Module.finrank ℝ V : ℂ) / 2) • ⇑(gaussian hb' : 𝓢(V, ℂ)) := by
    ext w
    rw [coe_gaussian, fourier_gaussian_innerProductSpace hb, Pi.smul_apply, gaussian_apply,
      smul_eq_mul]
    congr 2
    ring
  have hc : ‖((Real.pi : ℂ) / b) ^ ((Module.finrank ℝ V : ℂ) / 2)‖ =
      (Real.pi / ‖b‖) ^ ((Module.finrank ℝ V : ℝ) / 2) := by
    have : ((Module.finrank ℝ V : ℂ) / 2) = (((Module.finrank ℝ V : ℝ) / 2 : ℝ) : ℂ) := by
      rw [ofReal_div, ofReal_natCast, ofReal_ofNat]
    rw [this, norm_cpow_real, norm_div, norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [hF, eLpNorm_const_smul, eLpNorm_gaussian hb' hq0 hq, ← ofReal_norm, hc,
    ← ENNReal.ofReal_mul (by positivity), hre]
  congr 1
  -- Collect the powers of `‖b‖`.
  have hbase : Real.pi / (Real.pi ^ 2 * b.re / ‖b‖ ^ 2 * q.toReal) =
      ‖b‖ ^ (2 : ℝ) / (Real.pi * b.re * q.toReal) := by
    rw [Real.rpow_two]
    field_simp
  rw [hbase, Real.div_rpow Real.pi_pos.le hnb.le, Real.div_rpow (by positivity) (by positivity),
    ← Real.rpow_mul hnb.le, Real.rpow_sub hnb]
  field_simp

end SchwartzMap

/-- The real Gaussian `x ↦ exp (-c ‖x‖²)`, `0 ≤ c`, has temperate growth: for `c > 0` it is the
real part of the Schwartz function `SchwartzMap.gaussian`, and for `c = 0` it is constant.
Composed with `Complex.ofReal`, this is the symbol of the heat semigroup as a Fourier
multiplier. -/
theorem Function.hasTemperateGrowth_exp_neg_mul_norm_sq {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] {c : ℝ} (hc : 0 ≤ c) :
    (fun x : V ↦ Real.exp (-(c * ‖x‖ ^ 2))).HasTemperateGrowth := by
  rcases hc.eq_or_lt with rfl | hc
  · simp
  · have hb : 0 < (c : ℂ).re := by simpa using hc
    have h := Complex.hasTemperateGrowth_re.comp
      (SchwartzMap.gaussian (V := V) hb).hasTemperateGrowth
    rw [SchwartzMap.coe_gaussian_ofReal] at h
    exact h
