/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.RieszTransform.Basic
public import TauCeti.MeasureTheory.Integral.CalderonZygmund.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian
import TauCeti.MeasureTheory.Integral.RpowLaplace

/-!
# The kernel of the Riesz transforms

Let `E` be a real inner product space of finite dimension `n` and `F` a complex Hilbert space. The
Riesz transform `R_v` on `L²(E, F)` (`TauCeti.rieszTransform`) is the Fourier multiplier with
symbol `-i ⟪ξ, v⟫ / ‖ξ‖`. This file shows that it is a Calderón–Zygmund operator: off the support
of its argument it is the singular integral operator with kernel

`K_v(z) = c_n ⟪z, v⟫ / ‖z‖ ^ (n + 1)`, `c_n = Γ((n + 1) / 2) / π ^ ((n + 1) / 2)`

(`TauCeti.rieszKernel`). If `f ∈ L²` vanishes off a compact set `s`, then
`R_v f (x) = ∫ K_v(x - y) f(y) dy` for almost every `x ∉ s`
(`TauCeti.ae_rieszTransform_eq_integral`). The kernel satisfies the standard size and smoothness
estimates `|K_v(z)| ≤ c_n ‖v‖ ‖z‖⁻ⁿ` and `|K_v(a) - K_v(b)| ≤ C ‖v‖ ‖a - b‖ ‖b‖⁻ⁿ⁻¹` for
`2 ‖a - b‖ < ‖b‖`, so the Calderón–Zygmund theorem makes `R_v` of weak type `(1, 1)`
(`TauCeti.exists_mul_volume_lt_enorm_rieszTransform_le`). In dimension one, `K_1(z) = 1 / (π z)`
is the kernel of the Hilbert transform.

## The argument

The symbol and the kernel are both averages of Gaussians. For `t > 0`, the Schwartz function
`h_t(x) = t^(-n/2) ∂_v exp(-π ‖x‖² / t)` has Fourier transform `2πi ⟪ξ, v⟫ exp(-π t ‖ξ‖²)`, and
the Gamma integrals

`∫₀^∞ t^(-1/2) exp(-π t ‖ξ‖²) dt = ‖ξ‖⁻¹` and
`∫₀^∞ t^(-1/2) t^(-(n+2)/2) exp(-π ‖z‖² / t) dt = c_n ‖z‖⁻ⁿ⁻¹`

show that averaging `𝓕 h_t` against `t^(-1/2) dt` gives `-2π` times the Riesz symbol, while
averaging `h_t` gives `-2π K_v`. The multiplier with the Schwartz symbol `𝓕 h_t` is convolution
with `h_t` (`SchwartzMap.coeFn_fourierMultiplierCLM_toLp`). So for `g ∈ L²` vanishing off a set
at positive distance from `s`, Fubini's theorem on the Fourier side and in space gives

`⟪g, R_v f⟫ = ∫∫ K_v(x - y) ⟪g(x), f(y)⟫ dy dx`;

the separation of the supports keeps `K_v(x - y)` bounded, which makes the space-side integral
absolutely convergent. Taking `g` to be the restriction of `R_v f - K_v ⋆ f` to a compact set at
positive distance from `s` shows that the two agree there.

## References

* E. M. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter III,
  §1.2.
* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Section 5.1.4 and Proposition 5.1.14.
-/

public section

noncomputable section

open scoped ENNReal NNReal FourierTransform SchwartzMap RealInnerProductSpace Real LineDeriv
open FourierTransform MeasureTheory Set Filter Topology Module Metric

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The kernel `c_n ⟪z, v⟫ / ‖z‖ ^ (n + 1)` of the Riesz transform in the direction `v`, where
`n` is the dimension of `E` and `c_n = Γ((n + 1) / 2) / π ^ ((n + 1) / 2)`. At the origin it
takes the value `0`. -/
def rieszKernel (v z : E) : ℝ :=
  Real.Gamma ((finrank ℝ E + 1) / 2) / π ^ (((finrank ℝ E : ℝ) + 1) / 2) * ⟪z, v⟫ /
    ‖z‖ ^ (finrank ℝ E + 1)

theorem rieszKernel_apply (v z : E) :
    rieszKernel v z = Real.Gamma ((finrank ℝ E + 1) / 2) / π ^ (((finrank ℝ E : ℝ) + 1) / 2) *
      ⟪z, v⟫ / ‖z‖ ^ (finrank ℝ E + 1) := (rfl)

@[simp]
theorem rieszKernel_zero_right (v : E) : rieszKernel v 0 = 0 := by
  simp [rieszKernel]

@[fun_prop]
theorem measurable_rieszKernel [MeasurableSpace E] [BorelSpace E] (v : E) :
    Measurable (rieszKernel v) := by
  unfold rieszKernel
  fun_prop

/-- **Size estimate** for the Riesz kernel: `|K_v(z)| ≤ c_n ‖v‖ / ‖z‖ ^ n`. -/
theorem abs_rieszKernel_le (v z : E) :
    |rieszKernel v z| ≤ Real.Gamma ((finrank ℝ E + 1) / 2) /
      π ^ (((finrank ℝ E : ℝ) + 1) / 2) * ‖v‖ / ‖z‖ ^ finrank ℝ E := by
  have hc : 0 ≤ Real.Gamma ((finrank ℝ E + 1) / 2) / π ^ (((finrank ℝ E : ℝ) + 1) / 2) :=
    div_nonneg (Real.Gamma_nonneg_of_nonneg (by positivity)) (by positivity)
  rcases eq_or_ne z 0 with rfl | hz
  · simpa using div_nonneg (mul_nonneg hc (norm_nonneg v)) (by positivity)
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  rw [rieszKernel, abs_div, abs_mul, abs_of_nonneg hc, abs_of_pos (pow_pos hz' _),
    div_le_div_iff₀ (pow_pos hz' _) (pow_pos hz' _)]
  calc _ ≤ Real.Gamma ((finrank ℝ E + 1) / 2) / π ^ (((finrank ℝ E : ℝ) + 1) / 2) *
        (‖z‖ * ‖v‖) * ‖z‖ ^ finrank ℝ E := by
        gcongr
        exact abs_real_inner_le_norm _ _
    _ = _ := by ring

/-- The two first-order terms of the increment `⟪a, v⟫ / ‖a‖ ^ m - ⟪b, v⟫ / ‖b‖ ^ m`. -/
private theorem rieszKernel_sub_eq (v : E) {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) :
    rieszKernel v a - rieszKernel v b =
      Real.Gamma ((finrank ℝ E + 1) / 2) / π ^ (((finrank ℝ E : ℝ) + 1) / 2) *
        (⟪a - b, v⟫ / ‖a‖ ^ (finrank ℝ E + 1) + ⟪b, v⟫ * (‖b‖ ^ (finrank ℝ E + 1) -
          ‖a‖ ^ (finrank ℝ E + 1)) / (‖a‖ ^ (finrank ℝ E + 1) * ‖b‖ ^ (finrank ℝ E + 1))) := by
  have ha' : ‖a‖ ^ (finrank ℝ E + 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 ha)
  have hb' : ‖b‖ ^ (finrank ℝ E + 1) ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hb)
  simp only [rieszKernel_apply, inner_sub_left]
  field_simp
  ring

/-- The second term of `rieszKernel_sub_eq`, for `‖b‖ ≤ 2 ‖a‖` and `‖a‖ ≤ 2 ‖b‖`. -/
private theorem abs_inner_mul_pow_sub_pow_div_le (v : E) (n : ℕ)
    {a b : E} (hα : 0 < ‖a‖) (hβ : 0 < ‖b‖) (hαβ : ‖b‖ ≤ 2 * ‖a‖)
    (hβα : |‖b‖ - ‖a‖| ≤ ‖a - b‖) (hmax : max |‖b‖| |‖a‖| ≤ 2 * ‖b‖) :
    |⟪b, v⟫ * (‖b‖ ^ (n + 1) - ‖a‖ ^ (n + 1)) / (‖a‖ ^ (n + 1) * ‖b‖ ^ (n + 1))| ≤
      (n + 1) * 4 ^ (n + 1) * ‖v‖ * ‖a - b‖ / ‖b‖ ^ (n + 1) := by
  have hpow : |‖b‖ ^ (n + 1) - ‖a‖ ^ (n + 1)| ≤ ‖a - b‖ * (n + 1) * (2 * ‖b‖) ^ n := by
    refine (abs_pow_sub_pow_le _ _ _).trans ?_
    rw [Nat.add_sub_cancel]
    push_cast
    gcongr
  have hαβ' : 0 < ‖a‖ ^ (n + 1) * ‖b‖ ^ (n + 1) := mul_pos (pow_pos hα _) (pow_pos hβ _)
  rw [abs_div, abs_mul, abs_of_pos hαβ', div_le_div_iff₀ hαβ' (pow_pos hβ _)]
  calc |⟪b, v⟫| * |‖b‖ ^ (n + 1) - ‖a‖ ^ (n + 1)| * ‖b‖ ^ (n + 1)
      ≤ (‖b‖ * ‖v‖) * (‖a - b‖ * (n + 1) * (2 * ‖b‖) ^ n) * ‖b‖ ^ (n + 1) := by
        gcongr
        exact abs_real_inner_le_norm _ _
    _ = (n + 1) * 2 ^ n * ‖v‖ * ‖a - b‖ * ‖b‖ ^ (n + 1) * ‖b‖ ^ (n + 1) := by ring
    _ ≤ (n + 1) * 2 ^ n * ‖v‖ * ‖a - b‖ * (2 * ‖a‖) ^ (n + 1) * ‖b‖ ^ (n + 1) := by
        gcongr
    _ ≤ (n + 1) * 4 ^ (n + 1) * ‖v‖ * ‖a - b‖ * (‖a‖ ^ (n + 1) * ‖b‖ ^ (n + 1)) := by
        rw [mul_pow, show (4 : ℝ) ^ (n + 1) = 2 ^ (n + 1) * 2 ^ (n + 1) by
          rw [← mul_pow]; norm_num]
        have : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) := pow_le_pow_right₀ one_le_two n.le_succ
        have h0 : 0 ≤ ‖v‖ * ‖a - b‖ * ‖a‖ ^ (n + 1) * ‖b‖ ^ (n + 1) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left this
          (by positivity : 0 ≤ ((n : ℝ) + 1) * 2 ^ (n + 1) * (‖v‖ * ‖a - b‖ * ‖a‖ ^ (n + 1) *
            ‖b‖ ^ (n + 1)))]

/-- **Smoothness estimate** for the Riesz kernel: if `2 ‖a - b‖ < ‖b‖`, then
`|K_v(a) - K_v(b)| ≤ c_n (n + 2) 4 ^ (n + 1) ‖v‖ ‖a - b‖ / ‖b‖ ^ (n + 1)`. -/
theorem abs_rieszKernel_sub_le (v : E) {a b : E} (h : 2 * ‖a - b‖ < ‖b‖) :
    |rieszKernel v a - rieszKernel v b| ≤ Real.Gamma ((finrank ℝ E + 1) / 2) /
      π ^ (((finrank ℝ E : ℝ) + 1) / 2) * ((finrank ℝ E + 2) * 4 ^ (finrank ℝ E + 1)) * ‖v‖ *
        ‖a - b‖ / ‖b‖ ^ (finrank ℝ E + 1) := by
  set n := finrank ℝ E
  set c : ℝ := Real.Gamma ((n + 1) / 2) / π ^ (((n : ℝ) + 1) / 2)
  have hc : 0 ≤ c := div_nonneg (Real.Gamma_nonneg_of_nonneg (by positivity)) (by positivity)
  have hε := norm_nonneg (a - b)
  have hβ : 0 < ‖b‖ := by linarith
  have htri : ‖b‖ ≤ ‖a‖ + ‖a - b‖ := by
    simpa using norm_sub_le a (a - b)
  have hα : 0 < ‖a‖ := by linarith
  have hαβ : ‖b‖ ≤ 2 * ‖a‖ := by linarith
  have hβα : |‖b‖ - ‖a‖| ≤ ‖a - b‖ := by
    rw [abs_sub_comm]
    exact abs_norm_sub_norm_le a b
  have hmax : max |‖b‖| |‖a‖| ≤ 2 * ‖b‖ := by
    rw [abs_norm, abs_norm]
    exact max_le (by linarith) (by linarith [norm_le_insert' a b, norm_sub_rev a b])
  -- The first term.
  have h₁ : |⟪a - b, v⟫ / ‖a‖ ^ (n + 1)| ≤ 2 ^ (n + 1) * ‖v‖ * ‖a - b‖ / ‖b‖ ^ (n + 1) := by
    rw [abs_div, abs_of_pos (pow_pos hα _), div_le_div_iff₀ (pow_pos hα _) (pow_pos hβ _)]
    calc |⟪a - b, v⟫| * ‖b‖ ^ (n + 1) ≤ (‖a - b‖ * ‖v‖) * (2 * ‖a‖) ^ (n + 1) :=
          mul_le_mul (abs_real_inner_le_norm _ _) (pow_le_pow_left₀ hβ.le hαβ _)
            (by positivity) (by positivity)
      _ = _ := by ring
  have h₂ := abs_inner_mul_pow_sub_pow_div_le v n hα hβ hαβ hβα hmax
  rw [rieszKernel_sub_eq v (norm_pos_iff.1 hα) (norm_pos_iff.1 hβ), abs_mul, abs_of_nonneg hc]
  calc c * |⟪a - b, v⟫ / ‖a‖ ^ (n + 1) + ⟪b, v⟫ * (‖b‖ ^ (n + 1) - ‖a‖ ^ (n + 1)) /
        (‖a‖ ^ (n + 1) * ‖b‖ ^ (n + 1))|
      ≤ c * (2 ^ (n + 1) * ‖v‖ * ‖a - b‖ / ‖b‖ ^ (n + 1) +
        (n + 1) * 4 ^ (n + 1) * ‖v‖ * ‖a - b‖ / ‖b‖ ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add h₁ h₂)) hc
    _ ≤ c * ((n + 2) * 4 ^ (n + 1)) * ‖v‖ * ‖a - b‖ / ‖b‖ ^ (n + 1) := by
        rw [← add_div, mul_div_assoc', div_le_div_iff_of_pos_right (pow_pos hβ _)]
        have : (2 : ℝ) ^ (n + 1) ≤ 4 ^ (n + 1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
        have h0 : 0 ≤ c * ‖v‖ * ‖a - b‖ := by positivity
        nlinarith [mul_le_mul_of_nonneg_left this h0]

/-! ### A Gamma integral -/

/-- `∫₀^∞ t^(-1/2) e^(-r t) dt = √(π / r)`, in the form used for the symbol. -/
private theorem integral_rpow_neg_half_mul_exp {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2) : ℝ) * Real.exp (-(r * t)) = (1 / r) ^ (1 / 2 : ℝ) * √π := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 / 2) (by norm_num) hr
  rw [Real.Gamma_one_half_eq] at h
  rw [← h]
  norm_num

private theorem integrableOn_rpow_neg_half_mul_exp {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ ↦ t ^ (-(1 / 2) : ℝ) * Real.exp (-(r * t))) (Ioi 0) := by
  refine (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1 / 2)) (by norm_num) one_pos
    hr).congr_fun
    (fun t _ ↦ ?_) measurableSet_Ioi
  simp [neg_mul]

/-! ### Derivatives of Gaussians -/

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem re_pi_div_pos {t : ℝ} (ht : 0 < t) : 0 < (((π / t : ℝ)) : ℂ).re := by
  rw [Complex.ofReal_re]
  positivity

/-- The Schwartz function `t^(-n/2) ∂_v exp(-π ‖x‖² / t)`, whose Fourier transform is
`2πi ⟪ξ, v⟫ exp(-π t ‖ξ‖²)`. Averaging it against `t^(-1/2) dt` produces the Riesz kernel and the
Riesz symbol. -/
private def rieszGaussian (v : E) {t : ℝ} (ht : 0 < t) : 𝓢(E, ℂ) :=
  ((t ^ (-(finrank ℝ E : ℝ) / 2) : ℝ) : ℂ) •
    ∂_{v} (SchwartzMap.gaussian (V := E) (re_pi_div_pos ht))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem rieszGaussian_apply (v : E) {t : ℝ} (ht : 0 < t) (z : E) :
    rieszGaussian v ht z = ((-(2 * π) * ⟪z, v⟫ * (t ^ (-((finrank ℝ E : ℝ) + 2) / 2) *
      Real.exp (-(π * ‖z‖ ^ 2 / t))) : ℝ) : ℂ) := by
  have hder : HasFDerivAt (fun x : E ↦ Complex.exp (-(((π / t : ℝ)) : ℂ) * ‖x‖ ^ 2))
      (Complex.exp (-(((π / t : ℝ)) : ℂ) * ‖z‖ ^ 2) •
        ((-(((π / t : ℝ)) : ℂ)) • (Complex.ofRealCLM.comp ((2 : ℕ) • innerSL ℝ z)))) z := by
    have h1 : HasFDerivAt (fun x : E ↦ ((‖x‖ ^ 2 : ℝ) : ℂ))
        (Complex.ofRealCLM.comp ((2 : ℕ) • innerSL ℝ z)) z :=
      Complex.ofRealCLM.hasFDerivAt.comp z (hasStrictFDerivAt_norm_sq z).hasFDerivAt
    have h2 := (h1.const_mul (-(((π / t : ℝ)) : ℂ))).cexp
    simpa only [Complex.ofReal_pow] using h2
  rw [rieszGaussian, smul_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have hfun : ((SchwartzMap.gaussian (re_pi_div_pos ht) : 𝓢(E, ℂ)) : E → ℂ) =
      fun x : E ↦ Complex.exp (-(((π / t : ℝ)) : ℂ) * ‖x‖ ^ 2) :=
    funext fun x ↦ SchwartzMap.gaussian_apply _ x
  rw [hfun, hder.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, innerSL_apply_apply, smul_eq_mul]
  have ht' : (t : ℝ) ^ (-((finrank ℝ E : ℝ) + 2) / 2) = t ^ (-(finrank ℝ E : ℝ) / 2) * t⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add ht]
    ring_nf
  rw [ht']
  push_cast
  rw [show (-(π / t : ℂ) * (‖z‖ : ℂ) ^ 2) = -(π * (‖z‖ : ℂ) ^ 2 / t) by ring, nsmul_eq_mul]
  push_cast
  ring

private theorem fourier_rieszGaussian_apply (v : E) {t : ℝ} (ht : 0 < t) (ξ : E) :
    𝓕 (rieszGaussian v ht) ξ =
      Complex.I * ((2 * π * ⟪ξ, v⟫ * Real.exp (-(π * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) := by
  have hg : (inner ℝ · v : E → ℝ).HasTemperateGrowth := ((innerSL ℝ).flip v).hasTemperateGrowth
  rw [rieszGaussian, FourierTransform.fourier_smul, smul_apply,
    SchwartzMap.fourier_lineDerivOp_eq, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.fourier_coe]
  have hfun : ((SchwartzMap.gaussian (re_pi_div_pos ht) : 𝓢(E, ℂ)) : E → ℂ) =
      fun x : E ↦ Complex.exp (-(((π / t : ℝ)) : ℂ) * ‖x‖ ^ 2) :=
    funext fun x ↦ SchwartzMap.gaussian_apply _ x
  rw [hfun, fourier_gaussian_innerProductSpace (re_pi_div_pos ht)]
  have hπt : (π : ℂ) / (((π / t : ℝ)) : ℂ) = (t : ℂ) := by
    push_cast
    field_simp
  have hcpow : (t : ℂ) ^ ((finrank ℝ E : ℂ) / 2) = ((t ^ ((finrank ℝ E : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow ht.le]
    push_cast
    rfl
  rw [hπt, hcpow]
  have hexp : -(π : ℂ) ^ 2 * (‖ξ‖ : ℂ) ^ 2 / (((π / t : ℝ)) : ℂ) =
      ((-(π * ‖ξ‖ ^ 2 * t) : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [hexp, ← Complex.ofReal_exp]
  have hpow : ((t ^ (-(finrank ℝ E : ℝ) / 2) : ℝ) : ℂ) * ((t ^ ((finrank ℝ E : ℝ) / 2) : ℝ) : ℂ)
      = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add ht, neg_div, neg_add_cancel, Real.rpow_zero,
      Complex.ofReal_one]
  simp only [Complex.real_smul]
  push_cast
  linear_combination (2 * π * Complex.I * ⟪ξ, v⟫ * Complex.exp (-(π * ‖ξ‖ ^ 2 * t))) * hpow

/-! ### Subordination -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The Fourier-side profile `t ↦ t^(-1/2) exp(-π ‖ξ‖² t)` averages to `1 / ‖ξ‖`. -/
private theorem integral_symbolProfile {ξ : E} (hξ : ξ ≠ 0) :
    ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2) : ℝ) * Real.exp (-(π * ‖ξ‖ ^ 2 * t)) = ‖ξ‖⁻¹ := by
  have hr : 0 < π * ‖ξ‖ ^ 2 := by positivity
  rw [integral_rpow_neg_half_mul_exp hr, one_div, Real.inv_rpow hr.le, Real.mul_rpow Real.pi_pos.le
    (by positivity), ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _),
    mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.2 Real.pi_pos).ne', one_mul]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The kernel-side profile `t ↦ t^(-1/2) t^(-(n+2)/2) exp(-π ‖z‖² / t)` averages to
`c_n / ‖z‖ ^ (n + 1)`. -/
private theorem integral_kernelProfile {z : E} (hz : z ≠ 0) :
    ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2) : ℝ) *
        (t ^ (-((finrank ℝ E : ℝ) + 2) / 2) * Real.exp (-(π * ‖z‖ ^ 2 / t))) =
      Real.Gamma ((finrank ℝ E + 1) / 2) / π ^ (((finrank ℝ E : ℝ) + 1) / 2) /
        ‖z‖ ^ (finrank ℝ E + 1) := by
  have hr : 0 < π * ‖z‖ ^ 2 := by positivity
  have ha : (0 : ℝ) < ((finrank ℝ E : ℝ) + 1) / 2 := by positivity
  rw [← setIntegral_congr_fun measurableSet_Ioi (f := fun t : ℝ ↦
      t ^ (-(((finrank ℝ E : ℝ) + 1) / 2 + 1)) * Real.exp (-(π * ‖z‖ ^ 2 / t))) fun t ht ↦ by
    simp only
    rw [← mul_assoc, ← Real.rpow_add (mem_Ioi.1 ht)]
    ring_nf,
    integral_rpow_mul_exp_neg_div_Ioi ha hr, one_div, Real.inv_rpow hr.le,
    Real.mul_rpow Real.pi_pos.le (by positivity)]
  have hz' : (‖z‖ ^ 2) ^ (((finrank ℝ E : ℝ) + 1) / 2) = ‖z‖ ^ (finrank ℝ E + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  rw [hz']
  field_simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem integrableOn_kernelProfile {z : E} (hz : z ≠ 0) :
    IntegrableOn (fun t : ℝ ↦ t ^ (-(1 / 2) : ℝ) *
      (t ^ (-((finrank ℝ E : ℝ) + 2) / 2) * Real.exp (-(π * ‖z‖ ^ 2 / t)))) (Ioi 0) := by
  refine (integrableOn_rpow_mul_exp_neg_div_Ioi (a := ((finrank ℝ E : ℝ) + 1) / 2)
    (by positivity) (by positivity : 0 < π * ‖z‖ ^ 2)).congr_fun (fun t ht ↦ ?_)
    measurableSet_Ioi
  simp only
  rw [← mul_assoc, ← Real.rpow_add (mem_Ioi.1 ht)]
  ring_nf

/-! ### The pairing on the Fourier side -/

/-- Averaging the symbols `2πi ⟪ξ, v⟫ exp(-π t ‖ξ‖²)` of the Gaussian family against
`t^(-1/2) dt` gives `-2π` times the Riesz symbol, also after pairing with an integrable
function. -/
private theorem integral_neg_two_pi_mul_rieszSymbol_mul [Nontrivial E] (v : E) {Φ : E → ℂ}
    (hΦ : Integrable Φ) :
    ∫ ξ, (-(2 * π) * rieszSymbol v ξ) * Φ ξ =
      ∫ t in Ioi (0 : ℝ), ∫ ξ, (Complex.I * ((2 * π * ⟪ξ, v⟫ : ℝ) : ℂ) * Φ ξ) *
        ((t ^ (-(1 / 2) : ℝ) * Real.exp (-(π * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) := by
  set G : ℝ → E → ℂ := fun t ξ ↦ (Complex.I * ((2 * π * ⟪ξ, v⟫ : ℝ) : ℂ) * Φ ξ) *
    ((t ^ (-(1 / 2) : ℝ) * Real.exp (-(π * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ)
  have hmeas : AEStronglyMeasurable (Function.uncurry G)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · refine AEStronglyMeasurable.mul ?_ hΦ.1.comp_snd
      exact (by fun_prop : Measurable fun p : ℝ × E ↦
        Complex.I * ((2 * π * ⟪p.2, v⟫ : ℝ) : ℂ)).aestronglyMeasurable
    · exact (by fun_prop : Measurable fun p : ℝ × E ↦
        ((p.1 ^ (-(1 / 2) : ℝ) * Real.exp (-(π * ‖p.2‖ ^ 2 * p.1)) : ℝ) : ℂ)).aestronglyMeasurable
  -- The `t`-integral of `‖G t ξ‖` is `2π |⟪ξ, v⟫| ‖Φ ξ‖ / ‖ξ‖`.
  have hnorm : ∀ ξ ≠ 0, ∫ t in Ioi (0 : ℝ), ‖G t ξ‖ =
      2 * π * |⟪ξ, v⟫| * ‖Φ ξ‖ * ‖ξ‖⁻¹ := fun ξ hξ ↦ by
    rw [← integral_symbolProfile hξ, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
    simp only [G, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul,
      abs_two, abs_of_pos Real.pi_pos, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (Real.rpow_nonneg ht.le _)]
  have hint : Integrable (Function.uncurry G) ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    rw [integrable_prod_iff' hmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards [Measure.ae_ne volume 0] with ξ hξ
      simp only [Function.uncurry_apply_pair, G]
      exact ((integrableOn_rpow_neg_half_mul_exp (by positivity : 0 < π * ‖ξ‖ ^ 2)).ofReal
        ).const_mul _
    · refine Integrable.congr (f := fun ξ ↦ 2 * π * |⟪ξ, v⟫| * ‖ξ‖⁻¹ * ‖Φ ξ‖) ?_ ?_
      · refine hΦ.norm.bdd_mul (c := 2 * π * ‖v‖) (by fun_prop) (.of_forall fun ξ ↦ ?_)
        rcases eq_or_ne ξ 0 with rfl | hξ
        · simpa using by positivity
        have h1 : |⟪ξ, v⟫| * ‖ξ‖⁻¹ ≤ ‖v‖ := by
          rw [← div_eq_mul_inv, div_le_iff₀ (norm_pos_iff.2 hξ), mul_comm]
          exact abs_real_inner_le_norm _ _
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_assoc]
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
      · filter_upwards [Measure.ae_ne volume 0] with ξ hξ
        simp only [Function.uncurry_apply_pair]
        rw [hnorm ξ hξ]
        ring
  rw [integral_integral_swap hint]
  refine integral_congr_ae ?_
  filter_upwards [Measure.ae_ne volume 0] with ξ hξ
  rw [integral_const_mul, integral_complex_ofReal, integral_symbolProfile hξ, rieszSymbol_apply]
  push_cast
  field_simp

/-! ### The pairing in space -/

/-- Pairing `g` with a kernel integral of `f` is the integral of the kernel against
`⟪g x, f y⟫` over the product, as soon as the kernel is bounded where `g x ≠ 0` and `f y ≠ 0`. -/
private theorem integral_inner_integral_smul {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] {k : E → ℂ} (hk : Measurable k) {f g : E → F}
    (hf : Integrable f) (hg : Integrable g) {B : ℝ}
    (hB : ∀ x y, g x ≠ 0 → f y ≠ 0 → ‖k (x - y)‖ ≤ B) :
    ∫ x, inner ℂ (g x) (∫ y, k (x - y) • f y) =
      ∫ p : E × E, k (p.1 - p.2) * inner ℂ (g p.1) (f p.2) := by
  have hB' : ∀ x y, ‖k (x - y) * inner ℂ (g x) (f y)‖ ≤ B * (‖g x‖ * ‖f y‖) := fun x y ↦ by
    by_cases hx : g x = 0
    · simp [hx]
    by_cases hy : f y = 0
    · simp [hy]
    rw [norm_mul]
    exact mul_le_mul (hB x y hx hy) (norm_inner_le_norm _ _) (norm_nonneg _)
      ((norm_nonneg _).trans (hB x y hx hy))
  have hint : Integrable (fun p : E × E ↦ k (p.1 - p.2) * inner ℂ (g p.1) (f p.2))
      (volume.prod volume) := by
    refine ((hg.norm.mul_prod hf.norm).const_mul B).mono' ?_ (.of_forall fun p ↦ hB' p.1 p.2)
    exact ((hk.comp (by fun_prop)).aestronglyMeasurable).mul
      (hg.1.comp_fst.inner hf.1.comp_snd)
  rw [Measure.volume_eq_prod, integral_prod _ hint]
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  by_cases hx : g x = 0
  · simp [hx]
  have hxint : Integrable fun y ↦ k (x - y) • f y := by
    refine (hf.norm.const_mul B).mono' ((hk.comp (by fun_prop)).aestronglyMeasurable.smul hf.1)
      (.of_forall fun y ↦ ?_)
    by_cases hy : f y = 0
    · simp [hy]
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hB x y hx hy) (norm_nonneg _)
  simp only
  rw [← integral_inner hxint]
  simp_rw [inner_smul_right]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Averaging the Gaussian kernels `-2π ⟪z, v⟫ t^(-(n+2)/2) exp(-π ‖z‖² / t)` against
`t^(-1/2) dt` gives `-2π` times the Riesz kernel. -/
private theorem integral_kernelSubordination (v z : E) :
    ∫ t in Ioi (0 : ℝ), -(2 * π) * ⟪z, v⟫ * (t ^ (-(1 / 2) : ℝ) *
      (t ^ (-((finrank ℝ E : ℝ) + 2) / 2) * Real.exp (-(π * ‖z‖ ^ 2 / t)))) =
      -(2 * π) * rieszKernel v z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rw [integral_const_mul, integral_kernelProfile hz, rieszKernel]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem integral_abs_kernelSubordination (v z : E) :
    ∫ t in Ioi (0 : ℝ), |-(2 * π) * ⟪z, v⟫ * (t ^ (-(1 / 2) : ℝ) *
      (t ^ (-((finrank ℝ E : ℝ) + 2) / 2) * Real.exp (-(π * ‖z‖ ^ 2 / t))))| =
      2 * π * |rieszKernel v z| := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hc : 0 ≤ Real.Gamma ((finrank ℝ E + 1) / 2) / π ^ (((finrank ℝ E : ℝ) + 1) / 2) :=
    div_nonneg (Real.Gamma_nonneg_of_nonneg (by positivity)) (by positivity)
  rw [← setIntegral_congr_fun measurableSet_Ioi (f := fun t ↦ |-(2 * π) * ⟪z, v⟫| *
      (t ^ (-(1 / 2) : ℝ) * (t ^ (-((finrank ℝ E : ℝ) + 2) / 2) *
        Real.exp (-(π * ‖z‖ ^ 2 / t))))) fun t (ht : 0 < t) ↦ by
      rw [abs_mul (-(2 * π) * ⟪z, v⟫), abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _)
        (mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le))],
    integral_const_mul, integral_kernelProfile hz, rieszKernel_apply, abs_mul (-(2 * π)),
    abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * π), abs_div, abs_mul _ ⟪z, v⟫,
    abs_of_nonneg hc, abs_of_pos (pow_pos (norm_pos_iff.2 hz) _)]
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem integrableOn_kernelSubordination (v z : E) :
    IntegrableOn (fun t : ℝ ↦ -(2 * π) * ⟪z, v⟫ * (t ^ (-(1 / 2) : ℝ) *
      (t ^ (-((finrank ℝ E : ℝ) + 2) / 2) * Real.exp (-(π * ‖z‖ ^ 2 / t))))) (Ioi 0) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  exact (integrableOn_kernelProfile hz).const_mul _

/-- Averaging the Gaussian kernels against `t^(-1/2) dt` gives `-2π` times the Riesz kernel,
also after pairing against `⟪g x, f y⟫` for `f` and `g` with separated supports. -/
private theorem integral_neg_two_pi_mul_rieszKernel_mul {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (v : E) {f g : E → F} (hf : Integrable f)
    (hg : Integrable g) {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ x y, g x ≠ 0 → f y ≠ 0 → δ ≤ ‖x - y‖) :
    ∫ t in Ioi (0 : ℝ), ∫ p : E × E, ((-(2 * π) * ⟪p.1 - p.2, v⟫ *
        (t ^ (-(1 / 2) : ℝ) * (t ^ (-((finrank ℝ E : ℝ) + 2) / 2) *
          Real.exp (-(π * ‖p.1 - p.2‖ ^ 2 / t)))) : ℝ) : ℂ) * inner ℂ (g p.1) (f p.2) =
      ∫ p : E × E, ((-(2 * π) * rieszKernel v (p.1 - p.2) : ℝ) : ℂ) *
        inner ℂ (g p.1) (f p.2) := by
  set c : ℝ := Real.Gamma ((finrank ℝ E + 1) / 2) / π ^ (((finrank ℝ E : ℝ) + 1) / 2)
  have hc : 0 ≤ c := div_nonneg (Real.Gamma_nonneg_of_nonneg (by positivity)) (by positivity)
  set q : ℝ → E → ℝ := fun t z ↦ -(2 * π) * ⟪z, v⟫ * (t ^ (-(1 / 2) : ℝ) *
    (t ^ (-((finrank ℝ E : ℝ) + 2) / 2) * Real.exp (-(π * ‖z‖ ^ 2 / t))))
  set H : ℝ → E × E → ℂ := fun t p ↦ (q t (p.1 - p.2) : ℂ) * inner ℂ (g p.1) (f p.2)
  have hmeas : AEStronglyMeasurable (Function.uncurry H)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.prod volume)) := by
    refine AEStronglyMeasurable.mul ?_ (hg.1.comp_fst.inner hf.1.comp_snd).comp_snd
    exact (by fun_prop : Measurable fun r : ℝ × (E × E) ↦
      (q r.1 (r.2.1 - r.2.2) : ℂ)).aestronglyMeasurable
  -- Fubini applies: the `t`-integral of `‖H t p‖` is `2π |K_v(x - y)| ‖⟪g x, f y⟫‖`, which the
  -- separation of the supports bounds by a multiple of `‖g x‖ ‖f y‖`.
  have hint : Integrable (Function.uncurry H)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.prod volume)) := by
    rw [integrable_prod_iff' hmeas]
    refine ⟨.of_forall fun p ↦ ?_, ?_⟩
    · simp only [Function.uncurry_apply_pair, H, q]
      exact ((integrableOn_kernelSubordination v _).ofReal (𝕜 := ℂ)).mul_const _
    simp only [Function.uncurry_apply_pair, H, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    simp_rw [integral_mul_const, q, integral_abs_kernelSubordination]
    refine ((hg.norm.mul_prod hf.norm).const_mul (2 * π * (c * ‖v‖ / δ ^ finrank ℝ E))).mono'
      ?_ (.of_forall fun p ↦ ?_)
    · have hm : Measurable fun p : E × E ↦ 2 * π * |rieszKernel v (p.1 - p.2)| :=
        measurable_const.mul (continuous_abs.measurable.comp
          ((measurable_rieszKernel v).comp (measurable_fst.sub measurable_snd)))
      exact hm.aestronglyMeasurable.mul (hg.1.comp_fst.inner hf.1.comp_snd).norm
    by_cases hx : g p.1 = 0
    · simp [hx]
    by_cases hy : f p.2 = 0
    · simp [hy]
    have hK : |rieszKernel v (p.1 - p.2)| ≤ c * ‖v‖ / δ ^ finrank ℝ E :=
      (abs_rieszKernel_le v _).trans (div_le_div_of_nonneg_left (by positivity)
        (by positivity) (pow_le_pow_left₀ hδ.le (hsep p.1 p.2 hx hy) _))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc 2 * π * |rieszKernel v (p.1 - p.2)| * ‖inner ℂ (g p.1) (f p.2)‖
        = 2 * π * (|rieszKernel v (p.1 - p.2)| * ‖inner ℂ (g p.1) (f p.2)‖) := by ring
      _ ≤ 2 * π * ((c * ‖v‖ / δ ^ finrank ℝ E) * (‖g p.1‖ * ‖f p.2‖)) := by
        gcongr
        exact norm_inner_le_norm _ _
      _ = _ := by ring
  refine (integral_integral_swap hint).trans (integral_congr_ae (.of_forall fun p ↦ ?_))
  simp only [H]
  rw [integral_mul_const, integral_complex_ofReal, integral_kernelSubordination]

/-! ### The kernel representation -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- For one member of the Gaussian family, the pairing of `g` with the multiplier `T_σ f` whose
symbol `σ` is the Fourier transform of the Gaussian derivative is the integral of that
derivative against `⟪g x, f y⟫`. -/
private theorem integral_fourier_rieszGaussian_mul_eq (v : E) {t : ℝ} (ht : 0 < t)
    (f g : Lp F 2 (volume : Measure E)) {f' g' : E → F}
    (hff' : (f : E → F) =ᵐ[volume] f') (hgg' : (g : E → F) =ᵐ[volume] g')
    (hf' : Integrable f') (hg' : Integrable g') :
    ∫ ξ, 𝓕 (rieszGaussian v ht) ξ * inner ℂ ((𝓕 g : Lp F 2 (volume : Measure E)) ξ)
        ((𝓕 f : Lp F 2 (volume : Measure E)) ξ) =
      ∫ p : E × E, rieszGaussian v ht (p.1 - p.2) * inner ℂ (g' p.1) (f' p.2) := by
  set σ := 𝓕 (rieszGaussian v ht)
  have h₁ : ∫ ξ, σ ξ * inner ℂ ((𝓕 g : Lp F 2 (volume : Measure E)) ξ)
      ((𝓕 f : Lp F 2 (volume : Measure E)) ξ) =
      inner ℂ g (Lp.fourierMultiplierCLM F (σ.toLp ∞) f) := by
    rw [Lp.inner_fourierMultiplierCLM_apply]
    refine integral_congr_ae ?_
    filter_upwards [SchwartzMap.coeFn_toLp σ ∞ volume] with ξ hξ
    rw [hξ]
  have h₂ : inner ℂ g (Lp.fourierMultiplierCLM F (σ.toLp ∞) f) =
      ∫ x, inner ℂ (g' x) (∫ y, rieszGaussian v ht (x - y) • f' y) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [SchwartzMap.coeFn_fourierMultiplierCLM_toLp σ f, hgg'] with x hx hgx
    rw [hx, hgx, fourierInv_fourier_eq]
    congr 1
    exact integral_congr_ae (hff'.mono fun y hy ↦ by simp only [hy])
  rw [h₁, h₂]
  exact integral_inner_integral_smul (rieszGaussian v ht).continuous.measurable hf' hg'
    fun x y _ _ ↦ SchwartzMap.norm_le_seminorm ℝ _ _

/-- **The pairing identity.** For `f` and `g` in `L²` with integrable representatives whose
supports are at distance at least `δ > 0`, `⟪g, R_v f⟫ = ∫ ⟪g x, ∫ K_v(x - y) f y dy⟫ dx`. -/
private theorem inner_rieszTransform_eq_integral [Nontrivial E] (v : E)
    (f g : Lp F 2 (volume : Measure E)) {f' g' : E → F}
    (hff' : (f : E → F) =ᵐ[volume] f') (hgg' : (g : E → F) =ᵐ[volume] g')
    (hf' : Integrable f') (hg' : Integrable g') {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x y, g' x ≠ 0 → f' y ≠ 0 → δ ≤ ‖x - y‖) :
    inner ℂ g (rieszTransform F v f) =
      ∫ x, inner ℂ (g' x) (∫ y, (rieszKernel v (x - y) : ℂ) • f' y) := by
  set Φ : E → ℂ := fun ξ ↦ inner ℂ ((𝓕 g : Lp F 2 (volume : Measure E)) ξ)
    ((𝓕 f : Lp F 2 (volume : Measure E)) ξ)
  have hΦ : Integrable Φ := L2.integrable_inner (𝓕 g) (𝓕 f)
  set c : ℝ := Real.Gamma ((finrank ℝ E + 1) / 2) / π ^ (((finrank ℝ E : ℝ) + 1) / 2)
  have hc : 0 ≤ c := div_nonneg (Real.Gamma_nonneg_of_nonneg (by positivity)) (by positivity)
  -- The kernel side, `∫ ⟪g x, ∫ K(x - y) f y dy⟫ dx = ∫ K(x - y) ⟪g x, f y⟫ d(x, y)`.
  have hK := integral_inner_integral_smul (k := fun z ↦ (rieszKernel v z : ℂ)) (by fun_prop)
    hf' hg' (B := c * ‖v‖ / δ ^ finrank ℝ E) fun x y hx hy ↦ by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (abs_rieszKernel_le v _).trans (div_le_div_of_nonneg_left
        (mul_nonneg hc (norm_nonneg _)) (by positivity) (pow_le_pow_left₀ hδ.le (hsep x y hx hy) _))
  refine mul_left_cancel₀ (by simp [Real.pi_ne_zero] : (-(2 * π) : ℂ) ≠ 0) ?_
  calc (-(2 * π) : ℂ) * inner ℂ g (rieszTransform F v f)
      = ∫ ξ, (-(2 * π) * rieszSymbol v ξ) * Φ ξ := by
        rw [rieszTransform_def, Lp.inner_fourierMultiplierCLM_apply, ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [coeFn_rieszSymbolLp v] with ξ hξ
        rw [hξ, mul_assoc]
    _ = ∫ t in Ioi (0 : ℝ), ∫ ξ, (Complex.I * ((2 * π * ⟪ξ, v⟫ : ℝ) : ℂ) * Φ ξ) *
        ((t ^ (-(1 / 2) : ℝ) * Real.exp (-(π * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) :=
        integral_neg_two_pi_mul_rieszSymbol_mul v hΦ
    _ = ∫ t in Ioi (0 : ℝ), ∫ p : E × E, (((-(2 * π) * ⟪p.1 - p.2, v⟫) *
        (t ^ (-(1 / 2) : ℝ) * (t ^ (-((finrank ℝ E : ℝ) + 2) / 2) *
          Real.exp (-(π * ‖p.1 - p.2‖ ^ 2 / t)))) : ℝ) : ℂ) * inner ℂ (g' p.1) (f' p.2) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
        have h := integral_fourier_rieszGaussian_mul_eq v ht f g hff' hgg' hf' hg'
        simp only [fourier_rieszGaussian_apply, rieszGaussian_apply] at h
        calc _ = ((t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * ∫ ξ, Complex.I *
              ((2 * π * ⟪ξ, v⟫ * Real.exp (-(π * ‖ξ‖ ^ 2 * t)) : ℝ) : ℂ) * Φ ξ := by
              rw [← integral_const_mul]
              refine integral_congr_ae (.of_forall fun ξ ↦ ?_)
              push_cast
              ring
          _ = ((t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * ∫ p : E × E, ((-(2 * π) * ⟪p.1 - p.2, v⟫ *
              (t ^ (-((finrank ℝ E : ℝ) + 2) / 2) * Real.exp (-(π * ‖p.1 - p.2‖ ^ 2 / t))) :
                ℝ) : ℂ) * inner ℂ (g' p.1) (f' p.2) :=
              congrArg (fun z ↦ ((t ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * z) h
          _ = _ := by
              rw [← integral_const_mul]
              refine integral_congr_ae (.of_forall fun p ↦ ?_)
              push_cast
              ring
    _ = ∫ p : E × E, ((-(2 * π) * rieszKernel v (p.1 - p.2) : ℝ) : ℂ) *
        inner ℂ (g' p.1) (f' p.2) :=
        integral_neg_two_pi_mul_rieszKernel_mul v hf' hg' hδ hsep
    _ = (-(2 * π) : ℂ) * ∫ x, inner ℂ (g' x) (∫ y, (rieszKernel v (x - y) : ℂ) • f' y) := by
        rw [hK, ← integral_const_mul]
        refine integral_congr_ae (.of_forall fun p ↦ ?_)
        push_cast
        ring

omit [CompleteSpace F] in
/-- Away from the set `s` off which `f` vanishes, the kernel integral of `f` is bounded. -/
private theorem norm_integral_rieszKernel_smul_le (v : E) {f : E → F} (hf : Integrable f)
    {s : Set E} (hf0 : ∀ y, f y ≠ 0 → y ∈ s) {δ : ℝ} (hδ : 0 < δ) {x : E}
    (hx : ∀ y ∈ s, δ ≤ ‖x - y‖) :
    ‖∫ y, rieszKernel v (x - y) • f y‖ ≤ Real.Gamma ((finrank ℝ E + 1) / 2) /
      π ^ (((finrank ℝ E : ℝ) + 1) / 2) * ‖v‖ / δ ^ finrank ℝ E * ∫ y, ‖f y‖ := by
  have hc : 0 ≤ Real.Gamma ((finrank ℝ E + 1) / 2) / π ^ (((finrank ℝ E : ℝ) + 1) / 2) :=
    div_nonneg (Real.Gamma_nonneg_of_nonneg (by positivity)) (by positivity)
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (.of_forall fun _ ↦ norm_nonneg _) (hf.norm.const_mul _)
    (.of_forall fun y ↦ ?_)
  by_cases hy : f y = 0
  · simp [hy]
  dsimp only
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right ((abs_rieszKernel_le v _).trans
    (div_le_div_of_nonneg_left (mul_nonneg hc (norm_nonneg _)) (by positivity)
      (pow_le_pow_left₀ hδ.le (hx y (hf0 y hy)) _))) (norm_nonneg _)

/-- The kernel representation on a compact set `U` at distance at least `δ > 0` from the set `s`
off which `f` vanishes. Pairing `R_v f - K f` with its own restriction to `U` gives, by
`inner_rieszTransform_eq_integral`, `∫_U ‖R_v f - K f‖² = 0`. -/
private theorem ae_rieszTransform_eq_integral_of_isCompact [Nontrivial E] (v : E)
    (f : Lp F 2 (volume : Measure E)) {f' : E → F} (hff' : (f : E → F) =ᵐ[volume] f')
    (hf' : Integrable f') {s U : Set E} (hf'0 : ∀ y, f' y ≠ 0 → y ∈ s) (hUc : IsCompact U)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ x ∈ U, ∀ y ∈ s, δ ≤ ‖x - y‖) :
    ∀ᵐ x, x ∈ U → rieszTransform F v f x = ∫ y, rieszKernel v (x - y) • f' y := by
  set K : E → F := fun x ↦ ∫ y, rieszKernel v (x - y) • f' y
  have hKm : AEStronglyMeasurable K :=
    (((measurable_rieszKernel v).comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable.smul
      hf'.1.comp_snd : AEStronglyMeasurable (fun p : E × E ↦ rieszKernel v (p.1 - p.2) • f' p.2)
        (volume.prod volume)).integral_prod_right'
  have hUm : MeasurableSet U := hUc.measurableSet
  have : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.2 hUc.measure_lt_top.ne
  set B : ℝ := Real.Gamma ((finrank ℝ E + 1) / 2) / π ^ (((finrank ℝ E : ℝ) + 1) / 2) * ‖v‖ /
    δ ^ finrank ℝ E * ∫ y, ‖f' y‖
  have hKB : ∀ x ∈ U, ‖K x‖ ≤ B := fun x hx ↦
    norm_integral_rieszKernel_smul_le v hf' hf'0 hδ (hsep x hx)
  -- The restriction `d` of `w = R_v f - K` to `U` is in `L²`, and is integrable.
  set w : E → F := fun x ↦ rieszTransform F v f x - K x
  set d : E → F := U.indicator w
  have hd : MemLp d 2 := by
    rw [memLp_indicator_iff_restrict hUm.nullMeasurableSet]
    exact ((Lp.memLp _).restrict U).sub (MemLp.of_bound hKm.restrict _
      (ae_restrict_of_forall_mem hUm hKB))
  have hdi : Integrable d := by
    rw [integrable_indicator_iff hUm]
    exact ((memLp_indicator_iff_restrict hUm.nullMeasurableSet).1 hd).integrable one_le_two
  have hd0 : ∀ x, d x ≠ 0 → x ∈ U := fun x hx ↦ by
    by_contra h
    exact hx (indicator_of_notMem h _)
  -- The pairing identity with `g = d`: `∫ ⟪d x, R_v f x⟫ = ∫ ⟪d x, K x⟫`.
  have key := inner_rieszTransform_eq_integral v f (hd.toLp d) hff' hd.coeFn_toLp hf' hdi hδ
    fun x y hx hy ↦ hsep x (hd0 x hx) y (hf'0 y hy)
  have hKc : ∀ x, ∫ y, (rieszKernel v (x - y) : ℂ) • f' y = K x := fun x ↦
    integral_congr_ae (.of_forall fun y ↦ (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm)
  simp_rw [hKc] at key
  rw [L2.inner_def] at key
  have hint₁ : Integrable fun x ↦ inner ℂ (d x) (rieszTransform F v f x) :=
    (L2.integrable_inner (hd.toLp d) (rieszTransform F v f)).congr
      (hd.coeFn_toLp.mono fun x hx ↦ by simp only [hx])
  have hint₂ : Integrable fun x ↦ inner ℂ (d x) (K x) := by
    refine (hdi.norm.const_mul B).mono' (hdi.1.inner hKm) (.of_forall fun x ↦ ?_)
    by_cases hx : d x = 0
    · simp [hx]
    exact (norm_inner_le_norm _ _).trans ((mul_le_mul_of_nonneg_left (hKB x (hd0 x hx))
      (norm_nonneg (d x))).trans_eq (mul_comm _ _))
  -- Hence `∫ ‖d‖² = re ∫ ⟪d x, w x⟫ = 0`.
  have hzero : ∫ x, ‖d x‖ ^ 2 = 0 := by
    have hdw : ∀ x, RCLike.re (inner ℂ (d x) (w x)) = ‖d x‖ ^ 2 := fun x ↦ by
      by_cases hx : x ∈ U
      · simp only [d, indicator_of_mem hx]
        exact inner_self_eq_norm_sq (𝕜 := ℂ) _
      · simp [d, hx]
    have h1 : ∫ x, inner ℂ (d x) (w x) = 0 := by
      simp only [w, inner_sub_right]
      rw [integral_sub hint₁ hint₂, sub_eq_zero, ← key]
      refine integral_congr_ae ?_
      filter_upwards [hd.coeFn_toLp] with x hx
      rw [hx]
    simp_rw [← hdw]
    rw [integral_re (hint₁.sub hint₂ |>.congr (.of_forall fun x ↦ by
      simp only [w, inner_sub_right, Pi.sub_apply])), h1, map_zero]
  rw [integral_eq_zero_iff_of_nonneg (fun x ↦ by positivity)
    ((memLp_two_iff_integrable_sq_norm hd.aestronglyMeasurable).1 hd)] at hzero
  filter_upwards [hzero] with x hx hxU
  rw [Pi.zero_apply, sq_eq_zero_iff, norm_eq_zero] at hx
  simp only [d, indicator_of_mem hxU, w, sub_eq_zero] at hx
  exact hx

/-- In dimension zero the Riesz symbol vanishes, and so does the Riesz transform. -/
private theorem rieszTransform_eq_zero_of_subsingleton [Subsingleton E] (v : E) :
    rieszTransform F v = 0 := by
  have h0 : rieszSymbolLp v = 0 := by
    apply Lp.ext
    filter_upwards [coeFn_rieszSymbolLp v, Lp.coeFn_zero ℂ ∞ (volume : Measure E)] with ξ h₁ h₂
    rw [h₁, h₂, Subsingleton.elim ξ 0, rieszSymbol_zero_right, Pi.zero_apply]
  rw [rieszTransform_def, h0, Lp.fourierMultiplierCLM_zero]

/-- **The kernel of the Riesz transform.** Let `f ∈ L²(E, F)` vanish almost everywhere off a
compact set `s`. Then for almost every `x ∉ s`

`R_v f (x) = ∫ K_v(x - y) f(y) dy`, where `K_v(z) = c_n ⟪z, v⟫ / ‖z‖ ^ (n + 1)`

(`TauCeti.rieszKernel`) and `c_n = Γ((n + 1) / 2) / π ^ ((n + 1) / 2)`. The integral converges
absolutely, since the kernel is bounded for `y ∈ s` and `x` away from `s`. -/
theorem ae_rieszTransform_eq_integral (v : E) (f : Lp F 2 (volume : Measure E)) {s : Set E}
    (hs : IsCompact s) (hf : ∀ᵐ x, x ∉ s → f x = 0) :
    ∀ᵐ x, x ∉ s → rieszTransform F v f x = ∫ y, rieszKernel v (x - y) • f y := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · filter_upwards [Lp.coeFn_zero F 2 (volume : Measure E)] with x hx _
    rw [rieszTransform_eq_zero_of_subsingleton, zero_apply, hx]
    simp [Subsingleton.elim (x - _) (0 : E)]
  -- A representative of `f` vanishing everywhere off `s`.
  set f' : E → F := s.indicator f
  have hff' : (f : E → F) =ᵐ[volume] f' := by
    filter_upwards [hf] with x hx
    by_cases h : x ∈ s
    · simp [f', h]
    · simp [f', h, hx h]
  have hf'0 : ∀ y, f' y ≠ 0 → y ∈ s := fun y hy ↦ by
    by_contra h
    exact hy (indicator_of_notMem h _)
  have : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.2 hs.measure_lt_top.ne
  have hf' : Integrable f' :=
    IntegrableOn.integrable_indicator (((Lp.memLp f).restrict s).integrable one_le_two)
      hs.measurableSet
  -- The representation holds on the compact sets `U k`, at distance `1 / (k + 1)` from `s`.
  have hU : ∀ k : ℕ, ∀ᵐ x, x ∈ closedBall (0 : E) k \ thickening (1 / ((k : ℝ) + 1)) s →
      rieszTransform F v f x = ∫ y, rieszKernel v (x - y) • f' y := fun k ↦
    ae_rieszTransform_eq_integral_of_isCompact v f hff' hf' hf'0
      ((isCompact_closedBall 0 _).diff isOpen_thickening) Nat.one_div_pos_of_nat
        fun x hx y hy ↦ by
        rw [← dist_eq_norm]
        by_contra h
        exact hx.2 (mem_thickening_iff.2 ⟨y, hy, not_le.1 h⟩)
  -- Every `x ∉ s` lies in some `U k`.
  filter_upwards [ae_all_iff.2 hU] with x hx hxs
  have hcl : x ∉ closure s := hs.isClosed.closure_eq.symm ▸ hxs
  rw [closure_eq_iInter_thickening] at hcl
  simp only [mem_iInter, not_forall] at hcl
  obtain ⟨δ, hδ, hxδ⟩ := hcl
  obtain ⟨k, hk⟩ := exists_nat_gt (max ‖x‖ (1 / δ))
  have hk₁ : ‖x‖ ≤ k := (le_max_left _ _).trans hk.le
  have hk₂ : 1 / ((k : ℝ) + 1) ≤ δ := by
    rw [div_le_iff₀ (by positivity)]
    have := (le_max_right ‖x‖ (1 / δ)).trans hk.le
    rw [div_le_iff₀ hδ] at this
    nlinarith
  rw [show ∫ y, rieszKernel v (x - y) • f y = ∫ y, rieszKernel v (x - y) • f' y from
    integral_congr_ae (hff'.mono fun y hy ↦ by simp only [hy])]
  exact hx k ⟨mem_closedBall_zero_iff.2 hk₁, fun h ↦ hxδ (thickening_mono hk₂ s h)⟩

/-- **The Riesz transforms are of weak type `(1, 1)`.** In dimension `n ≥ 1` there is a constant
`A` with `t · |{x | ‖R_v f x‖ > t}| ≤ A ‖f‖₁` for every `f ∈ L²` and every `t`. The Riesz
transform is not bounded on `L¹`; this is the endpoint substitute. It follows from the
Calderón–Zygmund theorem, since `R_v` is bounded on `L²` and its kernel `K_v(x - y)` satisfies the
size and smoothness estimates `abs_rieszKernel_le` and `abs_rieszKernel_sub_le`. -/
theorem exists_mul_volume_lt_enorm_rieszTransform_le [Nontrivial E] (v : E) :
    ∃ A : ℝ≥0, ∀ (f : Lp F 2 (volume : Measure E)) (t : ℝ≥0∞),
      t * volume {x | t < ‖rieszTransform F v f x‖ₑ} ≤ A * ∫⁻ x, ‖f x‖ₑ := by
  set n := finrank ℝ E
  set c : ℝ := Real.Gamma ((n + 1) / 2) / π ^ (((n : ℝ) + 1) / 2)
  have hc : 0 ≤ c := div_nonneg (Real.Gamma_nonneg_of_nonneg (by positivity)) (by positivity)
  set k : E → E → F →L[ℝ] F := fun x y ↦ rieszKernel v (x - y) • ContinuousLinearMap.id ℝ F
  have hkm : StronglyMeasurable (Function.uncurry k) :=
    ((measurable_rieszKernel v).comp
      (measurable_fst.sub measurable_snd)).stronglyMeasurable.smul_const _
  have hk : ∀ x y, ‖k x y‖ ≤ |rieszKernel v (x - y)| := fun x y ↦ by
    simp only [k]
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) ContinuousLinearMap.norm_id_le
  have hsize : ∀ x y, x ≠ y → ‖k x y‖ ≤ (c * ‖v‖).toNNReal * dist x y ^ (-(n : ℝ)) :=
    fun x y hxy ↦ by
      rw [Real.coe_toNNReal _ (by positivity), Real.rpow_neg dist_nonneg, Real.rpow_natCast,
        dist_eq_norm, ← div_eq_mul_inv]
      exact (hk x y).trans (abs_rieszKernel_le v _)
  have hsmooth : ∀ x y y', 2 * dist y y' < dist x y' → ‖k x y - k x y'‖ ≤
      (c * ((n + 2) * 4 ^ (n + 1)) * ‖v‖).toNNReal *
        (dist y y' ^ (1 : ℝ) * dist x y' ^ (-((n : ℝ) + 1))) := fun x y y' h ↦ by
    rw [Real.coe_toNNReal _ (by positivity), Real.rpow_one, Real.rpow_neg dist_nonneg,
      show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
      dist_eq_norm, dist_eq_norm]
    have hab : (x - y) - (x - y') = y' - y := by abel
    have h' : 2 * ‖(x - y) - (x - y')‖ < ‖x - y'‖ := by
      rwa [hab, norm_sub_rev, ← dist_eq_norm, ← dist_eq_norm]
    calc ‖k x y - k x y'‖ ≤ |rieszKernel v (x - y) - rieszKernel v (x - y')| := by
          simp only [k, ← sub_smul]
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_of_le_one_right (abs_nonneg _) ContinuousLinearMap.norm_id_le
      _ ≤ _ := abs_rieszKernel_sub_le v h'
      _ = _ := by
          rw [hab, norm_sub_rev, div_eq_mul_inv]
          ring
  have hrep : ∀ (f : Lp F 2 (volume : Measure E)) (s : Set E), IsCompact s →
      (∀ᵐ x, x ∉ s → f x = 0) → ∀ᵐ x, x ∉ s →
        (rieszTransform F v).restrictScalars ℝ f x = ∫ z, k x z (f z) := fun f s hs hf ↦ by
    filter_upwards [ae_rieszTransform_eq_integral v f hs hf] with x hx hxs
    simp [k, hx hxs]
  exact ContinuousLinearMap.exists_mul_volume_lt_enorm_le_of_norm_sub_le_mul_rpow
    ((rieszTransform F v).restrictScalars ℝ) hkm one_pos hsize hsmooth hrep

end TauCeti
