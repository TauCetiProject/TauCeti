/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian
public import TauCeti.Analysis.PDE.Schrodinger.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The Schrödinger kernel and the dispersive estimate

Let `E` be a real inner product space of finite dimension `d` and `F` a complex Hilbert space.
For `t ≠ 0` the free Schrödinger propagator `S(t) = exp(itΔ)` of
`TauCeti.Analysis.PDE.Schrodinger.Basic` is convolution with the **Schrödinger kernel**

`K_t(x) = (4πit)^{-d/2} exp(i ‖x‖² / (4t))`,

with the principal branch of the power. Since `|K_t(x)| = (4π|t|)^{-d/2}` for every `x`, this
gives the **dispersive estimate**

`‖S(t) f‖_∞ ≤ (4π|t|)^{-d/2} ‖f‖₁`,

the decay in time that drives the Strichartz estimates.

The symbol `exp(-4π² i t ‖ξ‖²)` of `S(t)` is not integrable, so `K_t` is not the inverse Fourier
transform of the symbol in the sense of Lebesgue integrals. The proof instead moves the time off
the imaginary axis. For `ε > 0` the symbol `exp(-4π² (ε + it) ‖ξ‖²)` is a Schwartz function
(`SchwartzMap.gaussian`), so the corresponding `L²` multiplier is convolution with its inverse
Fourier transform, the complex Gaussian `(4π(ε + it))^{-d/2} exp(-‖x‖² / (4(ε + it)))`
(`SchwartzMap.coeFn_fourierMultiplierCLM_toLp` and Mathlib's
`fourier_gaussian_innerProductSpace`). Its modulus is at most `(4π|t|)^{-d/2}` uniformly in `ε`.
As `ε → 0⁺` the symbols converge boundedly to the Schrödinger symbol, so the multipliers converge
to `S(t) f` in `L²` and, along a subsequence, almost everywhere; for `f ∈ L¹` the convolution
integrals converge at every point by dominated convergence.

## Main declarations

* `TauCeti.schrodingerKernel`: the kernel `K_t(x) = (4πit)^{-d/2} exp(i ‖x‖² / (4t))`.
* `TauCeti.norm_schrodingerKernel`: `|K_t(x)| = (4π|t|)^{-d/2}`.
* `TauCeti.coeFn_schrodingerPropagator`: for `t ≠ 0` and `f ∈ L¹ ∩ L²`,
  `S(t) f (x) = ∫ K_t(x - y) f(y) dy` for almost every `x`.
* `TauCeti.ae_norm_schrodingerPropagator_le` and
  `TauCeti.eLpNorm_schrodingerPropagator_top_le`: the dispersive estimate
  `‖S(t) f‖_∞ ≤ (4π|t|)^{-d/2} ‖f‖₁`.
* `TauCeti.coeFn_schrodingerPropagator_toLp_gaussian`: the evolution of the Gaussian
  `g(x) = exp(-π ‖x‖²)`, `S(t) g (x) = (1 + 4πit)^{-d/2} exp(-π ‖x‖² / (1 + 4πit))`.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.2.
-/

public section

noncomputable section

open scoped ENNReal FourierTransform Topology SchwartzMap
open MeasureTheory Complex Filter Real Module FourierTransform

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **Schrödinger kernel** `K_t(x) = (4πit)^{-d/2} exp(i ‖x‖² / (4t))` on a real inner
product space of dimension `d`, with the principal branch of the complex power. For `t ≠ 0` the
propagator `exp(itΔ)` is convolution with `K_t`
(`TauCeti.coeFn_schrodingerPropagator`). -/
def schrodingerKernel (t : ℝ) (x : E) : ℂ :=
  (4 * π * t * I) ^ (-(finrank ℝ E : ℂ) / 2) * cexp ((‖x‖ ^ 2 / (4 * t) : ℝ) * I)

theorem schrodingerKernel_apply (t : ℝ) (x : E) :
    schrodingerKernel t x =
      (4 * π * t * I) ^ (-(finrank ℝ E : ℂ) / 2) * cexp ((‖x‖ ^ 2 / (4 * t) : ℝ) * I) :=
  (rfl)

/-- The Schrödinger kernel has constant modulus `(4π|t|)^{-d/2}`. -/
theorem norm_schrodingerKernel (t : ℝ) (x : E) :
    ‖schrodingerKernel t x‖ = (4 * π * |t|) ^ (-(finrank ℝ E : ℝ) / 2) := by
  have h : (-(finrank ℝ E : ℂ) / 2) = ((-(finrank ℝ E : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [schrodingerKernel, norm_mul, norm_exp_ofReal_mul_I, mul_one, h, norm_cpow_real]
  simp [abs_of_pos pi_pos]

/-! ### Complex Gaussians -/

/-- The inverse Fourier transform `(π / b)^{d/2} exp(-π² ‖v‖² / b)` of the complex Gaussian
`exp(-b ‖ξ‖²)`, in the form of Mathlib's `fourier_gaussian_innerProductSpace`. -/
private def gaussKernel (b : ℂ) (v : E) : ℂ :=
  (π / b) ^ (finrank ℝ E / 2 : ℂ) * cexp (-π ^ 2 * ‖v‖ ^ 2 / b)

private theorem continuous_gaussKernel (b : ℂ) : Continuous (gaussKernel b : E → ℂ) := by
  unfold gaussKernel
  fun_prop

/-- For `0 ≤ re b` the complex Gaussian kernel is bounded by `(π / |b|)^{d/2}`. -/
private theorem norm_gaussKernel_le {b : ℂ} (hb : 0 ≤ b.re) (v : E) :
    ‖gaussKernel b v‖ ≤ (π / ‖b‖) ^ ((finrank ℝ E : ℝ) / 2) := by
  have h : (finrank ℝ E / 2 : ℂ) = ((finrank ℝ E / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [gaussKernel, norm_mul, h, norm_cpow_real, norm_div, norm_real, Real.norm_of_nonneg pi_pos.le]
  refine mul_le_of_le_one_right (by positivity) ?_
  rw [Complex.norm_exp, Real.exp_le_one_iff, div_re]
  have h1 : (-(π : ℂ) ^ 2 * (‖v‖ : ℂ) ^ 2).re = -π ^ 2 * ‖v‖ ^ 2 := by
    simp [← ofReal_pow, ← ofReal_neg, ← ofReal_mul]
  have h2 : (-(π : ℂ) ^ 2 * (‖v‖ : ℂ) ^ 2).im = 0 := by
    simp [← ofReal_pow, ← ofReal_neg, ← ofReal_mul]
  rw [h1, h2, zero_mul, zero_div, add_zero]
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg π, sq_nonneg ‖v‖]) hb)
    (normSq_nonneg b)

private theorem re_exponent (ε t : ℝ) : (4 * π ^ 2 * ((ε : ℂ) + t * I)).re = 4 * π ^ 2 * ε := by
  simp [← ofReal_pow, ← ofReal_ofNat, ← ofReal_mul]

/-- Along complex times `ε + it`, `ε ≥ 0`, the Gaussian kernels are bounded by the modulus
`(4π|t|)^{-d/2}` of the Schrödinger kernel. -/
private theorem norm_gaussKernel_le_of_im {t : ℝ} (ht : t ≠ 0) {ε : ℝ} (hε : 0 ≤ ε) (v : E) :
    ‖gaussKernel (4 * π ^ 2 * (ε + t * I)) v‖ ≤ (4 * π * |t|) ^ (-(finrank ℝ E : ℝ) / 2) := by
  have hb : 0 ≤ (4 * π ^ 2 * ((ε : ℂ) + t * I)).re := by
    rw [re_exponent]
    positivity
  refine (norm_gaussKernel_le hb v).trans ?_
  have ht' : 0 < 4 * π * |t| := by positivity
  have hnorm : 4 * π ^ 2 * |t| ≤ ‖4 * π ^ 2 * ((ε : ℂ) + t * I)‖ := by
    rw [norm_mul, show ‖(4 * π ^ 2 : ℂ)‖ = 4 * π ^ 2 by
      rw [show (4 * π ^ 2 : ℂ) = ((4 * π ^ 2 : ℝ) : ℂ) by push_cast; ring, norm_real,
        Real.norm_of_nonneg (by positivity)]]
    gcongr
    simpa using abs_im_le_norm ((ε : ℂ) + t * I)
  rw [neg_div, Real.rpow_neg ht'.le, ← Real.inv_rpow ht'.le]
  gcongr
  rw [div_le_iff₀ ((by positivity : (0 : ℝ) < 4 * π ^ 2 * |t|).trans_le hnorm)]
  calc π = (4 * π * |t|)⁻¹ * (4 * π ^ 2 * |t|) := by field_simp
    _ ≤ _ := by gcongr

/-- The Gaussian exponents `b_n = 4π² (1 / (n + 1) + it)`, at the complex times `1 / (n + 1) + it`
that approach the imaginary time `it` from the right half-plane. -/
private def approxExponent (t : ℝ) (n : ℕ) : ℂ :=
  4 * π ^ 2 * (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) + t * I)

private theorem re_approxExponent_pos (t : ℝ) (n : ℕ) : 0 < (approxExponent t n).re := by
  rw [approxExponent, re_exponent]
  positivity

private theorem tendsto_approxExponent (t : ℝ) :
    Tendsto (approxExponent t) atTop (𝓝 (4 * π ^ 2 * (t * I))) := by
  have h := ((continuous_ofReal.tendsto 0).comp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).add_const (t * I : ℂ)
  rw [ofReal_zero, zero_add] at h
  exact h.const_mul (4 * π ^ 2 : ℂ)

/-- As the complex time `1 / (n + 1) + it` tends to `it`, the Gaussian kernels converge pointwise
to the Schrödinger kernel. -/
private theorem tendsto_gaussKernel_approxExponent {t : ℝ} (ht : t ≠ 0) (v : E) :
    Tendsto (fun n ↦ gaussKernel (approxExponent t n) v) atTop (𝓝 (schrodingerKernel t v)) := by
  set w : ℂ := 4 * π * t * I
  have hw : w.im ≠ 0 := by simp [w, ht, pi_ne_zero]
  have hw0 : w ≠ 0 := fun h ↦ hw (by simp [h])
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht
  have hb₀ : (4 * π ^ 2 * (t * I) : ℂ) ≠ 0 := by simp [ht, pi_ne_zero]
  have hπ : (π : ℂ) / (4 * π ^ 2 * (t * I)) = w⁻¹ := by
    simp only [w]
    field_simp
  have hslit : w⁻¹ ∈ slitPlane := mem_slitPlane_iff.2 (Or.inr (by simp [hw, hw0]))
  have hcont : ContinuousAt (fun b : ℂ ↦ gaussKernel b v) (4 * π ^ 2 * (t * I)) := by
    unfold gaussKernel
    refine ContinuousAt.mul ?_ ?_
    · refine (continuousAt_cpow_const (hπ ▸ hslit)).comp ?_
      exact continuousAt_const.div continuousAt_id hb₀
    · exact (continuousAt_const.div continuousAt_id hb₀).cexp
  have hval : gaussKernel (4 * π ^ 2 * (t * I)) v = schrodingerKernel t v := by
    have harg : w.arg ≠ π := (mem_slitPlane_iff_arg.1 (mem_slitPlane_iff.2 (Or.inr hw))).1
    rw [gaussKernel, schrodingerKernel, hπ, inv_cpow _ _ harg, ← cpow_neg, neg_div]
    congr 2
    rw [div_eq_iff hb₀]
    push_cast
    field_simp
    rw [I_sq, mul_neg_one]
  exact hval ▸ hcont.tendsto.comp (tendsto_approxExponent t)

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem fourierInv_gaussian {b : ℂ} (hb : 0 < b.re) (v : E) :
    𝓕⁻ (SchwartzMap.gaussian hb : 𝓢(E, ℂ)) v = gaussKernel b v := by
  rw [SchwartzMap.fourierInv_coe, fourierInv_eq_fourier_neg]
  have : ⇑(SchwartzMap.gaussian hb : 𝓢(E, ℂ)) = fun ξ ↦ cexp (-b * ‖ξ‖ ^ 2) :=
    funext (SchwartzMap.gaussian_apply hb)
  rw [this, fourier_gaussian_innerProductSpace hb, norm_neg, gaussKernel]

variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- For `t ≠ 0` the free Schrödinger propagator is convolution with the Schrödinger kernel
`K_t(x) = (4πit)^{-d/2} exp(i ‖x‖² / (4t))`: for every `f ∈ L² ∩ L¹`,
`S(t) f (x) = ∫ K_t(x - y) f(y) dy` for almost every `x`. The integral converges absolutely at
every `x`, since `K_t` is bounded. -/
theorem coeFn_schrodingerPropagator {t : ℝ} (ht : t ≠ 0)
    (f : Lp F 2 (volume : Measure E)) (hf : Integrable f) :
    schrodingerPropagator F t f =ᵐ[volume] fun x ↦ ∫ y, schrodingerKernel t (x - y) • f y := by
  set σ : ℕ → 𝓢(E, ℂ) := fun n ↦ SchwartzMap.gaussian (re_approxExponent_pos t n)
  -- The Schwartz symbols `σ n = exp(-b_n ‖ξ‖²)` converge boundedly to the Schrödinger symbol, so
  -- their multipliers converge to `S(t) f` in `L²`.
  have hlim : Tendsto (fun n ↦ Lp.fourierMultiplierCLM F ((σ n).toLp ∞) f) atTop
      (𝓝 (schrodingerPropagator F t f)) := by
    rw [schrodingerPropagator_def]
    refine Lp.tendsto_fourierMultiplierCLM_apply (C := 1) (.of_forall fun n ↦ ?_) ?_ f
    · refine SchwartzMap.norm_toLp_top_le.trans
        (SchwartzMap.seminorm_le_bound ℝ 0 0 _ zero_le_one fun ξ ↦ ?_)
      simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero, σ, SchwartzMap.gaussian_apply,
        Complex.norm_exp, Real.exp_le_one_iff]
      rw [← ofReal_pow, re_mul_ofReal, neg_re]
      nlinarith [re_approxExponent_pos t n, sq_nonneg ‖ξ‖]
    · filter_upwards [ae_all_iff.2 fun n ↦ (σ n).coeFn_toLp ∞ (volume : Measure E),
        (memLp_schrodingerSymbol t (volume : Measure E)).coeFn_toLp] with ξ h₁ h₂
      simp only [h₁, h₂, σ, SchwartzMap.gaussian_apply, schrodingerSymbol_apply]
      have h := (((tendsto_approxExponent t).neg.mul_const ((‖ξ‖ : ℂ) ^ 2)).cexp)
      convert h using 3
      push_cast
      ring
  -- Along a subsequence the convergence holds almost everywhere.
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hrep : ∀ᵐ x ∂(volume : Measure E), ∀ n,
      Lp.fourierMultiplierCLM F ((σ n).toLp ∞) f x =
        ∫ y, gaussKernel (approxExponent t n) (x - y) • f y :=
    ae_all_iff.2 fun n ↦ (SchwartzMap.coeFn_fourierMultiplierCLM_toLp (σ n) f).mono
      fun x hx ↦ by simpa only [σ, fourierInv_gaussian] using hx
  filter_upwards [hae, hrep] with x hx hxr
  refine tendsto_nhds_unique hx ?_
  simp only [hxr]
  -- Dominated convergence in `y`, with the dominating function `(4π|t|)^{-d/2} ‖f y‖`.
  refine (tendsto_integral_of_dominated_convergence
    (fun y ↦ (4 * π * |t|) ^ (-(finrank ℝ E : ℝ) / 2) * ‖f y‖)
    (fun n ↦ (((continuous_gaussKernel _).comp (continuous_const.sub continuous_id)
      ).aestronglyMeasurable.smul (Lp.aestronglyMeasurable f)))
    (hf.norm.const_mul _) (fun n ↦ .of_forall fun y ↦ ?_)
    (.of_forall fun y ↦ (tendsto_gaussKernel_approxExponent ht (x - y)).smul_const _)).comp
    hns.tendsto_atTop
  simp only [Pi.smul_apply', Function.comp_apply, Pi.sub_apply, id, norm_smul]
  exact mul_le_mul_of_nonneg_right (norm_gaussKernel_le_of_im ht (by positivity) _)
    (norm_nonneg _)

/-- **The dispersive estimate** for the free Schrödinger equation, pointwise form: for `t ≠ 0`
and `f ∈ L² ∩ L¹`, `|S(t) f (x)| ≤ (4π|t|)^{-d/2} ‖f‖₁` for almost every `x`. -/
theorem ae_norm_schrodingerPropagator_le {t : ℝ} (ht : t ≠ 0)
    (f : Lp F 2 (volume : Measure E)) (hf : Integrable f) :
    ∀ᵐ x ∂(volume : Measure E), ‖schrodingerPropagator F t f x‖ ≤
      (4 * π * |t|) ^ (-(finrank ℝ E : ℝ) / 2) * ∫ y, ‖f y‖ := by
  filter_upwards [coeFn_schrodingerPropagator ht f hf] with x hx
  rw [hx, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hf.norm.const_mul _) (.of_forall fun y ↦ ?_)
  rw [norm_smul, norm_schrodingerKernel]

/-- **The dispersive estimate** for the free Schrödinger equation: for `t ≠ 0` and
`f ∈ L² ∩ L¹`, `‖S(t) f‖_∞ ≤ (4π|t|)^{-d/2} ‖f‖₁`. -/
theorem eLpNorm_schrodingerPropagator_top_le {t : ℝ} (ht : t ≠ 0)
    (f : Lp F 2 (volume : Measure E)) (hf : Integrable f) :
    eLpNorm (schrodingerPropagator F t f) ∞ volume ≤
      ENNReal.ofReal ((4 * π * |t|) ^ (-(finrank ℝ E : ℝ) / 2)) * eLpNorm f 1 volume := by
  rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
  refine (eLpNormEssSup_le_of_ae_bound (ae_norm_schrodingerPropagator_le ht f hf)).trans_eq ?_
  rw [ENNReal.ofReal_mul (by positivity), ofReal_integral_norm_eq_lintegral_enorm hf,
    eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]

/-! ### The evolution of a Gaussian -/

/-- **The Schrödinger evolution of a Gaussian.** The Gaussian `g(x) = exp(-π ‖x‖²)`, which is its
own Fourier transform, evolves into the complex Gaussian

`S(t) g (x) = (1 + 4πit)^{-d/2} exp(-π ‖x‖² / (1 + 4πit))`,

with the principal branch of the power. -/
theorem coeFn_schrodingerPropagator_toLp_gaussian (t : ℝ) :
    schrodingerPropagator ℂ t
        ((SchwartzMap.gaussian (b := π) (by simpa using pi_pos) : 𝓢(E, ℂ)).toLp 2) =ᵐ[volume]
      fun x ↦ (1 + 4 * π * t * I) ^ (-(finrank ℝ E : ℂ) / 2) *
        cexp (-π * ‖x‖ ^ 2 / (1 + 4 * π * t * I)) := by
  have hπ : 0 < (π : ℂ).re := by simpa using pi_pos
  set b : ℂ := π * (1 + 4 * π * t * I)
  have hb : 0 < b.re := by
    have : b.re = π := by simp [b]
    rw [this]
    exact pi_pos
  have hfourier : ∀ ξ : E, 𝓕 (𝓕⁻ (SchwartzMap.gaussian hb : 𝓢(E, ℂ))) ξ =
      schrodingerSymbol t ξ • 𝓕 (SchwartzMap.gaussian hπ : 𝓢(E, ℂ)) ξ := fun ξ ↦ by
    rw [FourierTransform.fourier_fourierInv_eq, SchwartzMap.fourier_coe]
    have : ⇑(SchwartzMap.gaussian hπ : 𝓢(E, ℂ)) = fun ξ ↦ cexp (-π * ‖ξ‖ ^ 2) :=
      funext (SchwartzMap.gaussian_apply hπ)
    rw [this, fourier_gaussian_innerProductSpace hπ, div_self (ofReal_ne_zero.2 pi_ne_zero),
      one_cpow, one_mul, SchwartzMap.gaussian_apply, schrodingerSymbol_apply, smul_eq_mul,
      ← Complex.exp_add]
    congr 1
    simp only [b]
    push_cast
    field_simp
    ring
  have h := SchwartzMap.toLp_eq_fourierMultiplierCLM_of_fourier_eq_smul _
    (memLp_schrodingerSymbol t (volume : Measure E)).coeFn_toLp hfourier
  rw [schrodingerPropagator_def, ← h]
  filter_upwards [(𝓕⁻ (SchwartzMap.gaussian hb : 𝓢(E, ℂ))).coeFn_toLp 2] with x hx
  have h1 : (1 + 4 * π * t * I : ℂ).arg ≠ π :=
    (mem_slitPlane_iff_arg.1 (mem_slitPlane_iff.2 (Or.inl (by simp)))).1
  have h0 : (1 + 4 * π * t * I : ℂ) ≠ 0 := fun h ↦ by simpa using congrArg re h
  rw [hx, fourierInv_gaussian, gaussKernel]
  congr 1
  · rw [show (π : ℂ) / b = (1 + 4 * π * t * I)⁻¹ by
        simp only [b]
        field_simp, inv_cpow _ _ h1, ← cpow_neg, neg_div]
  · congr 1
    simp only [b]
    field_simp

end TauCeti
