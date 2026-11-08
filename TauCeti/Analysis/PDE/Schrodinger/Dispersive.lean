/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian
public import TauCeti.Analysis.PDE.Schrodinger.Basic

/-!
# The kernel of the Schrödinger propagator and the dispersive estimate

On a finite-dimensional real inner product space `E` of dimension `n`, the Schrödinger propagator
`S(t) = exp(itΔ)` (`TauCeti.schrodingerPropagator`) is, for `t ≠ 0`, convolution with the kernel

`K_t(x) = (4πit)^(-n/2) exp(i ‖x‖² / (4t))`,

where the power is the principal one. This file proves that for every `f ∈ L²` which is also
integrable, `S(t) f = K_t ⋆ f` almost everywhere
(`TauCeti.schrodingerPropagator_ae_eq_integral`). Since `|K_t| = (4π|t|)^(-n/2)`, this gives the
**dispersive estimate**

`‖S(t) f‖_∞ ≤ (4π|t|)^(-n/2) ‖f‖₁`

(`TauCeti.eLpNorm_schrodingerPropagator_le`), the decay in time with exponent `n/2` that drives the
Strichartz estimates.

## The argument

The symbol `exp(-4π² i t ‖ξ‖²)` of `S(t)` is the Gaussian `exp(-b ‖ξ‖²)` at the boundary value
`b₀ = 4π² i t` of the half-plane `0 < Re b`, where it is not integrable. For `b = ε + 4π² i t`
with `ε > 0` the Gaussian is a Schwartz function (`SchwartzMap.gaussian`), so the multiplier with
this symbol is convolution with its inverse Fourier transform
(`SchwartzMap.coeFn_fourierMultiplierCLM_toLp`), the complex Gaussian

`(π / b)^(n/2) exp(-π² ‖x‖² / b)`

(`SchwartzMap.fourierInv_gaussian`). These kernels are bounded by `(4π|t|)^(-n/2)` uniformly in
`ε`, because `|b| ≥ 4π²|t|` and `Re (1 / b) > 0`, and they converge pointwise to `K_t` as `ε → 0`.
As `ε → 0` the multipliers converge strongly to `S(t)` on `L²`
(`MeasureTheory.Lp.tendsto_fourierMultiplierCLM_apply`), hence almost everywhere along a
subsequence, while for integrable `f` the convolution integrals converge at every point by
dominated convergence.

## Main declarations

* `TauCeti.schrodingerKernel`: the kernel `K_t`.
* `TauCeti.norm_schrodingerKernel`: `|K_t(x)| = (4π|t|)^(-n/2)`.
* `TauCeti.schrodingerPropagator_ae_eq_integral`: `S(t) f = K_t ⋆ f` for integrable `f ∈ L²`.
* `TauCeti.norm_schrodingerPropagator_apply_le`, `TauCeti.eLpNorm_schrodingerPropagator_le`: the
  dispersive estimate.
* `TauCeti.coeFn_schrodingerPropagator_toLp_gaussian`: the evolution of the Gaussian
  `g(x) = exp(-π ‖x‖²)`, `S(t) g (x) = (1 + 4πit)^(-n/2) exp(-π ‖x‖² / (1 + 4πit))`.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.2.
-/

public section

noncomputable section

open scoped ENNReal FourierTransform Topology SchwartzMap
open MeasureTheory Filter Complex
open Real hiding exp

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **kernel of the Schrödinger propagator** `exp(itΔ)` on a space of dimension `n`:
`K_t(x) = (4πit)^(-n/2) exp(i ‖x‖² / (4t))`, with the principal power. It is meaningful only for
`t ≠ 0`. -/
def schrodingerKernel (t : ℝ) (x : E) : ℂ :=
  ((4 * π * t * I) ^ ((Module.finrank ℝ E : ℂ) / 2))⁻¹ * cexp (((‖x‖ ^ 2 / (4 * t) : ℝ) : ℂ) * I)

theorem schrodingerKernel_apply (t : ℝ) (x : E) :
    schrodingerKernel t x =
      ((4 * π * t * I) ^ ((Module.finrank ℝ E : ℂ) / 2))⁻¹ *
        cexp (((‖x‖ ^ 2 / (4 * t) : ℝ) : ℂ) * I) :=
  (rfl)

/-- The Schrödinger kernel has constant modulus `(4π|t|)^(-n/2)`. -/
theorem norm_schrodingerKernel (t : ℝ) (x : E) :
    ‖schrodingerKernel t x‖ = (4 * π * |t|) ^ (-(Module.finrank ℝ E : ℝ) / 2) := by
  have hs : (Module.finrank ℝ E : ℂ) / 2 = (((Module.finrank ℝ E : ℝ) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have hn : ‖(4 * π * t * I : ℂ)‖ = 4 * π * |t| := by
    simp [abs_of_pos pi_pos]
  rw [schrodingerKernel_apply, norm_mul, norm_inv, hs, norm_cpow_real, norm_exp_ofReal_mul_I,
    mul_one, hn, neg_div, rpow_neg (by positivity)]

/-! ### The regularized kernels -/

/-- The inverse Fourier transform of the Gaussian `exp(-b ‖ξ‖²)`, `0 < Re b`. -/
private def gaussianKernel (b : ℂ) (x : E) : ℂ :=
  (π / b) ^ ((Module.finrank ℝ E : ℂ) / 2) * cexp (-π ^ 2 * ‖x‖ ^ 2 / b)

/-- The regularized kernels at `b = ε + 4π² i t`, `ε > 0`, are bounded by `(4π|t|)^(-n/2)`. -/
private theorem norm_gaussianKernel_le {t : ℝ} (ht : t ≠ 0) {b : ℂ} (hb : 0 ≤ b.re)
    (hbt : b.im = 4 * π ^ 2 * t) (x : E) :
    ‖gaussianKernel b x‖ ≤ (4 * π * |t|) ^ (-(Module.finrank ℝ E : ℝ) / 2) := by
  have hs : (Module.finrank ℝ E : ℂ) / 2 = (((Module.finrank ℝ E : ℝ) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  have h4 : 0 < 4 * π * |t| := by positivity
  have hb' : 4 * π ^ 2 * |t| ≤ ‖b‖ := by
    calc 4 * π ^ 2 * |t| = |b.im| := by
          rw [hbt, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * π ^ 2)]
      _ ≤ ‖b‖ := abs_im_le_norm b
  have hb0 : 0 < ‖b‖ := lt_of_lt_of_le (by positivity) hb'
  -- The modulus of the power.
  have hpow : ‖(π / b) ^ ((Module.finrank ℝ E : ℂ) / 2)‖ ≤
      (4 * π * |t|) ^ (-(Module.finrank ℝ E : ℝ) / 2) := by
    rw [hs, norm_cpow_real, norm_div, norm_real, Real.norm_of_nonneg pi_pos.le, neg_div,
      rpow_neg h4.le, ← inv_rpow h4.le]
    refine rpow_le_rpow (by positivity) ?_ (by positivity)
    rw [div_le_iff₀ hb0, inv_mul_eq_div, le_div_iff₀ h4]
    nlinarith [pi_pos]
  -- The Gaussian factor has modulus at most one, since `Re (1 / b) ≥ 0`.
  have hexp : ‖cexp (-π ^ 2 * ‖x‖ ^ 2 / b)‖ ≤ 1 := by
    rw [norm_exp, Real.exp_le_one_iff, div_eq_mul_inv]
    have : (-(π : ℂ) ^ 2 * (‖x‖ : ℂ) ^ 2) = ((-(π ^ 2 * ‖x‖ ^ 2) : ℝ) : ℂ) := by push_cast; ring
    rw [this, re_ofReal_mul, inv_re]
    exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg ‖x‖, sq_nonneg π])
      (div_nonneg hb (normSq_nonneg b))
  rw [gaussianKernel, norm_mul]
  exact (mul_le_mul hpow hexp (norm_nonneg _) (by positivity)).trans_eq (mul_one _)

/-- At the boundary value `b₀ = 4π² i t` the regularized kernel is continuous in `b` and equals
the Schrödinger kernel. -/
private theorem tendsto_gaussianKernel {t : ℝ} (ht : t ≠ 0) (x : E) :
    Tendsto (fun b ↦ gaussianKernel b x) (𝓝 (((4 * π ^ 2 * t : ℝ) : ℂ) * I))
      (𝓝 (schrodingerKernel t x)) := by
  set b₀ : ℂ := ((4 * π ^ 2 * t : ℝ) : ℂ) * I
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 pi_ne_zero
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht
  have hb₀ : b₀ ≠ 0 := by
    simp [b₀, ht, pi_ne_zero]
  have hq : π / b₀ = (4 * π * t * I)⁻¹ := by
    simp only [b₀]
    push_cast
    field_simp
  have him : (4 * π * t * I : ℂ).im ≠ 0 := by
    simp [ht, pi_ne_zero]
  have hslit : π / b₀ ∈ slitPlane := by
    rw [hq, mem_slitPlane_iff]
    right
    rw [inv_im]
    exact div_ne_zero (neg_ne_zero.2 him) (normSq_pos.2 fun h ↦ him (by rw [h, zero_im])).ne'
  have hcont : ContinuousAt (fun b ↦ gaussianKernel b x) b₀ :=
    ((continuousAt_cpow_const hslit).comp (continuousAt_const.div continuousAt_id hb₀)).mul
      (continuousAt_const.div continuousAt_id hb₀).cexp
  have hval : gaussianKernel b₀ x = schrodingerKernel t x := by
    rw [gaussianKernel, schrodingerKernel_apply, hq,
      inv_cpow _ _ fun h ↦ him (arg_eq_pi_iff.1 h).2]
    congr 2
    simp only [b₀]
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  exact hval ▸ hcont.tendsto

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-! ### The kernel representation and the dispersive estimate -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The regularized Gaussian Fourier multipliers `exp(-b_k ‖ξ‖²)` converge strongly to the
Schrödinger propagator `S(t)` when `b_k → 4π² t i` with `0 < Re b_k`. -/
private theorem tendsto_fourierMultiplierCLM_gaussian_schrodingerPropagator {t : ℝ}
    {b : ℕ → ℂ} (hbre : ∀ k, 0 < (b k).re)
    (hb : Tendsto b atTop (𝓝 (((4 * π ^ 2 * t : ℝ) : ℂ) * I)))
    (f : Lp F 2 (volume : Measure E)) :
    Tendsto (fun k ↦ Lp.fourierMultiplierCLM F
      ((SchwartzMap.gaussian (hbre k) : 𝓢(E, ℂ)).toLp ∞) f) atTop
      (𝓝 (schrodingerPropagator F t f)) := by
  set b₀ : ℂ := ((4 * π ^ 2 * t : ℝ) : ℂ) * I
  rw [schrodingerPropagator_def]
  refine Lp.tendsto_fourierMultiplierCLM_apply (C := 1) (Eventually.of_forall fun k ↦
    SchwartzMap.norm_toLp_top_le.trans (SchwartzMap.seminorm_le_bound ℝ 0 0 _ zero_le_one
      fun ξ ↦ ?_)) ?_ f
  · simp only [pow_zero, norm_iteratedFDeriv_zero, one_mul, SchwartzMap.gaussian_apply]
    rw [norm_cexp_neg_mul_sq, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (hbre k).le) (sq_nonneg _)
  · filter_upwards [ae_all_iff.2 fun k ↦
        (SchwartzMap.gaussian (hbre k) : 𝓢(E, ℂ)).coeFn_toLp ∞ volume,
      (memLp_schrodingerSymbol (E := E) t).coeFn_toLp] with ξ h₁ h₂
    simp only [h₁, h₂, SchwartzMap.gaussian_apply]
    have hval : cexp (-b₀ * (‖ξ‖ : ℂ) ^ 2) = schrodingerSymbol t ξ := by
      rw [schrodingerSymbol_apply]
      congr 1
      simp only [b₀]
      push_cast
      ring
    rw [← hval]
    exact ((Complex.continuous_exp.comp (continuous_neg.mul continuous_const)).tendsto
      b₀).comp hb

/-- For integrable `f`, the regularized convolution integrals `∫ G_{b_k}(x - y) f(y) dy` converge
at every point `x` to `∫ K_t(x - y) f(y) dy`. -/
private theorem tendsto_integral_gaussianKernel_smul {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] {t : ℝ} (ht : t ≠ 0)
    {b : ℕ → ℂ} (hbre : ∀ k, 0 ≤ (b k).re) (hbim : ∀ k, (b k).im = 4 * π ^ 2 * t)
    (hb : Tendsto b atTop (𝓝 (((4 * π ^ 2 * t : ℝ) : ℂ) * I)))
    (f : E → G) (hf : Integrable f) (x : E) :
    Tendsto (fun k ↦ ∫ y, gaussianKernel (b k) (x - y) • f y) atTop
      (𝓝 (∫ y, schrodingerKernel t (x - y) • f y)) := by
  refine tendsto_integral_of_dominated_convergence
    (fun y ↦ (4 * π * |t|) ^ (-(Module.finrank ℝ E : ℝ) / 2) * ‖f y‖) (fun k ↦ ?_)
    (hf.norm.const_mul _) (fun k ↦ Eventually.of_forall fun y ↦ ?_)
    (Eventually.of_forall fun y ↦ ?_)
  · have hc : Continuous fun y ↦ gaussianKernel (b k) (x - y) := by
      unfold gaussianKernel
      fun_prop
    exact hc.aestronglyMeasurable.smul hf.aestronglyMeasurable
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_right
      (norm_gaussianKernel_le ht (hbre k) (hbim k) (x - y)) (norm_nonneg _)
  · exact ((tendsto_gaussianKernel ht (x - y)).comp hb).smul_const _

/-- **The kernel of the Schrödinger propagator.** For `t ≠ 0` and `f ∈ L²` integrable,
`S(t) f(x) = ∫ K_t(x - y) f(y) dy` for almost every `x`. -/
theorem schrodingerPropagator_ae_eq_integral {t : ℝ} (ht : t ≠ 0)
    (f : Lp F 2 (volume : Measure E)) (hf : Integrable f) :
    schrodingerPropagator F t f =ᵐ[volume] fun x ↦ ∫ y, schrodingerKernel t (x - y) • f y := by
  set b₀ : ℂ := ((4 * π ^ 2 * t : ℝ) : ℂ) * I
  set b : ℕ → ℂ := fun k ↦ ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) + b₀
  have hbre : ∀ k, 0 < (b k).re := fun k ↦ by
    rw [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero]
    positivity
  have hbim : ∀ k, (b k).im = 4 * π ^ 2 * t := fun k ↦ by
    rw [add_im, ofReal_im, mul_I_im, ofReal_re, zero_add]
  have hb : Tendsto b atTop (𝓝 b₀) := by
    have h := (continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [b] using h.add_const b₀
  set σ : ℕ → 𝓢(E, ℂ) := fun k ↦ SchwartzMap.gaussian (hbre k)
  have hL2 : Tendsto (fun k ↦ Lp.fourierMultiplierCLM F ((σ k).toLp ∞) f) atTop
      (𝓝 (schrodingerPropagator F t f)) :=
    tendsto_fourierMultiplierCLM_gaussian_schrodingerPropagator hbre hb f
  -- The regularized multipliers are convolutions with the regularized kernels.
  have hconv : ∀ k, Lp.fourierMultiplierCLM F ((σ k).toLp ∞) f =ᵐ[volume]
      fun x ↦ ∫ y, gaussianKernel (b k) (x - y) • f y := fun k ↦ by
    filter_upwards [SchwartzMap.coeFn_fourierMultiplierCLM_toLp (σ k) f] with x hx
    simp only [hx, σ, SchwartzMap.fourierInv_gaussian, gaussianKernel]
  have hlim := tendsto_integral_gaussianKernel_smul ht (fun k ↦ (hbre k).le) hbim hb f hf
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hL2).exists_seq_tendsto_ae
  filter_upwards [hae, ae_all_iff.2 hconv] with x hx hxc
  refine tendsto_nhds_unique hx ?_
  simp only [hxc]
  exact (hlim x).comp hns.tendsto_atTop

/-- **The dispersive estimate**, pointwise: for `t ≠ 0` and integrable `f ∈ L²`,
`|S(t) f(x)| ≤ (4π|t|)^(-n/2) ‖f‖₁` for almost every `x`. -/
theorem norm_schrodingerPropagator_apply_le {t : ℝ} (ht : t ≠ 0)
    (f : Lp F 2 (volume : Measure E)) (hf : Integrable f) :
    ∀ᵐ x ∂volume, ‖schrodingerPropagator F t f x‖ ≤
      (4 * π * |t|) ^ (-(Module.finrank ℝ E : ℝ) / 2) * ∫ y, ‖f y‖ := by
  filter_upwards [schrodingerPropagator_ae_eq_integral ht f hf] with x hx
  rw [hx, ← integral_const_mul]
  exact norm_integral_le_of_norm_le (hf.norm.const_mul _) (Eventually.of_forall fun y ↦ by
    rw [norm_smul, norm_schrodingerKernel])

/-- **The dispersive estimate** `‖S(t) f‖_∞ ≤ (4π|t|)^(-n/2) ‖f‖₁` for `t ≠ 0` and integrable
`f ∈ L²`. -/
theorem eLpNorm_schrodingerPropagator_le {t : ℝ} (ht : t ≠ 0)
    (f : Lp F 2 (volume : Measure E)) (hf : Integrable f) :
    eLpNorm (schrodingerPropagator F t f) ∞ volume ≤
      ENNReal.ofReal ((4 * π * |t|) ^ (-(Module.finrank ℝ E : ℝ) / 2)) * eLpNorm f 1 volume := by
  rw [eLpNorm_exponent_top, eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm hf, ← ENNReal.ofReal_mul (by positivity)]
  · exact eLpNormEssSup_le_of_ae_bound (norm_schrodingerPropagator_apply_le ht f hf)
  all_goals exact Lp.aestronglyMeasurable _

/-! ### The evolution of a Gaussian -/

/-- **The Schrödinger evolution of a Gaussian.** The Gaussian `g(x) = exp(-π ‖x‖²)`, which is its
own Fourier transform, evolves into the complex Gaussian

`S(t) g (x) = (1 + 4πit)^(-n/2) exp(-π ‖x‖² / (1 + 4πit))`,

with the principal power. -/
theorem coeFn_schrodingerPropagator_toLp_gaussian (t : ℝ) :
    schrodingerPropagator ℂ t
        ((SchwartzMap.gaussian (b := π) (by simpa using pi_pos) : 𝓢(E, ℂ)).toLp 2) =ᵐ[volume]
      fun x ↦ (1 + 4 * π * t * I) ^ (-(Module.finrank ℝ E : ℂ) / 2) *
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
    rw [this, fourier_gaussian_innerProductSpace hπ]
    simp only [div_self (ofReal_ne_zero.2 pi_ne_zero), one_cpow, one_mul,
      SchwartzMap.gaussian_apply, schrodingerSymbol_apply, smul_eq_mul]
    rw [← Complex.exp_add]
    congr 1
    simp only [b]
    push_cast
    field_simp
    ring
  have h := SchwartzMap.toLp_eq_fourierMultiplierCLM_of_fourier_eq_smul _
    (memLp_schrodingerSymbol (E := E) t).coeFn_toLp hfourier
  rw [schrodingerPropagator_def, ← h]
  filter_upwards [(𝓕⁻ (SchwartzMap.gaussian hb : 𝓢(E, ℂ))).coeFn_toLp 2] with x hx
  have h1 : (1 + 4 * π * t * I : ℂ).arg ≠ π :=
    (mem_slitPlane_iff_arg.1 (mem_slitPlane_iff.2 (Or.inl (by simp)))).1
  have h0 : (1 + 4 * π * t * I : ℂ) ≠ 0 := fun h ↦ by simpa using congrArg re h
  -- The coefficient `π / b` of the inverse-Fourier Gaussian is `(1 + 4πit)⁻¹`.
  have hcoeff : (π : ℂ) / b = (1 + 4 * π * t * I)⁻¹ := by
    simp only [b]
    field_simp
  rw [hx, SchwartzMap.fourierInv_gaussian]
  congr 1
  · rw [hcoeff, inv_cpow _ _ h1, ← cpow_neg, neg_div]
  · congr 1
    simp only [b]
    field_simp

end TauCeti
