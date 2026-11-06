/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Schrodinger.Propagator
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The kernel of the Schrödinger propagator and the dispersive estimate

Let `E` be a real inner product space of dimension `d` and `F` a complex Hilbert space. For
`t ≠ 0` the Schrödinger propagator `S(t) = exp (i t Δ)` on `L²(E, F)`
(`TauCeti.schrodingerPropagator`) is convolution with the **Schrödinger kernel**

`K_t(x) = (4π i t)^{-d/2} exp (i ‖x‖² / (4t))`,

on every `f ∈ L² ∩ L¹`. The kernel has constant modulus `(4π |t|)^{-d/2}`, which gives the
**dispersive estimate**

`‖S(t) f‖_∞ ≤ (4π |t|)^{-d/2} ‖f‖₁`.

Here `(4π i t)^{-d/2}` is the principal branch of `((4π i t)⁻¹)^{d/2}`. The estimate is the
decay input of the Strichartz estimates: unlike the conservation of the `L²` norm, it records that
solutions of the free Schrödinger equation spread out.

## Proof

The symbol `exp (-4π² i t ‖ξ‖²)` of `S(t)` is a Gaussian `ξ ↦ exp (-b ‖ξ‖²)` with the purely
imaginary parameter `b = 4π² i t`, which is not integrable. Adding `ε > 0` to `b` gives Schwartz
symbols whose multipliers are convolutions with the explicit kernels
`(π / b) ^ (d/2) exp (-π² ‖x‖² / b)` (Mathlib's `fourier_gaussian_innerProductSpace`). As
`ε → 0` the multipliers converge strongly to `S(t)` and, for `f ∈ L¹`, the convolutions converge
at every point by dominated convergence, because the regularised kernels are bounded by
`(4π |t|)^{-d/2}` uniformly in `ε`.

## Main declarations

* `TauCeti.schrodingerKernel`: the kernel `K_t`.
* `TauCeti.norm_schrodingerKernel`: `‖K_t(x)‖ = (4π |t|)^{-d/2}`.
* `TauCeti.schrodingerPropagator_ae_eq_integral`: `S(t) f = K_t ⋆ f` for `f ∈ L² ∩ L¹`.
* `TauCeti.ae_norm_schrodingerPropagator_le`: the dispersive estimate.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.2, equations (2.21)–(2.23).
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 4.3.1.
-/

public section

noncomputable section

open MeasureTheory Complex Filter
open scoped ENNReal FourierTransform Topology Real SchwartzMap

namespace TauCeti

section Kernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **Schrödinger kernel** `K_t(x) = (4π i t)^{-d/2} exp (i ‖x‖² / (4t))` on a real normed
space of dimension `d`, where the power is the principal branch of `((4π i t)⁻¹)^{d/2}`. For
`t ≠ 0` the Schrödinger propagator `S(t)` is convolution with `K_t`
(`TauCeti.schrodingerPropagator_ae_eq_integral`). -/
def schrodingerKernel (t : ℝ) (x : E) : ℂ :=
  (4 * π * t * I)⁻¹ ^ ((Module.finrank ℝ E : ℂ) / 2) * cexp (‖x‖ ^ 2 / (4 * t) * I)

theorem schrodingerKernel_apply (t : ℝ) (x : E) :
    schrodingerKernel t x =
      (4 * π * t * I)⁻¹ ^ ((Module.finrank ℝ E : ℂ) / 2) * cexp (‖x‖ ^ 2 / (4 * t) * I) :=
  (rfl)

/-- The Schrödinger kernel has constant modulus `(4π |t|)^{-d/2}`. -/
theorem norm_schrodingerKernel (t : ℝ) (x : E) :
    ‖schrodingerKernel t x‖ = (4 * π * |t|) ^ (-((Module.finrank ℝ E : ℝ) / 2)) := by
  have h₁ : ‖cexp (‖x‖ ^ 2 / (4 * t) * I)‖ = 1 := by
    rw [show (‖x‖ : ℂ) ^ 2 / (4 * t) = ((‖x‖ ^ 2 / (4 * t) : ℝ) : ℂ) by push_cast; ring]
    exact norm_exp_ofReal_mul_I _
  have h₂ : ((Module.finrank ℝ E : ℂ) / 2) = (((Module.finrank ℝ E : ℝ) / 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [schrodingerKernel_apply, norm_mul, h₁, mul_one, h₂, norm_cpow_real, norm_inv,
    Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]
  congr 2
  simp [abs_of_pos Real.pi_pos]

/-! ### Gaussian regularisation -/

/-- The kernel `(π / b) ^ (d/2) exp (-π² ‖x‖² / b)` of the Fourier multiplier with symbol
`ξ ↦ exp (-b ‖ξ‖²)`, `0 < re b`. -/
private def gaussianKernel (b : ℂ) (x : E) : ℂ :=
  (π / b) ^ ((Module.finrank ℝ E : ℂ) / 2) * cexp (-π ^ 2 * ‖x‖ ^ 2 / b)

/-- At the purely imaginary parameter `4π² i t`, the Gaussian kernel is the Schrödinger kernel. -/
private theorem gaussianKernel_eq_schrodingerKernel {t : ℝ} (ht : t ≠ 0) (x : E) :
    gaussianKernel (4 * π ^ 2 * t * I) x = schrodingerKernel t x := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht
  rw [gaussianKernel, schrodingerKernel_apply]
  congr 2
  · field_simp
  · field_simp
    ring_nf
    simp only [I_sq]
    ring

/-- The parameters `ε + 4π² i t` with `ε ≥ 0` lie in the closed right half-plane, at distance at
least `4π² |t|` from `0`; there the Gaussian kernel is bounded by `(4π |t|)^{-d/2}`. -/
private theorem norm_gaussianKernel_le {ε t : ℝ} (hε : 0 ≤ ε) (ht : t ≠ 0) (x : E) :
    ‖gaussianKernel (ε + 4 * π ^ 2 * t * I) x‖ ≤
      (4 * π * |t|) ^ (-((Module.finrank ℝ E : ℝ) / 2)) := by
  set b : ℂ := ε + 4 * π ^ 2 * t * I
  have hbre : b.re = ε := by simp [b, ← ofReal_pow]
  have hbim : b.im = 4 * π ^ 2 * t := by simp [b, ← ofReal_pow]
  have hb : 4 * π ^ 2 * |t| ≤ ‖b‖ := by
    calc 4 * π ^ 2 * |t| = |b.im| := by
          rw [hbim, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 4 * π ^ 2)]
      _ ≤ ‖b‖ := abs_im_le_norm b
  have hb0 : 0 < ‖b‖ := lt_of_lt_of_le (by positivity) hb
  -- The Gaussian factor has modulus at most `1`, since `re (1 / b) ≥ 0`.
  have hexp : ‖cexp (-π ^ 2 * ‖x‖ ^ 2 / b)‖ ≤ 1 := by
    rw [norm_exp, Real.exp_le_one_iff, div_re]
    have : (-π ^ 2 * (‖x‖ : ℂ) ^ 2).im = 0 := by simp [← ofReal_pow]
    rw [this, zero_mul, zero_div, add_zero, hbre]
    have : (-π ^ 2 * (‖x‖ : ℂ) ^ 2).re = -(π ^ 2 * ‖x‖ ^ 2) := by simp [← ofReal_pow]
    rw [this, neg_mul, neg_div]
    exact neg_nonpos.2 (div_nonneg (by positivity) (normSq_nonneg b))
  have h₂ : ((Module.finrank ℝ E : ℂ) / 2) = (((Module.finrank ℝ E : ℝ) / 2 : ℝ) : ℂ) := by
    push_cast; ring
  rw [gaussianKernel, norm_mul, h₂, norm_cpow_real]
  refine (mul_le_of_le_one_right (by positivity) hexp).trans ?_
  rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity)]
  refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
  rw [norm_div, norm_real, Real.norm_of_nonneg Real.pi_pos.le, div_le_iff₀ hb0]
  calc π = (4 * π * |t|)⁻¹ * (4 * π ^ 2 * |t|) := by
        field_simp [abs_pos.2 ht, Real.pi_pos.ne']
    _ ≤ (4 * π * |t|)⁻¹ * ‖b‖ := by gcongr

private theorem continuous_gaussianKernel (b : ℂ) : Continuous (gaussianKernel (E := E) b) := by
  unfold gaussianKernel
  fun_prop

/-- Away from `b = 0`, on the imaginary axis, the Gaussian kernel depends continuously on `b`. -/
private theorem continuousAt_gaussianKernel {t : ℝ} (ht : t ≠ 0) (x : E) :
    ContinuousAt (fun b ↦ gaussianKernel b x) (4 * π ^ 2 * t * I) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht
  have hb : (4 * π ^ 2 * t * I : ℂ) ≠ 0 := by simp [hπ, ht']
  -- `π / (4π² i t) = -i / (4π t)` is purely imaginary and nonzero, so off the branch cut.
  have hslit : (π / (4 * π ^ 2 * t * I) : ℂ) ∈ slitPlane := by
    have : (π / (4 * π ^ 2 * t * I) : ℂ) = ((-(4 * π * t)⁻¹ : ℝ) : ℂ) * I := by
      push_cast
      field_simp
      simp
    rw [this, mem_slitPlane_iff]
    right
    simp [Real.pi_ne_zero, ht]
  unfold gaussianKernel
  exact ((continuousAt_cpow_const hslit).comp (continuousAt_const.div continuousAt_id hb)).mul
    (continuousAt_const.div continuousAt_id hb).cexp

end Kernel

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

private theorem fourierInv_gaussian {b : ℂ} (hb : 0 < b.re) (x : E) :
    𝓕⁻ (SchwartzMap.gaussian hb : 𝓢(E, ℂ)) x = gaussianKernel b x := by
  have h : (SchwartzMap.gaussian hb : E → ℂ) = fun v ↦ cexp (-b * ‖v‖ ^ 2) :=
    funext (SchwartzMap.gaussian_apply hb)
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, h,
    fourier_gaussian_innerProductSpace hb, norm_neg, gaussianKernel]

/-! ### The kernel representation and the dispersive estimate -/

/-- For `t ≠ 0` the Schrödinger propagator is convolution with the Schrödinger kernel: for
`f ∈ L² ∩ L¹`, `S(t) f x = ∫ K_t(x - y) f(y) dy` for almost every `x`, the integral converging
at every `x`. -/
theorem schrodingerPropagator_ae_eq_integral {t : ℝ} (ht : t ≠ 0)
    (f : Lp F 2 (volume : Measure E)) (hf : Integrable f) :
    schrodingerPropagator t f =ᵐ[volume] fun x ↦ ∫ y, schrodingerKernel t (x - y) • f y := by
  -- Regularise the parameter `4π² i t` of the symbol to `b n = 1 / (n + 1) + 4π² i t`.
  set ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  set b : ℕ → ℂ := fun n ↦ (ε n : ℂ) + 4 * π ^ 2 * t * I
  have hε : ∀ n, 0 < ε n := fun n ↦ Nat.one_div_pos_of_nat
  have hb : ∀ n, 0 < (b n).re := fun n ↦ by simpa [b, ← ofReal_pow] using hε n
  have hbt : Tendsto b atTop (𝓝 (4 * π ^ 2 * t * I)) := by
    have h0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have := ((continuous_ofReal.tendsto 0).comp h0).add_const (4 * π ^ 2 * t * I : ℂ)
    rwa [ofReal_zero, zero_add] at this
  set T : ℕ → Lp F 2 (volume : Measure E) := fun n ↦
    Lp.fourierMultiplierCLM F ((SchwartzMap.gaussian (hb n) : 𝓢(E, ℂ)).toLp ∞) f
  -- The regularised multipliers converge to `S(t) f` in `L²`.
  have hL2 : Tendsto T atTop (𝓝 (schrodingerPropagator t f)) := by
    rw [schrodingerPropagator_def]
    refine Lp.tendsto_fourierMultiplierCLM_apply (C := 1) (Eventually.of_forall fun n ↦ ?_) ?_ f
    · refine Lp.norm_top_le_of_ae_bound zero_le_one ?_
      filter_upwards [(SchwartzMap.gaussian (hb n) : 𝓢(E, ℂ)).coeFn_toLp ∞ volume] with ξ h
      rw [h, SchwartzMap.gaussian_apply, norm_exp, Real.exp_le_one_iff]
      have : (-b n * (‖ξ‖ : ℂ) ^ 2).re = -((b n).re * ‖ξ‖ ^ 2) := by simp [← ofReal_pow]
      rw [this, neg_nonpos]
      exact mul_nonneg (hb n).le (sq_nonneg _)
    · filter_upwards [ae_all_iff.2 fun n ↦
          (SchwartzMap.gaussian (hb n) : 𝓢(E, ℂ)).coeFn_toLp ∞ volume,
        (memLp_schrodingerSymbol volume t).coeFn_toLp] with ξ h₁ h₂
      simp only [h₁, h₂, SchwartzMap.gaussian_apply, schrodingerSymbol_apply]
      have hc : Continuous fun c : ℂ ↦ cexp (-c * ‖ξ‖ ^ 2) := by fun_prop
      exact (hc.tendsto _).comp hbt
  -- Each regularised multiplier is convolution with a Gaussian kernel.
  have hconv : ∀ᵐ x ∂(volume : Measure E), ∀ n, T n x = ∫ y, gaussianKernel (b n) (x - y) • f y :=
    ae_all_iff.2 fun n ↦ by
      filter_upwards [SchwartzMap.coeFn_fourierMultiplierCLM_toLp
        (SchwartzMap.gaussian (hb n) : 𝓢(E, ℂ)) f] with x hx
      simp only [T, hx, fourierInv_gaussian]
  -- At every point the convolutions converge, by dominated convergence.
  have hpt : ∀ x, Tendsto (fun n ↦ ∫ y, gaussianKernel (b n) (x - y) • f y) atTop
      (𝓝 (∫ y, schrodingerKernel t (x - y) • f y)) := fun x ↦ by
    refine tendsto_integral_of_dominated_convergence
      (fun y ↦ (4 * π * |t|) ^ (-((Module.finrank ℝ E : ℝ) / 2)) * ‖f y‖) (fun n ↦ ?_)
      (hf.norm.const_mul _) (fun n ↦ ae_of_all _ fun y ↦ ?_) (ae_of_all _ fun y ↦ ?_)
    · exact ((continuous_gaussianKernel (b n)).comp
        (continuous_const.sub continuous_id)).aestronglyMeasurable.smul (Lp.aestronglyMeasurable f)
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (norm_gaussianKernel_le (hε n).le ht _) (norm_nonneg _)
    · rw [← gaussianKernel_eq_schrodingerKernel ht]
      exact ((continuousAt_gaussianKernel ht (x - y)).tendsto.comp hbt).smul_const _
  -- Along a subsequence, `T n → S(t) f` almost everywhere.
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hL2).exists_seq_tendsto_ae
  filter_upwards [hae, hconv] with x hx hxc
  refine tendsto_nhds_unique hx ?_
  simp only [hxc]
  exact (hpt x).comp hns.tendsto_atTop

/-- **The dispersive estimate** for the Schrödinger propagator: for `t ≠ 0` and `f ∈ L² ∩ L¹`,
`‖S(t) f‖_∞ ≤ (4π |t|)^{-d/2} ‖f‖₁`, where `d` is the dimension of `E`. -/
theorem ae_norm_schrodingerPropagator_le {t : ℝ} (ht : t ≠ 0)
    (f : Lp F 2 (volume : Measure E)) (hf : Integrable f) :
    ∀ᵐ x ∂(volume : Measure E), ‖schrodingerPropagator t f x‖ ≤
      (4 * π * |t|) ^ (-((Module.finrank ℝ E : ℝ) / 2)) * ∫ y, ‖f y‖ := by
  filter_upwards [schrodingerPropagator_ae_eq_integral ht f hf] with x hx
  rw [hx, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae (ae_of_all _ fun y ↦ ?_))
  simp only [norm_smul, norm_schrodingerKernel]

end TauCeti
