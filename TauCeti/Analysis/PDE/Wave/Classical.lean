/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Wave.Energy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Calculus.IntervalIntegral.ParametricPrimitive
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Fourier.Continuous

/-!
# Classical solutions of the wave equation with Schwartz data

On a finite-dimensional real inner product space `E`, the solution of the wave equation
`∂ₜ²u = Δu` with Cauchy data `u(0) = f`, `∂ₜu(0) = g` is, on the Fourier side,

`𝓕 u(t) ξ = cos(2π t ‖ξ‖) 𝓕 f ξ + sin(2π t ‖ξ‖) / (2π ‖ξ‖) 𝓕 g ξ`.

For Schwartz data `f, g` this file takes the inverse Fourier integral of the right-hand side at
every time (`TauCeti.waveSolution`) and shows that it is a classical solution, and that it agrees
with the `L²` solution `cos(tD) f + D⁻¹ sin(tD) g` given by the wave propagators, `D = √(-Δ)`, and
with every strong `L²` solution with the same data:

* **Smoothness** (`TauCeti.contDiff_waveSolution`). `(t, x) ↦ u(t, x)` is `C^∞` on `ℝ × E`.
* **The equation** (`TauCeti.deriv_deriv_waveSolution`). `∂ₜ²u(t, x) = Δu(t, x)` at every point.
  More precisely, `∂ₜ` maps the solution with data `(f, g)` to the solution with data `(g, Δf)`
  (`TauCeti.hasDerivAt_waveSolution`, `TauCeti.deriv_waveSolution`), and `Δ` maps it to the
  solution with data `(Δf, Δg)` (`TauCeti.laplacian_waveSolution`).
* **The Cauchy data** (`TauCeti.waveSolution_time_zero`, `TauCeti.deriv_waveSolution_time_zero`).
  `u(0, x) = f x` and `∂ₜu(0, x) = g x`.
* **Agreement with the propagators**
  (`TauCeti.waveSolution_ae_eq_waveCosPropagator_add_waveSinPropagator`). At every time, `u(t)` is
  a representative of `cos(tD) f + D⁻¹ sin(tD) g` in `L²(E, F)`.
* **Strong solutions are classical** (`TauCeti.IsWaveSolutionOn.ae_eq_waveSolution`). Every strong
  `L²` solution of the free equation on an interval of times containing `0`, with data `f` and `g`
  at time `0`, agrees almost everywhere with `u(t)` at every time of the interval.

## The arguments

The time derivatives of the symbols, `∂ₜ cos(tω) = -ω² sin(tω) / ω` and
`∂ₜ (sin(tω) / ω) = cos(tω)` with `ω = 2π ‖ξ‖` (`TauCeti.hasDerivAt_waveCosSymbol`,
`TauCeti.hasDerivAt_waveSinSymbol`), grow at most like `‖ξ‖²`, locally uniformly in `t`, while
`𝓕 f` and `𝓕 g` decay rapidly, so time derivatives pass under the inverse Fourier integral by
dominated convergence. Since `𝓕 (Δ f) = -4π² ‖ξ‖² 𝓕 f`, the time derivative is again a solution,
with data `(g, Δf)`. Spatial derivatives pass under the integral for the same reason
(`TauCeti.laplacian_fourierInv`). The agreement with strong solutions is Duhamel's formula
`TauCeti.IsWaveSolutionOn.eq_waveCosPropagator_add_waveSinPropagator_add_integral`.

Joint smoothness in `(t, x)` uses the half-wave decomposition
`cos(2π t ‖ξ‖) = (𝐞(t ‖ξ‖) + 𝐞(-t ‖ξ‖)) / 2`. Each half,
`(t, x) ↦ ∫ 𝐞(±t ‖ξ‖ + ⟪ξ, x⟫) 𝓕 f ξ dξ`, is a Fourier integral on `ℝ × E` of the image of the
measure `𝓕 f ξ dξ` under the cone map `ξ ↦ (±‖ξ‖, ξ)`, so it is smooth by Mathlib's
`VectorFourier.contDiff_fourierIntegral`, since the image measure has moments of every order. The
`sin` part is the time primitive `∫₀ᵗ cos(sD) g ds` of a smooth function.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Chapter 2 (the Fourier representation of the free wave
  propagators).
-/

public section

noncomputable section

open scoped FourierTransform Laplacian SchwartzMap ContDiff
open MeasureTheory Filter Real

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-! ### The solution -/

/-- The solution of the wave equation `∂ₜ²u = Δu` on `ℝ × E` with Schwartz Cauchy data
`u(0) = f`, `∂ₜu(0) = g`: the inverse Fourier integral, at every time `t`, of
`cos(2π t ‖ξ‖) 𝓕 f ξ + sin(2π t ‖ξ‖) / (2π ‖ξ‖) 𝓕 g ξ`. -/
def waveSolution (f g : 𝓢(E, F)) (t : ℝ) (x : E) : F :=
  𝓕⁻ (fun ξ ↦ waveCosSymbol t ξ • 𝓕 f ξ + waveSinSymbol t ξ • 𝓕 g ξ) x

theorem waveSolution_def (f g : 𝓢(E, F)) (t : ℝ) :
    waveSolution f g t = 𝓕⁻ (fun ξ ↦ waveCosSymbol t ξ • 𝓕 f ξ + waveSinSymbol t ξ • 𝓕 g ξ) :=
  (rfl)

private theorem continuous_waveIntegrand (f g : 𝓢(E, F)) (t : ℝ) :
    Continuous fun ξ ↦ waveCosSymbol t ξ • 𝓕 f ξ + waveSinSymbol t ξ • 𝓕 g ξ :=
  ((continuous_waveCosSymbol t).smul (𝓕 f).continuous).add
    ((continuous_waveSinSymbol t).smul (𝓕 g).continuous)

private theorem norm_waveIntegrand_le (f g : 𝓢(E, F)) (t : ℝ) (ξ : E) :
    ‖waveCosSymbol t ξ • 𝓕 f ξ + waveSinSymbol t ξ • 𝓕 g ξ‖ ≤ ‖𝓕 f ξ‖ + |t| * ‖𝓕 g ξ‖ :=
  (norm_add_le _ _).trans
    (add_le_add (norm_waveCosSymbol_smul_le t ξ _) (norm_waveSinSymbol_smul_le t ξ _))

private theorem integrable_pow_mul_waveIntegrand (f g : 𝓢(E, F)) (t : ℝ) (n : ℕ) :
    Integrable fun ξ ↦ ‖ξ‖ ^ n * ‖waveCosSymbol t ξ • 𝓕 f ξ + waveSinSymbol t ξ • 𝓕 g ξ‖ := by
  refine (((𝓕 f).integrable_pow_mul volume n).add
    (((𝓕 g).integrable_pow_mul volume n).const_mul |t|)).mono'
    ((continuous_norm.pow n).mul (continuous_waveIntegrand f g t).norm).aestronglyMeasurable
    (ae_of_all _ fun ξ ↦ ?_)
  rw [norm_mul, norm_norm, norm_pow, norm_norm]
  calc ‖ξ‖ ^ n * ‖waveCosSymbol t ξ • 𝓕 f ξ + waveSinSymbol t ξ • 𝓕 g ξ‖
      ≤ ‖ξ‖ ^ n * (‖𝓕 f ξ‖ + |t| * ‖𝓕 g ξ‖) :=
        mul_le_mul_of_nonneg_left (norm_waveIntegrand_le f g t ξ) (by positivity)
    _ = ‖ξ‖ ^ n * ‖𝓕 f ξ‖ + |t| * (‖ξ‖ ^ n * ‖𝓕 g ξ‖) := by ring

/-- The time derivative of the wave solution with data `(f, g)` is the wave solution with data
`(g, Δf)`. -/
theorem hasDerivAt_waveSolution (f g : 𝓢(E, F)) (t : ℝ) (x : E) :
    HasDerivAt (fun s ↦ waveSolution f g s x) (waveSolution g (Δ f) t x) t := by
  have hderiv : ∀ s ξ, HasDerivAt (fun r ↦ waveCosSymbol r ξ • 𝓕 f ξ + waveSinSymbol r ξ • 𝓕 g ξ)
      ((laplacianSymbol ξ * waveSinSymbol s ξ) • 𝓕 f ξ + waveCosSymbol s ξ • 𝓕 g ξ) s :=
    fun s ξ ↦ ((hasDerivAt_waveCosSymbol s ξ).smul_const _).add
      ((hasDerivAt_waveSinSymbol s ξ).smul_const _)
  have hcont : Continuous fun ξ ↦
      (laplacianSymbol ξ * waveSinSymbol t ξ) • 𝓕 f ξ + waveCosSymbol t ξ • 𝓕 g ξ :=
    (((Complex.continuous_ofReal.comp laplacianSymbol.continuous).mul
      (continuous_waveSinSymbol t)).smul (𝓕 f).continuous).add
      ((continuous_waveCosSymbol t).smul (𝓕 g).continuous)
  have hb : Integrable fun ξ ↦ 4 * π ^ 2 * (|t| + 1) * (‖ξ‖ ^ 2 * ‖𝓕 f ξ‖) + ‖𝓕 g ξ‖ :=
    (((𝓕 f).integrable_pow_mul volume 2).const_mul _).add (𝓕 g).integrable.norm
  have hbd : ∀ s ∈ Metric.ball t 1, ∀ ξ,
      ‖(laplacianSymbol ξ * waveSinSymbol s ξ) • 𝓕 f ξ + waveCosSymbol s ξ • 𝓕 g ξ‖ ≤
        4 * π ^ 2 * (|t| + 1) * (‖ξ‖ ^ 2 * ‖𝓕 f ξ‖) + ‖𝓕 g ξ‖ := fun s hs ξ ↦ by
    have hs' : |s| ≤ |t| + 1 := by
      have := abs_sub_abs_le_abs_sub s t
      rw [Metric.mem_ball, Real.dist_eq] at hs
      linarith
    refine (norm_add_le _ _).trans (add_le_add ?_ (norm_waveCosSymbol_smul_le s ξ _))
    rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, laplacianSymbol_apply, abs_neg,
      abs_of_nonneg (by positivity)]
    calc 4 * π ^ 2 * ‖ξ‖ ^ 2 * ‖waveSinSymbol s ξ‖ * ‖𝓕 f ξ‖
        ≤ 4 * π ^ 2 * ‖ξ‖ ^ 2 * (|t| + 1) * ‖𝓕 f ξ‖ := by
          gcongr
          exact (norm_waveSinSymbol_le s ξ).trans hs'
      _ = 4 * π ^ 2 * (|t| + 1) * (‖ξ‖ ^ 2 * ‖𝓕 f ξ‖) := by ring
  have h := hasDerivAt_fourierInv_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds t one_pos)
    (Eventually.of_forall fun s ↦ (continuous_waveIntegrand f g s).aestronglyMeasurable)
    ((integrable_waveCosSymbol_smul (𝓕 f).integrable t).add
      (integrable_waveSinSymbol_smul (𝓕 g).integrable t))
    hcont.aestronglyMeasurable (ae_of_all _ fun ξ s hs ↦ hbd s hs ξ) hb
    (ae_of_all _ fun ξ s _ ↦ hderiv s ξ) x
  refine h.congr_deriv ?_
  rw [waveSolution_def]
  refine congrArg (fun G : E → F ↦ 𝓕⁻ G x) (funext fun ξ ↦ ?_)
  rw [SchwartzMap.fourier_laplacian_apply_eq_laplacianSymbol_smul, smul_smul,
    mul_comm (waveSinSymbol t ξ), add_comm (waveCosSymbol t ξ • 𝓕 g ξ)]

/-- The Laplacian of the wave solution with data `(f, g)` is the wave solution with data
`(Δf, Δg)`. -/
@[simp]
theorem laplacian_waveSolution (f g : 𝓢(E, F)) (t : ℝ) :
    Δ (waveSolution f g t) = waveSolution (Δ f) (Δ g) t := by
  rw [waveSolution_def, laplacian_fourierInv (fun n _ ↦ integrable_pow_mul_waveIntegrand f g t n)
    (continuous_waveIntegrand f g t).aestronglyMeasurable, waveSolution_def]
  congr 1 with ξ
  rw [SchwartzMap.fourier_laplacian_apply_eq_laplacianSymbol_smul,
    SchwartzMap.fourier_laplacian_apply_eq_laplacianSymbol_smul, smul_add,
    smul_comm _ (waveCosSymbol t ξ), smul_comm _ (waveSinSymbol t ξ)]

/-- The time derivative of the wave solution with data `(f, g)` is the wave solution with data
`(g, Δf)`. -/
@[simp]
theorem deriv_waveSolution (f g : 𝓢(E, F)) (t : ℝ) (x : E) :
    deriv (fun s ↦ waveSolution f g s x) t = waveSolution g (Δ f) t x :=
  (hasDerivAt_waveSolution f g t x).deriv

/-- **The wave equation.** The wave solution satisfies `∂ₜ²u = Δu` at every point. -/
theorem deriv_deriv_waveSolution (f g : 𝓢(E, F)) (t : ℝ) (x : E) :
    deriv (fun s ↦ deriv (fun r ↦ waveSolution f g r x) s) t = Δ (waveSolution f g t) x := by
  simp only [deriv_waveSolution, laplacian_waveSolution]

/-! ### Smoothness in space and time -/

/-- The pairing `((τ, ξ), (t, x)) ↦ -(τ t + ⟪ξ, x⟫)` of `ℝ × E` with itself, for which the
Fourier integral is the inverse Fourier integral in space and time. -/
private def spaceTimePairing : (ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ :=
  -((ContinuousLinearMap.mul ℝ ℝ).bilinearComp (ContinuousLinearMap.fst ℝ ℝ E)
      (ContinuousLinearMap.fst ℝ ℝ E) +
    ((innerSL ℝ (E := E)).bilinearComp (ContinuousLinearMap.snd ℝ ℝ E)
      (ContinuousLinearMap.snd ℝ ℝ E) : (ℝ × E) →L[ℝ] (ℝ × E) →L[ℝ] ℝ))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem spaceTimePairing_apply (v w : ℝ × E) :
    spaceTimePairing v w = -(v.1 * w.1 + inner ℝ v.2 w.2) := by
  simp [spaceTimePairing]

/-- A half-wave `(t, x) ↦ ∫ 𝐞(σ ‖ξ‖ t + ⟪ξ, x⟫) a ξ dξ` is the Fourier integral on `ℝ × E` of the
image of `a ξ dξ` under the cone map `ξ ↦ (σ ‖ξ‖, ξ)`. -/
private theorem integral_fourierChar_smul_eq_fourierIntegral (σ : ℝ) (a : 𝓢(E, F))
    (p : ℝ × E) :
    ∫ ξ, 𝐞 (σ * ‖ξ‖ * p.1 + inner ℝ ξ p.2) • a ξ =
      VectorFourier.fourierIntegral 𝐞 (volume.map fun ξ : E ↦ (σ * ‖ξ‖, ξ))
        spaceTimePairing.toLinearMap₁₂ (fun v ↦ a v.2) p := by
  have hΦ : Continuous fun ξ : E ↦ (σ * ‖ξ‖, ξ) := by fun_prop
  have hc : Continuous fun v : ℝ × E ↦ 𝐞 (-spaceTimePairing v p) • a v.2 :=
    (continuous_fourierChar.comp
      ((spaceTimePairing (E := E)).continuous.clm_apply continuous_const).neg).smul
      (a.continuous.comp continuous_snd)
  rw [VectorFourier.fourierIntegral]
  simp only [ContinuousLinearMap.toLinearMap₁₂_apply_apply_apply]
  rw [integral_map hΦ.aemeasurable hc.aestronglyMeasurable]
  simp [spaceTimePairing_apply]

/-- A half-wave `(t, x) ↦ ∫ 𝐞(σ ‖ξ‖ t + ⟪ξ, x⟫) a ξ dξ` is smooth for `|σ| ≤ 1`, since the image of
`a ξ dξ` under the cone map `ξ ↦ (σ ‖ξ‖, ξ)` has moments of every order. -/
private theorem contDiff_halfWave {σ : ℝ} (hσ : |σ| ≤ 1) (a : 𝓢(E, F)) :
    ContDiff ℝ ∞ fun p : ℝ × E ↦ ∫ ξ, 𝐞 (σ * ‖ξ‖ * p.1 + inner ℝ ξ p.2) • a ξ := by
  have hΦ : Continuous fun ξ : E ↦ (σ * ‖ξ‖, ξ) := by fun_prop
  have hmom : ∀ n : ℕ, (n : ℕ∞) ≤ ⊤ → Integrable (fun v : ℝ × E ↦ ‖v‖ ^ n * ‖a v.2‖)
      (volume.map fun ξ : E ↦ (σ * ‖ξ‖, ξ)) := fun n _ ↦ by
    have hg : Continuous fun v : ℝ × E ↦ ‖v‖ ^ n * ‖a v.2‖ :=
      (continuous_norm.pow n).mul (a.continuous.comp continuous_snd).norm
    rw [integrable_map_measure hg.aestronglyMeasurable hΦ.aemeasurable]
    refine (a.integrable_pow_mul volume n).congr (ae_of_all _ fun ξ ↦ ?_)
    have : |σ| * ‖ξ‖ ≤ ‖ξ‖ := mul_le_of_le_one_left (norm_nonneg _) hσ
    simp [Prod.norm_def, abs_mul, max_eq_right this]
  rw [funext (integral_fourierChar_smul_eq_fourierIntegral σ a)]
  exact VectorFourier.contDiff_fourierIntegral (N := ⊤)
    (μ := volume.map fun ξ : E ↦ (σ * ‖ξ‖, ξ)) (f := fun v : ℝ × E ↦ a v.2) spaceTimePairing hmom

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `𝐞(⟪ξ, x⟫) cos(2π t ‖ξ‖) = (𝐞(‖ξ‖ t + ⟪ξ, x⟫) + 𝐞(-‖ξ‖ t + ⟪ξ, x⟫)) / 2`. -/
private theorem fourierChar_smul_waveCosSymbol_smul (t : ℝ) (ξ x : E) (y : F) :
    𝐞 (inner ℝ ξ x) • waveCosSymbol t ξ • y = (2⁻¹ : ℂ) •
      (𝐞 (1 * ‖ξ‖ * t + inner ℝ ξ x) • y + 𝐞 (-1 * ‖ξ‖ * t + inner ℝ ξ x) • y) := by
  rw [waveCosSymbol_eq_phaseSymbol, phaseSymbol_apply, phaseSymbol_apply]
  simp only [Circle.smul_def, smul_smul, ← add_smul, fourierChar_apply]
  rw [mul_left_comm, mul_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 4 <;> push_cast [sqrtNegLaplacianSymbol_apply] <;> ring

/-- The `cos` part of the wave solution is smooth in space and time. -/
private theorem contDiff_fourierInv_waveCosSymbol_smul (a : 𝓢(E, F)) :
    ContDiff ℝ ∞ fun p : ℝ × E ↦ 𝓕⁻ (fun ξ ↦ waveCosSymbol p.1 ξ • a ξ) p.2 := by
  have h : (fun p : ℝ × E ↦ 𝓕⁻ (fun ξ ↦ waveCosSymbol p.1 ξ • a ξ) p.2) = fun p ↦ (2⁻¹ : ℂ) •
      ((∫ ξ, 𝐞 (1 * ‖ξ‖ * p.1 + inner ℝ ξ p.2) • a ξ) +
        ∫ ξ, 𝐞 (-1 * ‖ξ‖ * p.1 + inner ℝ ξ p.2) • a ξ) := by
    funext p
    rw [Real.fourierInv_eq, ← integral_add (a.integrable.fourierChar_smul (by fun_prop))
      (a.integrable.fourierChar_smul (by fun_prop)), ← integral_smul]
    congr 1 with ξ
    exact fourierChar_smul_waveCosSymbol_smul p.1 ξ p.2 (a ξ)
  rw [h]
  exact ((contDiff_halfWave (by norm_num) a).add (contDiff_halfWave (by norm_num) a)).const_smul _

variable [CompleteSpace F]

/-- The `sin` part of the wave solution is the time primitive of its `cos` part. -/
private theorem fourierInv_waveSinSymbol_smul_eq_integral (a : 𝓢(E, F)) (t : ℝ) (x : E) :
    𝓕⁻ (fun ξ ↦ waveSinSymbol t ξ • a ξ) x =
      ∫ s in 0..t, 𝓕⁻ (fun ξ ↦ waveCosSymbol s ξ • a ξ) x := by
  have hd : ∀ s, HasDerivAt (fun r ↦ 𝓕⁻ (fun ξ ↦ waveSinSymbol r ξ • a ξ) x)
      (𝓕⁻ (fun ξ ↦ waveCosSymbol s ξ • a ξ) x) s := fun s ↦
    hasDerivAt_fourierInv_of_dominated_loc_of_deriv_le (G := fun r ξ ↦ waveSinSymbol r ξ • a ξ)
      (G' := fun r ξ ↦ waveCosSymbol r ξ • a ξ) Filter.univ_mem
      (Eventually.of_forall fun r ↦ (integrable_waveSinSymbol_smul a.integrable r).1)
      (integrable_waveSinSymbol_smul a.integrable s)
      (integrable_waveCosSymbol_smul a.integrable s).1
      (ae_of_all _ fun ξ r _ ↦ norm_waveCosSymbol_smul_le r ξ (a ξ))
      a.integrable.norm (ae_of_all _ fun ξ r _ ↦ (hasDerivAt_waveSinSymbol r ξ).smul_const _) x
  have hc : Continuous fun s ↦ 𝓕⁻ (fun ξ ↦ waveCosSymbol s ξ • a ξ) x :=
    (contDiff_fourierInv_waveCosSymbol_smul a).continuous.comp
      (continuous_id.prodMk continuous_const)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hd s)
    (hc.intervalIntegrable 0 t)]
  simp [Real.fourierInv_eq]

/-- **Smoothness.** The wave solution is `C^∞` jointly in time and space. -/
theorem contDiff_waveSolution (f g : 𝓢(E, F)) :
    ContDiff ℝ ∞ (Function.uncurry (waveSolution f g)) := by
  have hsin : ContDiff ℝ ∞ fun p : ℝ × E ↦
      ∫ s in 0..p.1, 𝓕⁻ (fun ξ ↦ waveCosSymbol s ξ • 𝓕 g ξ) p.2 :=
    (intervalIntegral.contDiff_parametric_primitive_of_contDiff
      (f := fun x s ↦ 𝓕⁻ (fun ξ ↦ waveCosSymbol s ξ • 𝓕 g ξ) x)
      ((contDiff_fourierInv_waveCosSymbol_smul (𝓕 g)).comp
        (contDiff_snd.prodMk contDiff_fst)) 0).comp
      (contDiff_snd.prodMk contDiff_fst)
  convert (contDiff_fourierInv_waveCosSymbol_smul (𝓕 f)).add hsin using 1
  funext ⟨t, x⟩
  rw [Function.uncurry_apply_pair, waveSolution_def,
    ← fourierInv_waveSinSymbol_smul_eq_integral]
  exact congrFun (Integrable.fourierInv_add (integrable_waveCosSymbol_smul (𝓕 f).integrable t)
    (integrable_waveSinSymbol_smul (𝓕 g).integrable t)) x

/-- The wave solution takes the initial value `f`. -/
@[simp]
theorem waveSolution_time_zero (f g : 𝓢(E, F)) : waveSolution f g 0 = ⇑f := by
  ext x
  simp only [waveSolution_def, waveCosSymbol_zero, waveSinSymbol_zero, one_smul, zero_smul,
    add_zero]
  rw [← SchwartzMap.fourierInv_coe, FourierTransform.fourierInv_fourier_eq]

/-- The wave solution takes the initial velocity `g`. -/
theorem deriv_waveSolution_time_zero (f g : 𝓢(E, F)) (x : E) :
    deriv (fun t ↦ waveSolution f g t x) 0 = g x := by
  rw [deriv_waveSolution, waveSolution_time_zero]

/-! ### Agreement with the `L²` propagators -/

section L2

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Agreement with the propagators.** At every time, the wave solution with Schwartz data
`f, g` is a representative of `cos(tD) f + D⁻¹ sin(tD) g` in `L²(E, F)`. -/
theorem waveSolution_ae_eq_waveCosPropagator_add_waveSinPropagator (f g : 𝓢(E, F)) (t : ℝ) :
    waveSolution f g t =ᵐ[volume]
      ⇑(waveCosPropagator F t (f.toLp 2) + waveSinPropagator F t (g.toLp 2) :
        Lp F 2 (volume : Measure E)) := by
  have hint := (integrable_waveCosSymbol_smul ((𝓕 f).integrable (μ := volume)) t).add
    (integrable_waveSinSymbol_smul ((𝓕 g).integrable (μ := volume)) t)
  have hfourier (u : 𝓢(E, F)) :
      ⇑(𝓕 (u.toLp 2) : Lp F 2 (volume : Measure E)) =ᵐ[volume] ⇑(𝓕 u : 𝓢(E, F)) := by
    rw [SchwartzMap.toLp_fourier_eq]
    exact (𝓕 u).coeFn_toLp 2 volume
  -- The distributional Fourier transform of the `L²` solution is the integrable symbol.
  have hF : 𝓕 ((waveCosPropagator F t (f.toLp 2) + waveSinPropagator F t (g.toLp 2) :
      Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) =
      ((hint.toL1 _ : Lp F 1 (volume : Measure E)) : 𝓢'(E, F)) := by
    rw [Lp.fourier_toTemperedDistribution_eq,
      Lp.toTemperedDistribution_eq_toTemperedDistribution_iff, FourierAdd.fourier_add]
    filter_upwards [Lp.coeFn_add (𝓕 (waveCosPropagator F t (f.toLp 2)))
      (𝓕 (waveSinPropagator F t (g.toLp 2))), coeFn_fourier_waveCosPropagator t (f.toLp 2),
      coeFn_fourier_waveSinPropagator t (g.toLp 2), hint.coeFn_toL1, hfourier f, hfourier g]
      with ξ h₁ h₂ h₃ h₄ h₅ h₆
    simp only [h₁, Pi.add_apply, h₂, h₃, h₄, h₅, h₆]
  have h : waveSolution f g t = 𝓕⁻ ⇑(hint.toL1 _) :=
    funext fun x ↦ (Real.fourierInv_congr_ae hint.coeFn_toL1 x).symm
  rw [h]
  exact (Lp.ae_eq_fourierInv_of_fourier_eq hF).symm

/-- **Strong solutions with Schwartz data are classical.** A strong solution of the free wave
equation on an order-connected set of times `s ∋ 0`, whose data at time `0` are Schwartz functions
`f` and `g`, agrees at every time of `s` almost everywhere with the classical solution
`TauCeti.waveSolution f g`. -/
theorem IsWaveSolutionOn.ae_eq_waveSolution {u u' u'' : ℝ → Lp F 2 (volume : Measure E)}
    {s : Set ℝ} [s.OrdConnected] (hu : IsWaveSolutionOn u u' u'' 0 s) (h₀ : 0 ∈ s)
    {f g : 𝓢(E, F)} (hf : u 0 = f.toLp 2) (hg : u' 0 = g.toLp 2) {t : ℝ} (ht : t ∈ s) :
    u t =ᵐ[volume] waveSolution f g t := by
  rw [hu.eq_waveCosPropagator_add_waveSinPropagator_add_integral h₀ ht intervalIntegrable_const,
    hf, hg, sub_zero]
  simpa using (waveSolution_ae_eq_waveCosPropagator_add_waveSinPropagator f g t).symm

end L2

end TauCeti
