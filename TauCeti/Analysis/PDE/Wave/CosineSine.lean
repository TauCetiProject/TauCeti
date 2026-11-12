/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.PDE.Wave.HalfWave
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Sinc
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The wave equation on `L²`: the cosine and sine propagators

On a finite-dimensional real inner product space `E`, let `D = √(-Δ)` be the Fourier multiplier
with symbol `TauCeti.sqrtNegLaplacianSymbol`, `ξ ↦ 2π ‖ξ‖`. The Cauchy problem for the wave
equation

`∂ₜ²u - Δu = G`, `u(0) = f`, `∂ₜu(0) = g`

is solved by

`u(t) = cos (tD) f + D⁻¹ sin (tD) g + ∫₀ᵗ D⁻¹ sin ((t - s)D) G(s) ds`.

This file constructs the **cosine propagator** `cos (tD)` (`TauCeti.waveCosine`) and the **sine
propagator** `D⁻¹ sin (tD)` (`TauCeti.waveSine`) as Fourier multipliers on `L²(E, F)`, with the
real symbols `cos (2π t ‖ξ‖)` and `sin (2π t ‖ξ‖) / (2π ‖ξ‖)`. The latter is written
`t sinc (2π t ‖ξ‖)`, which also covers the frequency `ξ = 0`, where it is `t`; so `D⁻¹ sin (tD)`
is a bounded operator of norm at most `|t|`, although `D⁻¹` is not. The sine propagator vanishes
at `t = 0` and its time derivative is the cosine propagator: in the language of second-order
abstract Cauchy problems the two form a cosine family and its sine family. The cosine propagator
is the average `(W₊(t) + W₋(t)) / 2` of the half-wave propagators
(`TauCeti.waveCosine_eq_halfWavePropagator`), so bounds for `W±` transfer to it.

The solution formula `TauCeti.waveSolution f g G` is defined for `f, g ∈ L²` and a forcing
`G : ℝ → L²`. It starts from `f` (`TauCeti.waveSolution_zero`), it is bounded by
`‖u(t)‖ ≤ ‖f‖ + |t| ‖g‖ + |∫₀ᵗ |t - s| ‖G(s)‖ ds|` for continuous `G`
(`TauCeti.norm_waveSolution_le`), and for continuous `G` it solves the wave equation weakly: for
every `φ ∈ L²` whose Laplacian `ψ = Δφ` lies in `L²`, in the sense that
`𝓕 ψ = -4π² ‖ξ‖² 𝓕 φ`, the scalar function `t ↦ ⟪φ, u(t)⟫` is twice differentiable, with

`d/dt ⟪φ, u(t)⟫ = ⟪ψ, D⁻¹ sin (tD) f⟫ + ⟪φ, cos (tD) g + ∫₀ᵗ cos ((t - s)D) G(s) ds⟫`,
`d²/dt² ⟪φ, u(t)⟫ = ⟪ψ, u(t)⟫ + ⟪φ, G(t)⟫`

(`TauCeti.hasDerivAt_inner_waveSolution`, `TauCeti.hasDerivAt_deriv_inner_waveSolution`). At
`t = 0` the first derivative is `⟪φ, g⟫`, so `u` takes the initial velocity `g` weakly
(`TauCeti.hasDerivAt_inner_waveSolution_zero`). Every Schwartz function `φ` is admissible, with
`ψ = Δφ` (`SchwartzMap.coeFn_fourier_toLp_laplacian`), so `u` solves the wave equation in the
sense of distributions in space (`TauCeti.hasDerivAt_deriv_inner_toLp_waveSolution`).

The time derivatives come from differentiating the symbols under the multiplier
(`MeasureTheory.Lp.hasDerivAt_fourierMultiplierCLM_toLp_apply`). The sine propagator is
differentiable in time on all of `L²`, with derivative `cos (tD)`, because its symbol is
`1`-Lipschitz in `t`. The cosine propagator is differentiable only on the domain of `D`; on
`φ` with `Δφ = ψ ∈ L²` it is `φ + K_t ψ`, where `K_t` has the bounded symbol
`(1 - cos (2π t ‖ξ‖)) / (4π² ‖ξ‖²)`, and its derivative is `D⁻¹ sin (tD) ψ`. The Duhamel term is
differentiated through the subtraction formula
`D⁻¹ sin ((t - s)D) = D⁻¹ sin (tD) cos (sD) - cos (tD) D⁻¹ sin (sD)` (`TauCeti.waveSine_sub`),
which splits it into bounded operators of `t` applied to integrals from `0` to `t`.

## Main declarations

* `TauCeti.waveCosine`, `TauCeti.waveSine`: the propagators `cos (tD)` and `D⁻¹ sin (tD)`, with
  their Fourier-side description `TauCeti.coeFn_fourier_waveCosine`,
  `TauCeti.coeFn_fourier_waveSine`, the bounds `TauCeti.norm_waveCosine_le`,
  `TauCeti.norm_waveSine_le` and `TauCeti.norm_waveSine_sub_le`, and self-adjointness.
* `TauCeti.waveCosine_eq_halfWavePropagator`: `cos (tD) = (W₊(t) + W₋(t)) / 2`.
* `TauCeti.waveSine_sub`, `TauCeti.waveCosine_sub_apply`: the subtraction formulas.
* `TauCeti.hasDerivAt_waveSine_apply`: `∂ₜ D⁻¹ sin (tD) f = cos (tD) f`.
* `TauCeti.hasDerivAt_waveCosine_apply`: `∂ₜ cos (tD) φ = D⁻¹ sin (tD) Δφ`.
* `TauCeti.waveSolution`: the solution formula, and `TauCeti.hasDerivAt_inner_waveSolution`,
  `TauCeti.hasDerivAt_deriv_inner_waveSolution`: the weak wave equation.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Chapter 2 (the Fourier solution of the wave equation and
  Duhamel's formula).
* W. Arendt, C. J. K. Batty, M. Hieber and F. Neubrander, *Vector-valued Laplace Transforms and
  Cauchy Problems*, 2nd ed., Birkhäuser, 2011, Section 3.14 (cosine and sine families).
-/

public section

noncomputable section

open scoped FourierTransform ComplexInnerProductSpace Topology ENNReal SchwartzMap Laplacian
open MeasureTheory Filter Real FourierTransform

namespace TauCeti

/-- The subtraction formula for `t ↦ t sinc (a t)`, which is `sin (a t) / a` for `a ≠ 0`. -/
private theorem sub_mul_sinc_mul_sub (a s t : ℝ) :
    (t - s) * sinc (a * (t - s)) =
      t * sinc (a * t) * cos (a * s) - cos (a * t) * (s * sinc (a * s)) := by
  rcases eq_or_ne a 0 with rfl | h
  · simp
  · rw [mul_sinc_mul_of_ne_zero h, mul_sinc_mul_of_ne_zero h, mul_sinc_mul_of_ne_zero h, mul_sub,
      sin_sub]
    ring

/-- The subtraction formula for `cos (a t)`, in terms of `t ↦ t sinc (a t)`. -/
private theorem cos_mul_sub (a s t : ℝ) :
    cos (a * (t - s)) =
      cos (a * s) * cos (a * t) + s * sinc (a * s) * (t * sinc (a * t)) * a ^ 2 := by
  rcases eq_or_ne a 0 with rfl | h
  · simp
  · rw [mul_sinc_mul_of_ne_zero h, mul_sinc_mul_of_ne_zero h, mul_sub, cos_sub]
    field_simp

section Symbol

variable {E : Type*} [NormedAddCommGroup E]

/-- The symbol `ξ ↦ cos (2π t ‖ξ‖)` of the cosine propagator `cos (tD)`. -/
def waveCosineSymbol (t : ℝ) (ξ : E) : ℂ :=
  (cos (sqrtNegLaplacianSymbol ξ * t) : ℝ)

/-- The symbol `ξ ↦ sin (2π t ‖ξ‖) / (2π ‖ξ‖)` of the sine propagator `D⁻¹ sin (tD)`, written
`t sinc (2π t ‖ξ‖)` so that it is defined, with the value `t`, at `ξ = 0`. -/
def waveSineSymbol (t : ℝ) (ξ : E) : ℂ :=
  (t * sinc (sqrtNegLaplacianSymbol ξ * t) : ℝ)

theorem waveCosineSymbol_apply (t : ℝ) (ξ : E) :
    waveCosineSymbol t ξ = (cos (sqrtNegLaplacianSymbol ξ * t) : ℝ) :=
  (rfl)

theorem waveSineSymbol_apply (t : ℝ) (ξ : E) :
    waveSineSymbol t ξ = (t * sinc (sqrtNegLaplacianSymbol ξ * t) : ℝ) :=
  (rfl)

@[simp]
theorem waveCosineSymbol_zero (ξ : E) : waveCosineSymbol 0 ξ = 1 := by
  simp [waveCosineSymbol_apply]

@[simp]
theorem waveSineSymbol_zero (ξ : E) : waveSineSymbol 0 ξ = 0 := by
  simp [waveSineSymbol_apply]

theorem star_waveCosineSymbol (t : ℝ) (ξ : E) :
    star (waveCosineSymbol t ξ) = waveCosineSymbol t ξ :=
  Complex.conj_ofReal _

theorem star_waveSineSymbol (t : ℝ) (ξ : E) : star (waveSineSymbol t ξ) = waveSineSymbol t ξ :=
  Complex.conj_ofReal _

theorem norm_waveCosineSymbol_le (t : ℝ) (ξ : E) : ‖waveCosineSymbol t ξ‖ ≤ 1 := by
  rw [waveCosineSymbol_apply, Complex.norm_real, Real.norm_eq_abs]
  exact abs_cos_le_one _

theorem norm_waveSineSymbol_le (t : ℝ) (ξ : E) : ‖waveSineSymbol t ξ‖ ≤ |t| := by
  rw [waveSineSymbol_apply, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg t) (abs_sinc_le_one _)

/-- The time derivative of the sine symbol is the cosine symbol, at every frequency. -/
theorem hasDerivAt_waveSineSymbol (t : ℝ) (ξ : E) :
    HasDerivAt (fun s ↦ waveSineSymbol s ξ) (waveCosineSymbol t ξ) t :=
  (hasDerivAt_mul_sinc_mul (sqrtNegLaplacianSymbol ξ) t).ofReal_comp

/-- The sine symbol is `1`-Lipschitz in time, at every frequency. -/
theorem norm_waveSineSymbol_sub_le (s t : ℝ) (ξ : E) :
    ‖waveSineSymbol s ξ - waveSineSymbol t ξ‖ ≤ |s - t| := by
  have h := (convex_univ (𝕜 := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r _ ↦ (hasDerivAt_waveSineSymbol r ξ).hasDerivWithinAt)
    (fun r _ ↦ norm_waveCosineSymbol_le r ξ) (Set.mem_univ t) (Set.mem_univ s)
  rwa [one_mul, Real.norm_eq_abs] at h

/-- The subtraction formula
`sin (a (t - s)) / a = sin (a t) cos (a s) / a - cos (a t) sin (a s) / a` for the sine symbol,
`a = 2π ‖ξ‖`. -/
theorem waveSineSymbol_sub (s t : ℝ) (ξ : E) :
    waveSineSymbol (t - s) ξ =
      waveSineSymbol t ξ * waveCosineSymbol s ξ - waveCosineSymbol t ξ * waveSineSymbol s ξ := by
  simp only [waveSineSymbol_apply, waveCosineSymbol_apply,
    sub_mul_sinc_mul_sub (sqrtNegLaplacianSymbol ξ) s t]
  push_cast
  ring

/-- The subtraction formula `cos (a (t - s)) = cos (a s) cos (a t) + a² (sin (a s) / a)
(sin (a t) / a)`, with `-a²` the symbol of the Laplacian. -/
theorem waveCosineSymbol_sub (s t : ℝ) (ξ : E) :
    waveCosineSymbol (t - s) ξ = waveCosineSymbol s ξ * waveCosineSymbol t ξ -
      waveSineSymbol s ξ * waveSineSymbol t ξ * (laplacianSymbol ξ : ℂ) := by
  have hl : laplacianSymbol ξ = -sqrtNegLaplacianSymbol ξ ^ 2 := by
    rw [sq_sqrtNegLaplacianSymbol, neg_neg]
  simp only [waveSineSymbol_apply, waveCosineSymbol_apply, hl,
    cos_mul_sub (sqrtNegLaplacianSymbol ξ) s t]
  push_cast
  ring

theorem continuous_waveCosineSymbol (t : ℝ) : Continuous (waveCosineSymbol (E := E) t) := by
  unfold waveCosineSymbol
  fun_prop

theorem continuous_waveSineSymbol (t : ℝ) : Continuous (waveSineSymbol (E := E) t) := by
  unfold waveSineSymbol
  have := continuous_sinc
  fun_prop

end Symbol

/-- The half-angle identity `(t² / 2) sinc² (a t / 2) a² = 1 - cos (a t)`. -/
private theorem mul_sinc_sq_mul_sq (a t : ℝ) :
    t ^ 2 / 2 * sinc (a * t / 2) ^ 2 * a ^ 2 = 1 - cos (a * t) := by
  have h₁ := cos_two_mul (a * t / 2)
  rw [show 2 * (a * t / 2) = a * t by ring] at h₁
  linear_combination h₁ + 2 * sin_sq_add_cos_sq (a * t / 2) +
    2 * (a * t / 2 * sinc (a * t / 2) + sin (a * t / 2)) * mul_sinc (a * t / 2)

/-- The auxiliary symbol `(1 - cos (2π t ‖ξ‖)) / (4π² ‖ξ‖²)`, written `(t² / 2) sinc² (π t ‖ξ‖)`
so that it is defined, with the value `t² / 2`, at `ξ = 0`. Its time derivative is the sine
symbol, and `cos (tD) = 1 + K_t Δ`. -/
private def waveAuxSymbol {E : Type*} [NormedAddCommGroup E] (t : ℝ) (ξ : E) : ℂ :=
  (t ^ 2 / 2 * sinc (sqrtNegLaplacianSymbol ξ * t / 2) ^ 2 : ℝ)

section AuxSymbol

variable {E : Type*} [NormedAddCommGroup E]

/-- `cos (a t) = 1 + K_t(a) · (-a²)`. -/
private theorem waveCosineSymbol_eq_one_add_waveAuxSymbol_mul (t : ℝ) (ξ : E) :
    waveCosineSymbol t ξ = 1 + waveAuxSymbol t ξ * (laplacianSymbol ξ : ℂ) := by
  have hl : laplacianSymbol ξ = -sqrtNegLaplacianSymbol ξ ^ 2 := by
    rw [sq_sqrtNegLaplacianSymbol, neg_neg]
  have key := mul_sinc_sq_mul_sq (sqrtNegLaplacianSymbol ξ) t
  rw [waveAuxSymbol, waveCosineSymbol_apply, hl,
    show cos (sqrtNegLaplacianSymbol ξ * t) = 1 + t ^ 2 / 2 *
      sinc (sqrtNegLaplacianSymbol ξ * t / 2) ^ 2 * -sqrtNegLaplacianSymbol ξ ^ 2 by linarith]
  push_cast
  ring

/-- The time derivative of the auxiliary symbol is the sine symbol. -/
private theorem hasDerivAt_waveAuxSymbol (t : ℝ) (ξ : E) :
    HasDerivAt (fun s ↦ waveAuxSymbol s ξ) (waveSineSymbol t ξ) t := by
  simp only [waveAuxSymbol, waveSineSymbol_apply]
  refine HasDerivAt.ofReal_comp ?_
  generalize sqrtNegLaplacianSymbol ξ = a
  rcases eq_or_ne a 0 with rfl | h
  · simpa using (hasDerivAt_pow 2 t).div_const 2
  · have hfun : (fun s ↦ s ^ 2 / 2 * sinc (a * s / 2) ^ 2) = fun s ↦ (1 - cos (a * s)) / a ^ 2 :=
      funext fun s ↦ eq_div_of_mul_eq (pow_ne_zero 2 h) (mul_sinc_sq_mul_sq a s)
    rw [hfun, mul_sinc_mul_of_ne_zero h]
    convert ((((hasDerivAt_id' t).const_mul a).cos).const_sub 1).div_const (a ^ 2) using 1
    field_simp

/-- The auxiliary symbol is Lipschitz in time near `t`, with constant `|t| + 1`. -/
private theorem norm_waveAuxSymbol_sub_le {s t : ℝ} (hs : s ∈ Metric.ball t 1) (ξ : E) :
    ‖waveAuxSymbol s ξ - waveAuxSymbol t ξ‖ ≤ (|t| + 1) * |s - t| := by
  have h := (convex_ball t 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r _ ↦ (hasDerivAt_waveAuxSymbol r ξ).hasDerivWithinAt) (C := |t| + 1)
    (fun r hr ↦ (norm_waveSineSymbol_le r ξ).trans ?_) (Metric.mem_ball_self one_pos) hs
  · rwa [Real.norm_eq_abs] at h
  · have := abs_sub_abs_le_abs_sub r t
    rw [Metric.mem_ball, Real.dist_eq] at hr
    linarith

private theorem continuous_waveAuxSymbol (t : ℝ) : Continuous (waveAuxSymbol (E := E) t) := by
  unfold waveAuxSymbol
  have := continuous_sinc
  fun_prop

end AuxSymbol

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem memLp_waveCosineSymbol (t : ℝ) : MemLp (waveCosineSymbol (E := E) t) ∞ volume :=
  memLp_top_of_bound (continuous_waveCosineSymbol t).aestronglyMeasurable 1
    (Eventually.of_forall (norm_waveCosineSymbol_le t))

theorem memLp_waveSineSymbol (t : ℝ) : MemLp (waveSineSymbol (E := E) t) ∞ volume :=
  memLp_top_of_bound (continuous_waveSineSymbol t).aestronglyMeasurable |t|
    (Eventually.of_forall (norm_waveSineSymbol_le t))

private theorem memLp_waveAuxSymbol (t : ℝ) : MemLp (waveAuxSymbol (E := E) t) ∞ volume := by
  refine memLp_top_of_bound (continuous_waveAuxSymbol t).aestronglyMeasurable (t ^ 2 / 2)
    (Eventually.of_forall fun ξ ↦ ?_)
  rw [waveAuxSymbol, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_div, abs_two,
    sq_abs, abs_pow, sq_abs]
  exact mul_le_of_le_one_right (by positivity)
    (by simpa [sq_abs] using pow_le_one₀ (abs_nonneg _) (abs_sinc_le_one _) (n := 2))

variable (F) in
/-- The **cosine propagator** `cos (tD)` on `L²(E, F)`, `D = √(-Δ)`: the Fourier multiplier with
symbol `cos (2π t ‖ξ‖)`. -/
def waveCosine (t : ℝ) : Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  Lp.fourierMultiplierCLM F ((memLp_waveCosineSymbol t).toLp _)

variable (F) in
/-- The **sine propagator** `D⁻¹ sin (tD)` on `L²(E, F)`, `D = √(-Δ)`: the Fourier multiplier
with symbol `sin (2π t ‖ξ‖) / (2π ‖ξ‖)`, which is `t` at `ξ = 0`. -/
def waveSine (t : ℝ) : Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  Lp.fourierMultiplierCLM F ((memLp_waveSineSymbol t).toLp _)

variable (F) in
/-- The bounded operator `K_t` with symbol `(1 - cos (2π t ‖ξ‖)) / (4π² ‖ξ‖²)`, so that
`cos (tD) = 1 + K_t Δ` on the domain of the Laplacian. -/
private def waveAux (t : ℝ) : Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  Lp.fourierMultiplierCLM F ((memLp_waveAuxSymbol t).toLp _)

theorem waveCosine_def (t : ℝ) :
    waveCosine F t = Lp.fourierMultiplierCLM (E := E) F ((memLp_waveCosineSymbol t).toLp _) :=
  (rfl)

theorem waveSine_def (t : ℝ) :
    waveSine F t = Lp.fourierMultiplierCLM (E := E) F ((memLp_waveSineSymbol t).toLp _) :=
  (rfl)

/-- On the Fourier side, `cos (tD)` is pointwise multiplication by `cos (2π t ‖ξ‖)`, almost
everywhere. -/
theorem coeFn_fourier_waveCosine (t : ℝ) (f : Lp F 2 (volume : Measure E)) :
    𝓕 (waveCosine F t f) =ᵐ[volume] fun ξ ↦ waveCosineSymbol t ξ • 𝓕 f ξ :=
  Lp.coeFn_fourier_fourierMultiplierCLM_toLp f (memLp_waveCosineSymbol t)

/-- On the Fourier side, `D⁻¹ sin (tD)` is pointwise multiplication by
`sin (2π t ‖ξ‖) / (2π ‖ξ‖)`, almost everywhere. -/
theorem coeFn_fourier_waveSine (t : ℝ) (f : Lp F 2 (volume : Measure E)) :
    𝓕 (waveSine F t f) =ᵐ[volume] fun ξ ↦ waveSineSymbol t ξ • 𝓕 f ξ :=
  Lp.coeFn_fourier_fourierMultiplierCLM_toLp f (memLp_waveSineSymbol t)

private theorem coeFn_fourier_waveAux (t : ℝ) (f : Lp F 2 (volume : Measure E)) :
    𝓕 (waveAux F t f) =ᵐ[volume] fun ξ ↦ waveAuxSymbol t ξ • 𝓕 f ξ :=
  Lp.coeFn_fourier_fourierMultiplierCLM_toLp f (memLp_waveAuxSymbol t)

private theorem fourier_sub' (x y : Lp F 2 (volume : Measure E)) : 𝓕 (x - y) = 𝓕 x - 𝓕 y := by
  rw [sub_eq_add_neg, FourierTransform.fourier_add, FourierTransform.fourier_neg,
    ← sub_eq_add_neg]

/-- Two elements of `L²` with almost everywhere equal Fourier transforms are equal. -/
private theorem eq_of_fourier_ae_eq {x y : Lp F 2 (volume : Measure E)}
    (h : ((𝓕 x : Lp F 2 (volume : Measure E)) : E → F) =ᵐ[volume]
      (𝓕 y : Lp F 2 (volume : Measure E))) : x = y := by
  simpa using congrArg 𝓕⁻ (Lp.ext h)

@[simp]
theorem waveCosine_zero :
    waveCosine F 0 = ContinuousLinearMap.id ℂ (Lp F 2 (volume : Measure E)) := by
  rw [waveCosine_def, Lp.fourierMultiplierCLM_of_ae_eq_const (c := 1) ?_, one_smul]
  filter_upwards [(memLp_waveCosineSymbol 0).coeFn_toLp] with ξ h
  simp [h]

@[simp]
theorem waveSine_zero : waveSine F 0 = (0 : Lp F 2 (volume : Measure E) →L[ℂ] _) := by
  rw [waveSine_def, Lp.fourierMultiplierCLM_of_ae_eq_const (c := 0) ?_]
  · exact zero_smul ℂ (ContinuousLinearMap.id ℂ (Lp F 2 (volume : Measure E)))
  · filter_upwards [(memLp_waveSineSymbol 0).coeFn_toLp] with ξ h
    simp [h]

/-- `cos (tD)` has operator norm at most one. -/
theorem norm_waveCosine_le (t : ℝ) : ‖waveCosine (E := E) F t‖ ≤ 1 := by
  refine (Lp.norm_fourierMultiplierCLM_le _).trans (Lp.norm_top_le_of_ae_bound zero_le_one ?_)
  filter_upwards [(memLp_waveCosineSymbol t).coeFn_toLp] with ξ h
  rw [h]
  exact norm_waveCosineSymbol_le t ξ

/-- `D⁻¹ sin (tD)` has operator norm at most `|t|`. -/
theorem norm_waveSine_le (t : ℝ) : ‖waveSine (E := E) F t‖ ≤ |t| := by
  refine (Lp.norm_fourierMultiplierCLM_le _).trans (Lp.norm_top_le_of_ae_bound (abs_nonneg t) ?_)
  filter_upwards [(memLp_waveSineSymbol t).coeFn_toLp] with ξ h
  rw [h]
  exact norm_waveSineSymbol_le t ξ

/-- `t ↦ D⁻¹ sin (tD)` is `1`-Lipschitz in operator norm. -/
theorem norm_waveSine_sub_le (s t : ℝ) : ‖waveSine (E := E) F s - waveSine F t‖ ≤ |s - t| := by
  rw [waveSine_def, waveSine_def, ← Lp.fourierMultiplierCLM_sub]
  refine (Lp.norm_fourierMultiplierCLM_le _).trans (Lp.norm_top_le_of_ae_bound (abs_nonneg _) ?_)
  filter_upwards [Lp.coeFn_sub ((memLp_waveSineSymbol s).toLp (waveSineSymbol (E := E) s))
      ((memLp_waveSineSymbol t).toLp _), (memLp_waveSineSymbol s).coeFn_toLp,
    (memLp_waveSineSymbol t).coeFn_toLp] with ξ h₁ h₂ h₃
  rw [h₁, Pi.sub_apply, h₂, h₃]
  exact norm_waveSineSymbol_sub_le s t ξ

theorem lipschitzWith_waveSine : LipschitzWith 1 (waveSine (E := E) F) :=
  LipschitzWith.of_dist_le_mul fun s t ↦ by
    rw [dist_eq_norm, NNReal.coe_one, one_mul, Real.dist_eq]
    exact norm_waveSine_sub_le s t

/-- **The cosine propagator is the average of the half-wave propagators**:
`cos (tD) = (W₊(t) + W₋(t)) / 2`, where `W₋(t) = W₊(-t)`. -/
theorem waveCosine_eq_halfWavePropagator (t : ℝ) :
    waveCosine (E := E) F t =
      (2 : ℂ)⁻¹ • (halfWavePropagator F t + halfWavePropagator F (-t)) := by
  ext1 f
  refine eq_of_fourier_ae_eq ?_
  rw [smul_apply, add_apply, fourier_smul, FourierTransform.fourier_add]
  filter_upwards [coeFn_fourier_waveCosine t f, coeFn_fourier_halfWavePropagator t f,
    coeFn_fourier_halfWavePropagator (-t) f,
    Lp.coeFn_smul (2 : ℂ)⁻¹ (𝓕 (halfWavePropagator F t f) + 𝓕 (halfWavePropagator F (-t) f)),
    Lp.coeFn_add (𝓕 (halfWavePropagator F t f)) (𝓕 (halfWavePropagator F (-t) f))]
    with ξ h₁ h₂ h₃ h₄ h₅
  rw [h₁, h₄, Pi.smul_apply, h₅, Pi.add_apply, h₂, h₃, ← add_smul, smul_smul,
    waveCosineSymbol_apply, sqrtNegLaplacianSymbol_apply, Complex.ofReal_cos, Complex.cos]
  congr 1
  push_cast
  ring_nf

/-- `cos (tD)` is self-adjoint. -/
theorem adjoint_waveCosine (t : ℝ) :
    ContinuousLinearMap.adjoint (waveCosine (E := E) F t) = waveCosine F t := by
  rw [waveCosine_def, Lp.adjoint_fourierMultiplierCLM]
  congr 1
  apply Lp.ext
  filter_upwards [Lp.coeFn_star ((memLp_waveCosineSymbol t).toLp _),
    (memLp_waveCosineSymbol t).coeFn_toLp] with ξ h₁ h₂
  rw [h₁, Pi.star_apply, h₂, star_waveCosineSymbol]

/-- `D⁻¹ sin (tD)` is self-adjoint. -/
theorem adjoint_waveSine (t : ℝ) :
    ContinuousLinearMap.adjoint (waveSine (E := E) F t) = waveSine F t := by
  rw [waveSine_def, Lp.adjoint_fourierMultiplierCLM]
  congr 1
  apply Lp.ext
  filter_upwards [Lp.coeFn_star ((memLp_waveSineSymbol t).toLp _),
    (memLp_waveSineSymbol t).coeFn_toLp] with ξ h₁ h₂
  rw [h₁, Pi.star_apply, h₂, star_waveSineSymbol]

/-- `cos (tD)` moves across the `L²` inner product. -/
theorem inner_waveCosine_apply (t : ℝ) (f g : Lp F 2 (volume : Measure E)) :
    ⟪waveCosine F t f, g⟫ = ⟪f, waveCosine F t g⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_waveCosine]

/-- `D⁻¹ sin (tD)` moves across the `L²` inner product. -/
theorem inner_waveSine_apply (t : ℝ) (f g : Lp F 2 (volume : Measure E)) :
    ⟪waveSine F t f, g⟫ = ⟪f, waveSine F t g⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, adjoint_waveSine]

/-- **The subtraction formula**
`D⁻¹ sin ((t - s)D) = D⁻¹ sin (tD) cos (sD) - cos (tD) D⁻¹ sin (sD)`. -/
theorem waveSine_sub (s t : ℝ) :
    waveSine (E := E) F (t - s) =
      waveSine F t ∘L waveCosine F s - waveCosine F t ∘L waveSine F s := by
  ext1 f
  refine eq_of_fourier_ae_eq ?_
  simp only [sub_apply, ContinuousLinearMap.comp_apply, fourier_sub']
  filter_upwards [coeFn_fourier_waveSine (t - s) f, coeFn_fourier_waveSine t (waveCosine F s f),
    coeFn_fourier_waveCosine s f, coeFn_fourier_waveCosine t (waveSine F s f),
    coeFn_fourier_waveSine s f, Lp.coeFn_sub (𝓕 (waveSine F t (waveCosine F s f)))
      (𝓕 (waveCosine F t (waveSine F s f)))] with ξ h₁ h₂ h₃ h₄ h₅ h₆
  rw [h₁, h₆, Pi.sub_apply, h₂, h₃, h₄, h₅, waveSineSymbol_sub]
  module

/-- `cos (tD)` and `D⁻¹ sin (sD)` commute. -/
theorem waveCosine_comp_waveSine (s t : ℝ) :
    waveCosine (E := E) F t ∘L waveSine F s = waveSine F s ∘L waveCosine F t := by
  ext1 f
  refine eq_of_fourier_ae_eq ?_
  simp only [ContinuousLinearMap.comp_apply]
  filter_upwards [coeFn_fourier_waveCosine t (waveSine F s f), coeFn_fourier_waveSine s f,
    coeFn_fourier_waveSine s (waveCosine F t f), coeFn_fourier_waveCosine t f]
    with ξ h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, smul_comm]

/-- `D⁻¹ sin (sD) cos (tD) = cos (tD) D⁻¹ sin (sD)`. -/
theorem waveSine_apply_waveCosine_apply (s t : ℝ) (x : Lp F 2 (volume : Measure E)) :
    waveSine F s (waveCosine F t x) = waveCosine F t (waveSine F s x) := by
  rw [← ContinuousLinearMap.comp_apply, ← waveCosine_comp_waveSine,
    ContinuousLinearMap.comp_apply]

/-- **The subtraction formula for the cosine propagator**, on the domain of the Laplacian: if
`Δφ = ψ` in `L²`, that is `𝓕 ψ = -4π² ‖ξ‖² 𝓕 φ`, then
`cos ((t - s)D) φ = cos (sD) cos (tD) φ - D⁻¹ sin (sD) D⁻¹ sin (tD) ψ`. -/
theorem waveCosine_sub_apply {φ ψ : Lp F 2 (volume : Measure E)}
    (hψ : 𝓕 ψ =ᵐ[volume] fun ξ ↦ (laplacianSymbol ξ : ℂ) • 𝓕 φ ξ) (s t : ℝ) :
    waveCosine F (t - s) φ =
      waveCosine F s (waveCosine F t φ) - waveSine F s (waveSine F t ψ) := by
  refine eq_of_fourier_ae_eq ?_
  rw [fourier_sub']
  filter_upwards [coeFn_fourier_waveCosine (t - s) φ, coeFn_fourier_waveCosine s
      (waveCosine F t φ), coeFn_fourier_waveCosine t φ, coeFn_fourier_waveSine s
      (waveSine F t ψ), coeFn_fourier_waveSine t ψ, hψ, Lp.coeFn_sub
      (𝓕 (waveCosine F s (waveCosine F t φ))) (𝓕 (waveSine F s (waveSine F t ψ)))]
    with ξ h₁ h₂ h₃ h₄ h₅ h₆ h₇
  rw [h₁, h₇, Pi.sub_apply, h₂, h₃, h₄, h₅, h₆, waveCosineSymbol_sub]
  module

/-- On the domain of the Laplacian, `cos (tD) φ = φ + K_t Δφ`. -/
private theorem waveCosine_apply_eq_add_waveAux {φ ψ : Lp F 2 (volume : Measure E)}
    (hψ : 𝓕 ψ =ᵐ[volume] fun ξ ↦ (laplacianSymbol ξ : ℂ) • 𝓕 φ ξ) (t : ℝ) :
    waveCosine F t φ = φ + waveAux F t ψ := by
  refine eq_of_fourier_ae_eq ?_
  rw [FourierTransform.fourier_add]
  filter_upwards [coeFn_fourier_waveCosine t φ, coeFn_fourier_waveAux t ψ, hψ,
    Lp.coeFn_add (𝓕 φ) (𝓕 (waveAux F t ψ))] with ξ h₁ h₂ h₃ h₄
  rw [h₁, h₄, Pi.add_apply, h₂, h₃, smul_smul, waveCosineSymbol_eq_one_add_waveAuxSymbol_mul,
    add_smul, one_smul]

/-- **The time derivative of the sine propagator** is the cosine propagator:
`∂ₜ (D⁻¹ sin (tD) f) = cos (tD) f` in `L²`, for every `f ∈ L²`. -/
theorem hasDerivAt_waveSine_apply (f : Lp F 2 (volume : Measure E)) (t : ℝ) :
    HasDerivAt (fun s ↦ waveSine F s f) (waveCosine F t f) t :=
  Lp.hasDerivAt_fourierMultiplierCLM_toLp_apply memLp_waveSineSymbol (memLp_waveCosineSymbol t)
    (C := 1) (Eventually.of_forall fun s ξ ↦ by
      simpa using norm_waveSineSymbol_sub_le s t ξ)
    (Eventually.of_forall fun ξ ↦ hasDerivAt_waveSineSymbol t ξ) f

/-- **The time derivative of the cosine propagator**, on the domain of the Laplacian: if
`Δφ = ψ` in `L²`, then `∂ₜ (cos (tD) φ) = D⁻¹ sin (tD) ψ`. -/
theorem hasDerivAt_waveCosine_apply {φ ψ : Lp F 2 (volume : Measure E)}
    (hψ : 𝓕 ψ =ᵐ[volume] fun ξ ↦ (laplacianSymbol ξ : ℂ) • 𝓕 φ ξ) (t : ℝ) :
    HasDerivAt (fun s ↦ waveCosine F s φ) (waveSine F t ψ) t := by
  simp_rw [waveCosine_apply_eq_add_waveAux hψ]
  refine HasDerivAt.const_add φ ?_
  exact Lp.hasDerivAt_fourierMultiplierCLM_toLp_apply memLp_waveAuxSymbol
    (memLp_waveSineSymbol t) (C := |t| + 1)
    (eventually_of_mem (Metric.ball_mem_nhds t one_pos) fun s hs ξ ↦
      norm_waveAuxSymbol_sub_le hs ξ)
    (Eventually.of_forall fun ξ ↦ hasDerivAt_waveAuxSymbol t ξ) ψ

/-- `t ↦ D⁻¹ sin (tD)` is continuous in operator norm. -/
theorem continuous_waveSine : Continuous (waveSine (E := E) F) :=
  lipschitzWith_waveSine.continuous

/-- **Strong continuity**: `t ↦ cos (tD) f` is continuous for every `f ∈ L²`. -/
theorem continuous_waveCosine_apply (f : Lp F 2 (volume : Measure E)) :
    Continuous fun t ↦ waveCosine F t f := by
  simp_rw [waveCosine_eq_halfWavePropagator, smul_apply, add_apply]
  exact ((continuous_phasePropagator_apply _ f).add
    ((continuous_phasePropagator_apply _ f).comp continuous_neg)).const_smul (2⁻¹ : ℂ)

/-- For a continuous `G : ℝ → L²`, the map `t ↦ cos (tD) G(t)` is continuous: the operators are
strongly continuous and uniformly bounded. -/
theorem _root_.Continuous.waveCosine_apply {G : ℝ → Lp F 2 (volume : Measure E)}
    (hG : Continuous G) :
    Continuous fun t ↦ waveCosine F t (G t) := by
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  have h₁ : Tendsto (fun s ↦ waveCosine F s (G s) - waveCosine F s (G t)) (𝓝 t) (𝓝 0) := by
    refine squeeze_zero_norm (fun s ↦ ?_) (by simpa using ((hG.tendsto t).sub_const (G t)).norm)
    rw [← map_sub]
    exact ((waveCosine F s).le_opNorm _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_waveCosine_le s))
  rw [ContinuousAt]
  simpa using h₁.add ((continuous_waveCosine_apply (G t)).tendsto t)

/-! ### The solution formula -/

variable (F) in
/-- **The solution of the Cauchy problem for the wave equation** `∂ₜ²u - Δu = G`, `u(0) = f`,
`∂ₜu(0) = g`, given by
`u(t) = cos (tD) f + D⁻¹ sin (tD) g + ∫₀ᵗ D⁻¹ sin ((t - s)D) G(s) ds`. -/
def waveSolution (f g : Lp F 2 (volume : Measure E)) (G : ℝ → Lp F 2 (volume : Measure E))
    (t : ℝ) : Lp F 2 (volume : Measure E) :=
  waveCosine F t f + waveSine F t g + ∫ s in (0 : ℝ)..t, waveSine F (t - s) (G s)

theorem waveSolution_def (f g : Lp F 2 (volume : Measure E))
    (G : ℝ → Lp F 2 (volume : Measure E)) (t : ℝ) :
    waveSolution F f g G t =
      waveCosine F t f + waveSine F t g + ∫ s in (0 : ℝ)..t, waveSine F (t - s) (G s) :=
  (rfl)

/-- The solution starts from the initial displacement. -/
@[simp]
theorem waveSolution_zero (f g : Lp F 2 (volume : Measure E))
    (G : ℝ → Lp F 2 (volume : Measure E)) : waveSolution F f g G 0 = f := by
  simp [waveSolution_def]

/-- The **a priori bound** `‖u(t)‖ ≤ ‖f‖ + |t| ‖g‖ + |∫₀ᵗ |t - s| ‖G(s)‖ ds|`. -/
theorem norm_waveSolution_le (f g : Lp F 2 (volume : Measure E))
    {G : ℝ → Lp F 2 (volume : Measure E)} (hG : Continuous G) (t : ℝ) :
    ‖waveSolution F f g G t‖ ≤
      ‖f‖ + |t| * ‖g‖ + |∫ s in (0 : ℝ)..t, |t - s| * ‖G s‖| := by
  refine (norm_add₃_le).trans (add_le_add (add_le_add ?_ ?_) ?_)
  · exact ((waveCosine F t).le_opNorm f).trans
      (mul_le_of_le_one_left (norm_nonneg f) (norm_waveCosine_le t))
  · exact ((waveSine F t).le_opNorm g).trans (by gcongr; exact norm_waveSine_le t)
  · refine intervalIntegral.norm_integral_le_abs_of_norm_le (Eventually.of_forall fun s ↦ ?_)
      ((by fun_prop : Continuous fun s ↦ |t - s| * ‖G s‖).intervalIntegrable 0 t)
    exact ((waveSine F (t - s)).le_opNorm _).trans (by gcongr; exact norm_waveSine_le _)

section Duhamel

variable {G : ℝ → Lp F 2 (volume : Measure E)}

/-- The integral `∫₀ᵗ cos (sD) G(s) ds` of the Duhamel splitting. -/
private def duhamelCos (G : ℝ → Lp F 2 (volume : Measure E)) (t : ℝ) :
    Lp F 2 (volume : Measure E) :=
  ∫ s in (0 : ℝ)..t, waveCosine F s (G s)

/-- The integral `∫₀ᵗ D⁻¹ sin (sD) G(s) ds` of the Duhamel splitting. -/
private def duhamelSin (G : ℝ → Lp F 2 (volume : Measure E)) (t : ℝ) :
    Lp F 2 (volume : Measure E) :=
  ∫ s in (0 : ℝ)..t, waveSine F s (G s)

private theorem hasDerivAt_duhamelCos (hG : Continuous G) (t : ℝ) :
    HasDerivAt (duhamelCos G) (waveCosine F t (G t)) t :=
  (hG.waveCosine_apply.integral_hasStrictDerivAt 0 t).hasDerivAt

private theorem hasDerivAt_duhamelSin (hG : Continuous G) (t : ℝ) :
    HasDerivAt (duhamelSin G) (waveSine F t (G t)) t :=
  ((continuous_waveSine.clm_apply hG).integral_hasStrictDerivAt 0 t).hasDerivAt

/-- The Duhamel term splits as `D⁻¹ sin (tD) ∫₀ᵗ cos (sD) G - cos (tD) ∫₀ᵗ D⁻¹ sin (sD) G`. -/
private theorem integral_waveSine_sub_apply (hG : Continuous G) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, waveSine F (t - s) (G s) =
      waveSine F t (duhamelCos G t) - waveCosine F t (duhamelSin G t) := by
  have hc₁ : Continuous fun s ↦ waveCosine F s (G s) := hG.waveCosine_apply
  have hc₂ : Continuous fun s ↦ waveSine F s (G s) := continuous_waveSine.clm_apply hG
  simp_rw [waveSine_sub, sub_apply, ContinuousLinearMap.comp_apply]
  have hc₃ : Continuous fun s ↦ waveSine F t (waveCosine F s (G s)) :=
    (waveSine F t).continuous.comp hc₁
  have hc₄ : Continuous fun s ↦ waveCosine F t (waveSine F s (G s)) :=
    (waveCosine F t).continuous.comp hc₂
  rw [intervalIntegral.integral_sub (hc₃.intervalIntegrable 0 t) (hc₄.intervalIntegrable 0 t),
    duhamelCos, duhamelSin,
    (waveSine F t).intervalIntegral_comp_comm (hc₁.intervalIntegrable 0 t),
    (waveCosine F t).intervalIntegral_comp_comm (hc₂.intervalIntegrable 0 t)]

/-- Against a test function `φ` with `Δφ = ψ`, the integral `∫₀ᵗ cos ((t - s)D) G(s) ds` splits as
`⟪cos (tD) φ, ∫₀ᵗ cos (sD) G⟫ - ⟪D⁻¹ sin (tD) ψ, ∫₀ᵗ D⁻¹ sin (sD) G⟫`. -/
private theorem inner_integral_waveCosine_sub_apply {φ ψ : Lp F 2 (volume : Measure E)}
    (hψ : 𝓕 ψ =ᵐ[volume] fun ξ ↦ (laplacianSymbol ξ : ℂ) • 𝓕 φ ξ) (hG : Continuous G) (t : ℝ) :
    ⟪φ, ∫ s in (0 : ℝ)..t, waveCosine F (t - s) (G s)⟫ =
      ⟪waveCosine F t φ, duhamelCos G t⟫ - ⟪waveSine F t ψ, duhamelSin G t⟫ := by
  have hc₁ : Continuous fun s ↦ waveCosine F s (G s) := hG.waveCosine_apply
  have hc₂ : Continuous fun s ↦ waveSine F s (G s) := continuous_waveSine.clm_apply hG
  have hc₃ : Continuous fun s ↦ waveCosine F (t - s) (G s) := by
    have := (hG.comp (continuous_sub_left t)).waveCosine_apply.comp (continuous_sub_left t)
    simpa [Function.comp_def] using this
  have hinner (y : Lp F 2 (volume : Measure E)) {h : ℝ → Lp F 2 (volume : Measure E)}
      (hh : Continuous h) : ⟪y, ∫ s in (0 : ℝ)..t, h s⟫ = ∫ s in (0 : ℝ)..t, ⟪y, h s⟫ :=
    ((innerSL ℂ y).intervalIntegral_comp_comm (hh.intervalIntegrable 0 t)).symm
  rw [duhamelCos, duhamelSin, hinner _ hc₃, hinner _ hc₁, hinner _ hc₂,
    ← intervalIntegral.integral_sub ((continuous_const.inner hc₁).intervalIntegrable 0 t)
      ((continuous_const.inner hc₂).intervalIntegrable 0 t)]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  rw [← inner_waveCosine_apply, waveCosine_sub_apply hψ, inner_sub_left, inner_waveCosine_apply,
    inner_waveSine_apply]

variable {φ ψ : Lp F 2 (volume : Measure E)}

/-- **The weak velocity of the solution of the wave equation.** For a test function `φ ∈ L²` with
`Δφ = ψ ∈ L²`, the pairing `t ↦ ⟪φ, u(t)⟫` of the solution
`u(t) = cos (tD) f + D⁻¹ sin (tD) g + ∫₀ᵗ D⁻¹ sin ((t - s)D) G(s) ds` is differentiable, with
derivative `⟪ψ, D⁻¹ sin (tD) f⟫ + ⟪φ, cos (tD) g + ∫₀ᵗ cos ((t - s)D) G(s) ds⟫`, the pairing of
`φ` with the velocity `∂ₜu = D⁻¹ sin (tD) Δf + cos (tD) g + ∫₀ᵗ cos ((t - s)D) G(s) ds`. -/
theorem hasDerivAt_inner_waveSolution
    (hψ : 𝓕 ψ =ᵐ[volume] fun ξ ↦ (laplacianSymbol ξ : ℂ) • 𝓕 φ ξ)
    (f g : Lp F 2 (volume : Measure E)) (hG : Continuous G) (t : ℝ) :
    HasDerivAt (fun t ↦ ⟪φ, waveSolution F f g G t⟫)
      (⟪ψ, waveSine F t f⟫ +
        ⟪φ, waveCosine F t g + ∫ s in (0 : ℝ)..t, waveCosine F (t - s) (G s)⟫) t := by
  -- Move the propagators onto `φ`, so that only `φ` and `ψ` are differentiated in time.
  have hfun : (fun t ↦ ⟪φ, waveSolution F f g G t⟫) = fun t ↦ ⟪waveCosine F t φ, f⟫ +
      ⟪φ, waveSine F t g⟫ + (⟪waveSine F t φ, duhamelCos G t⟫ -
        ⟪waveCosine F t φ, duhamelSin G t⟫) := by
    ext t
    rw [waveSolution_def, integral_waveSine_sub_apply hG]
    simp only [inner_add_right, inner_sub_right, inner_waveSine_apply, inner_waveCosine_apply]
  rw [hfun, inner_add_right, inner_integral_waveCosine_sub_apply hψ hG]
  have h₁ := (hasDerivAt_waveCosine_apply hψ t).inner ℂ (hasDerivAt_const t f)
  have h₂ := (hasDerivAt_const t φ).inner ℂ (hasDerivAt_waveSine_apply g t)
  have h₃ := (hasDerivAt_waveSine_apply φ t).inner ℂ (hasDerivAt_duhamelCos hG t)
  have h₄ := (hasDerivAt_waveCosine_apply hψ t).inner ℂ (hasDerivAt_duhamelSin hG t)
  convert (h₁.add h₂).add (h₃.sub h₄) using 1
  simp only [inner_zero_left, inner_zero_right, inner_waveSine_apply, inner_waveCosine_apply,
    waveSine_apply_waveCosine_apply]
  ring

/-- The weak velocity of `hasDerivAt_inner_waveSolution` has derivative `⟪ψ, u(t)⟫ + ⟪φ, G(t)⟫`. -/
private theorem hasDerivAt_inner_waveVelocity
    (hψ : 𝓕 ψ =ᵐ[volume] fun ξ ↦ (laplacianSymbol ξ : ℂ) • 𝓕 φ ξ)
    (f g : Lp F 2 (volume : Measure E)) (hG : Continuous G) (t : ℝ) :
    HasDerivAt (fun t ↦ ⟪ψ, waveSine F t f⟫ +
        ⟪φ, waveCosine F t g + ∫ s in (0 : ℝ)..t, waveCosine F (t - s) (G s)⟫)
      (⟪ψ, waveSolution F f g G t⟫ + ⟪φ, G t⟫) t := by
  have hfun : (fun t ↦ ⟪ψ, waveSine F t f⟫ +
      ⟪φ, waveCosine F t g + ∫ s in (0 : ℝ)..t, waveCosine F (t - s) (G s)⟫) =
      fun t ↦ ⟪ψ, waveSine F t f⟫ + ⟪waveCosine F t φ, g⟫ +
        (⟪waveCosine F t φ, duhamelCos G t⟫ - ⟪waveSine F t ψ, duhamelSin G t⟫) := by
    ext t
    rw [inner_add_right, inner_integral_waveCosine_sub_apply hψ hG, ← inner_waveCosine_apply,
      add_assoc]
  -- `cos² (tD) + sin² (tD) = 1`, against `φ`.
  have hφ : ⟪φ, G t⟫ = ⟪φ, waveCosine F t (waveCosine F t (G t))⟫ -
      ⟪ψ, waveSine F t (waveSine F t (G t))⟫ := by
    conv_lhs => rw [show φ = waveCosine F (t - t) φ by simp, waveCosine_sub_apply hψ]
    simp only [inner_sub_left, inner_waveCosine_apply, inner_waveSine_apply]
  rw [hfun, waveSolution_def, integral_waveSine_sub_apply hG]
  have h₁ := (hasDerivAt_const t ψ).inner ℂ (hasDerivAt_waveSine_apply f t)
  have h₂ := (hasDerivAt_waveCosine_apply hψ t).inner ℂ (hasDerivAt_const t g)
  have h₃ := (hasDerivAt_waveCosine_apply hψ t).inner ℂ (hasDerivAt_duhamelCos hG t)
  have h₄ := (hasDerivAt_waveSine_apply ψ t).inner ℂ (hasDerivAt_duhamelSin hG t)
  convert (h₁.add h₂).add (h₃.sub h₄) using 1
  simp only [inner_add_right, inner_sub_right, inner_zero_left, inner_zero_right,
    inner_waveSine_apply, inner_waveCosine_apply]
  linear_combination hφ

/-- **The weak wave equation.** For a test function `φ ∈ L²` with `Δφ = ψ ∈ L²`, the derivative
of `t ↦ ⟪φ, u(t)⟫` is itself differentiable, with derivative `⟪ψ, u(t)⟫ + ⟪φ, G(t)⟫`: the solution
satisfies `∂ₜ²u = Δu + G` against `φ`. -/
theorem hasDerivAt_deriv_inner_waveSolution
    (hψ : 𝓕 ψ =ᵐ[volume] fun ξ ↦ (laplacianSymbol ξ : ℂ) • 𝓕 φ ξ)
    (f g : Lp F 2 (volume : Measure E)) (hG : Continuous G) (t : ℝ) :
    HasDerivAt (deriv fun t ↦ ⟪φ, waveSolution F f g G t⟫)
      (⟪ψ, waveSolution F f g G t⟫ + ⟪φ, G t⟫) t := by
  rw [funext fun t ↦ (hasDerivAt_inner_waveSolution hψ f g hG t).deriv]
  exact hasDerivAt_inner_waveVelocity hψ f g hG t

/-- **The weak initial velocity.** The pairing `t ↦ ⟪φ, u(t)⟫` has derivative `⟪φ, g⟫` at
`t = 0`. -/
theorem hasDerivAt_inner_waveSolution_zero
    (hψ : 𝓕 ψ =ᵐ[volume] fun ξ ↦ (laplacianSymbol ξ : ℂ) • 𝓕 φ ξ)
    (f g : Lp F 2 (volume : Measure E)) (hG : Continuous G) :
    HasDerivAt (fun t ↦ ⟪φ, waveSolution F f g G t⟫) ⟪φ, g⟫ 0 := by
  simpa using hasDerivAt_inner_waveSolution hψ f g hG 0

/-- **The wave equation in the sense of distributions.** For every Schwartz function `φ`, the
derivative of `t ↦ ⟪φ, u(t)⟫` has derivative `⟪Δφ, u(t)⟫ + ⟪φ, G(t)⟫`. -/
theorem hasDerivAt_deriv_inner_toLp_waveSolution (φ : 𝓢(E, F))
    (f g : Lp F 2 (volume : Measure E)) (hG : Continuous G) (t : ℝ) :
    HasDerivAt (deriv fun t ↦ ⟪φ.toLp 2, waveSolution F f g G t⟫)
      (⟪(Δ φ).toLp 2, waveSolution F f g G t⟫ + ⟪φ.toLp 2, G t⟫) t :=
  hasDerivAt_deriv_inner_waveSolution (SchwartzMap.coeFn_fourier_toLp_laplacian φ) f g hG t

end Duhamel

end TauCeti
