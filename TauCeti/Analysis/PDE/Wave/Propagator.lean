/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Wave.HalfWave
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The wave propagators `cos(tD)` and `D⁻¹ sin(tD)` on `L²`

On a finite-dimensional real inner product space `E`, let `D = √(-Δ)` be the Fourier multiplier
with symbol `TauCeti.sqrtNegLaplacianSymbol`, `ξ ↦ 2π ‖ξ‖`. The solution of the wave equation
`∂ₜ²u = Δu` with initial data `u(0) = f` and `∂ₜu(0) = g` is

`u(t) = cos(tD) f + D⁻¹ sin(tD) g`.

Both operators are Fourier multipliers with bounded real symbols:

* `cos(tD)` (`TauCeti.waveCosPropagator`) has the symbol `cos(2π t ‖ξ‖)`
  (`TauCeti.waveCosSymbol`), bounded by `1`;
* `D⁻¹ sin(tD)` (`TauCeti.waveSinPropagator`) has the symbol `sin(2π t ‖ξ‖) / (2π ‖ξ‖)`, whose value
  at `ξ = 0` is its limit `t` (`TauCeti.waveSinSymbol`, written with `Real.sinc`), bounded by
  `|t|`.

So, unlike `D` itself, both are bounded operators on `L²(E, F)` for every `t`, and no regularity
of the data is needed to form `u(t)`. In terms of the half-wave propagators `W±(t) = exp(±itD)`,
`cos(tD) = (W₊(t) + W₋(t)) / 2` (`TauCeti.waveCosPropagator_eq_halfWavePropagator`).

The time derivatives are computed at every frequency and passed to `L²` by dominated convergence
(`MeasureTheory.Lp.hasDerivAt_fourierMultiplierCLM_toLp_apply`):

* `∂ₜ (D⁻¹ sin(tD) g) = cos(tD) g` for every `g ∈ L²`
  (`TauCeti.hasDerivAt_waveSinPropagator_apply`), since `∂ₜ (sin(tω) / ω) = cos(tω)` and
  `t ↦ sin(tω) / ω` is `1`-Lipschitz;
* `∂ₜ (cos(tD) f) = D⁻¹ sin(tD) Δf` when the distributional Laplacian `Δf` lies in `L²`
  (`TauCeti.hasDerivAt_waveCosPropagator_apply`), since `∂ₜ cos(tω) = -ω² sin(tω) / ω`, and
  `-ω²` is the symbol of `Δ`.

Both operators commute with `Δ` (`TauCeti.laplacian_waveCosPropagator_apply`,
`TauCeti.laplacian_waveSinPropagator_apply`). These are the facts from which
`TauCeti.Analysis.PDE.Wave.Energy` builds strong solutions of the wave equation, their energy
identity and Duhamel's formula.

## Main declarations

* `TauCeti.waveCosSymbol`, `TauCeti.waveSinSymbol`: the symbols, with
  `TauCeti.sqrtNegLaplacianSymbol_mul_waveSinSymbol`: `2π ‖ξ‖ · sin(2π t ‖ξ‖) / (2π ‖ξ‖) =
  sin(2π t ‖ξ‖)`.
* `TauCeti.integrable_waveCosSymbol_smul`, `TauCeti.integrable_waveSinSymbol_smul`: both symbols
  are bounded, so multiplying by them preserves integrability.
* `TauCeti.waveCosPropagator`, `TauCeti.waveSinPropagator`: the operators on `L²(E, F)`, with
  their Fourier-side description, their values at `t = 0` and their norm bounds. Both commute with
  every `L²` Fourier multiplier (`TauCeti.fourierMultiplierCLM_waveCosPropagator_apply`,
  `TauCeti.fourierMultiplierCLM_waveSinPropagator_apply`).
* `TauCeti.waveCosPropagator_eq_halfWavePropagator`: `cos(tD) = (W₊(t) + W₋(t)) / 2`.
* `TauCeti.norm_waveSinPropagator_sub_le`: `t ↦ D⁻¹ sin(tD)` is `1`-Lipschitz in operator norm,
  and `TauCeti.continuous_waveSinPropagator_uncurry`: `(t, g) ↦ D⁻¹ sin(tD) g` is jointly
  continuous. Hence retarded Duhamel integrals are measurable in time
  (`TauCeti.aestronglyMeasurable_setIntegral_Iio_waveSinPropagator_sub`).
* `TauCeti.hasDerivAt_waveSinPropagator_apply`, `TauCeti.hasDerivAt_waveCosPropagator_apply`:
  the time derivatives.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., Section 4.3.1 (the wave equation by
  Fourier transform).
-/

public section

noncomputable section

open scoped FourierTransform Laplacian SchwartzMap Topology ENNReal
open MeasureTheory Filter Real

namespace TauCeti

section Symbol

variable {E : Type*} [NormedAddCommGroup E]

/-- The symbol `cos(2π t ‖ξ‖)` of `cos(tD)`, `D = √(-Δ)`. -/
def waveCosSymbol (t : ℝ) (ξ : E) : ℂ :=
  Real.cos (t * sqrtNegLaplacianSymbol ξ)

theorem waveCosSymbol_apply (t : ℝ) (ξ : E) :
    waveCosSymbol t ξ = Real.cos (t * sqrtNegLaplacianSymbol ξ) :=
  (rfl)

/-- The symbol `sin(2π t ‖ξ‖) / (2π ‖ξ‖)` of `D⁻¹ sin(tD)`, `D = √(-Δ)`, written as
`t sinc(2π t ‖ξ‖)`, so that its value at `ξ = 0` is its limit `t`. -/
def waveSinSymbol (t : ℝ) (ξ : E) : ℂ :=
  t * Real.sinc (t * sqrtNegLaplacianSymbol ξ)

theorem waveSinSymbol_apply (t : ℝ) (ξ : E) :
    waveSinSymbol t ξ = t * Real.sinc (t * sqrtNegLaplacianSymbol ξ) :=
  (rfl)

@[simp]
theorem waveCosSymbol_zero (ξ : E) : waveCosSymbol 0 ξ = 1 := by
  simp [waveCosSymbol_apply]

@[simp]
theorem waveSinSymbol_zero (ξ : E) : waveSinSymbol 0 ξ = 0 := by
  simp [waveSinSymbol_apply]

/-- `ω · sin(tω) / ω = sin(tω)` for the frequency `ω = 2π ‖ξ‖`, including at `ξ = 0`. -/
theorem sqrtNegLaplacianSymbol_mul_waveSinSymbol (t : ℝ) (ξ : E) :
    (sqrtNegLaplacianSymbol ξ : ℂ) * waveSinSymbol t ξ =
      Real.sin (t * sqrtNegLaplacianSymbol ξ) := by
  rw [waveSinSymbol_apply]
  norm_cast
  rcases eq_or_ne (t * sqrtNegLaplacianSymbol ξ) 0 with h | h
  · rw [h, Real.sin_zero, Real.sinc_zero, mul_one, mul_comm, h]
  · rw [Real.sinc_of_ne_zero h, ← mul_assoc, mul_comm _ t, mul_div_assoc']
    exact mul_div_cancel_left₀ _ h

theorem norm_waveCosSymbol_le (t : ℝ) (ξ : E) : ‖waveCosSymbol t ξ‖ ≤ 1 := by
  rw [waveCosSymbol_apply, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_cos_le_one _

theorem norm_waveSinSymbol_le (t : ℝ) (ξ : E) : ‖waveSinSymbol t ξ‖ ≤ |t| := by
  rw [waveSinSymbol_apply, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg t) (Real.abs_sinc_le_one _)

/-- `∂ₜ (sin(tω) / ω) = cos(tω)`. -/
theorem hasDerivAt_waveSinSymbol (t : ℝ) (ξ : E) :
    HasDerivAt (fun s ↦ waveSinSymbol s ξ) (waveCosSymbol t ξ) t := by
  simp only [waveSinSymbol_apply, waveCosSymbol_apply, ← Complex.ofReal_mul]
  refine HasDerivAt.ofReal_comp ?_
  set ω := sqrtNegLaplacianSymbol ξ
  rcases eq_or_ne ω 0 with hω | hω
  · simpa [hω] using hasDerivAt_id' t
  · have h : (fun s ↦ s * Real.sinc (s * ω)) = fun s ↦ Real.sin (s * ω) / ω := by
      ext s
      rcases eq_or_ne s 0 with rfl | hs
      · simp
      · rw [Real.sinc_of_ne_zero (mul_ne_zero hs hω)]
        field_simp
    rw [h]
    convert (hasDerivAt_mul_const ω (x := t)).sin.div_const ω using 1
    field_simp

/-- `∂ₜ cos(tω) = -ω² · sin(tω) / ω`, where `-ω² = -4π² ‖ξ‖²` is the symbol of `Δ`. -/
theorem hasDerivAt_waveCosSymbol (t : ℝ) (ξ : E) :
    HasDerivAt (fun s ↦ waveCosSymbol s ξ) (laplacianSymbol ξ * waveSinSymbol t ξ) t := by
  have h : (laplacianSymbol ξ : ℂ) * waveSinSymbol t ξ =
      ((-(Real.sin (t * sqrtNegLaplacianSymbol ξ) * sqrtNegLaplacianSymbol ξ) : ℝ) : ℂ) := by
    have hω := sqrtNegLaplacianSymbol_mul_waveSinSymbol t ξ
    rw [neg_eq_iff_eq_neg.1 (sq_sqrtNegLaplacianSymbol ξ).symm]
    push_cast at hω ⊢
    linear_combination (-(sqrtNegLaplacianSymbol ξ : ℂ)) * hω
  simp only [waveCosSymbol_apply, h]
  exact (((hasDerivAt_id t).mul_const _).cos.congr_deriv (by simp)).ofReal_comp

/-- `t ↦ sin(tω) / ω` is `1`-Lipschitz, uniformly in `ξ`. -/
theorem norm_waveSinSymbol_sub_le (s t : ℝ) (ξ : E) :
    ‖waveSinSymbol s ξ - waveSinSymbol t ξ‖ ≤ |s - t| := by
  have := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun τ ↦ waveSinSymbol τ ξ) (fun τ _ ↦ (hasDerivAt_waveSinSymbol τ ξ).hasDerivWithinAt)
    (fun τ _ ↦ norm_waveCosSymbol_le τ ξ) (Set.mem_univ t) (Set.mem_univ s)
  rwa [one_mul, Real.norm_eq_abs] at this

/-- The variation of `t ↦ cos(tω)` is at most `ω² (|s| + |t|) |s - t|`. -/
theorem norm_waveCosSymbol_sub_le (s t : ℝ) (ξ : E) :
    ‖waveCosSymbol s ξ - waveCosSymbol t ξ‖ ≤
      ‖(laplacianSymbol ξ : ℂ)‖ * (|s| + |t|) * |s - t| := by
  have hbound : ∀ τ ∈ Set.uIcc t s,
      ‖(laplacianSymbol ξ : ℂ) * waveSinSymbol τ ξ‖ ≤ ‖(laplacianSymbol ξ : ℂ)‖ * (|s| + |t|) :=
    fun τ hτ ↦ by
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ((norm_waveSinSymbol_le τ ξ).trans ?_) (norm_nonneg _)
      rcases Set.mem_uIcc.1 hτ with h | h <;>
        exact abs_le.2 ⟨by linarith [neg_abs_le s, neg_abs_le t, abs_nonneg s, abs_nonneg t],
          by linarith [le_abs_self s, le_abs_self t, abs_nonneg s, abs_nonneg t]⟩
  have := (convex_uIcc t s).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun τ ↦ waveCosSymbol τ ξ) (fun τ _ ↦ (hasDerivAt_waveCosSymbol τ ξ).hasDerivWithinAt)
    hbound Set.left_mem_uIcc Set.right_mem_uIcc
  rwa [Real.norm_eq_abs] at this

theorem continuous_waveCosSymbol (t : ℝ) : Continuous (waveCosSymbol (E := E) t) :=
  Complex.continuous_ofReal.comp
    (Real.continuous_cos.comp (continuous_const.mul sqrtNegLaplacianSymbol.continuous))

theorem continuous_waveSinSymbol (t : ℝ) : Continuous (waveSinSymbol (E := E) t) :=
  continuous_const.mul (Complex.continuous_ofReal.comp
    (Real.continuous_sinc.comp (continuous_const.mul sqrtNegLaplacianSymbol.continuous)))

theorem norm_waveCosSymbol_smul_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (t : ℝ) (ξ : E) (y : F) : ‖waveCosSymbol t ξ • y‖ ≤ ‖y‖ := by
  rw [norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_waveCosSymbol_le t ξ)

theorem norm_waveSinSymbol_smul_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (t : ℝ) (ξ : E) (y : F) : ‖waveSinSymbol t ξ • y‖ ≤ |t| * ‖y‖ := by
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (norm_waveSinSymbol_le t ξ) (norm_nonneg _)

/-- Multiplying an integrable function by the symbol of `cos(tD)` keeps it integrable. -/
theorem integrable_waveCosSymbol_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} {a : E → F}
    (ha : Integrable a μ) (t : ℝ) : Integrable (fun ξ ↦ waveCosSymbol t ξ • a ξ) μ :=
  ha.bdd_smul 1 (continuous_waveCosSymbol t).aestronglyMeasurable
    (ae_of_all _ (norm_waveCosSymbol_le t))

/-- Multiplying an integrable function by the symbol of `D⁻¹ sin(tD)` keeps it integrable. -/
theorem integrable_waveSinSymbol_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E} {a : E → F}
    (ha : Integrable a μ) (t : ℝ) : Integrable (fun ξ ↦ waveSinSymbol t ξ • a ξ) μ :=
  ha.bdd_smul |t| (continuous_waveSinSymbol t).aestronglyMeasurable
    (ae_of_all _ (norm_waveSinSymbol_le t))

/-- `cos x = (e^{ix} + e^{-ix}) / 2` for the half-wave phases `x = ±2π t ‖ξ‖`. -/
theorem waveCosSymbol_eq_phaseSymbol (t : ℝ) (ξ : E) :
    waveCosSymbol t ξ = 2⁻¹ * (phaseSymbol sqrtNegLaplacianSymbol t ξ +
      phaseSymbol sqrtNegLaplacianSymbol (-t) ξ) := by
  rw [waveCosSymbol_apply, phaseSymbol_apply, phaseSymbol_apply, Complex.ofReal_cos,
    Complex.cos]
  push_cast
  ring_nf

end Symbol

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem memLp_waveCosSymbol (t : ℝ) : MemLp (waveCosSymbol (E := E) t) ∞ volume :=
  memLp_top_of_bound (continuous_waveCosSymbol t).aestronglyMeasurable 1
    (Eventually.of_forall fun ξ ↦ norm_waveCosSymbol_le t ξ)

theorem memLp_waveSinSymbol (t : ℝ) : MemLp (waveSinSymbol (E := E) t) ∞ volume :=
  memLp_top_of_bound (continuous_waveSinSymbol t).aestronglyMeasurable |t|
    (Eventually.of_forall fun ξ ↦ norm_waveSinSymbol_le t ξ)

variable (F) in
/-- The operator `cos(tD)` on `L²(E, F)`, `D = √(-Δ)`: the Fourier multiplier with symbol
`cos(2π t ‖ξ‖)`. -/
def waveCosPropagator (t : ℝ) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  Lp.fourierMultiplierCLM F ((memLp_waveCosSymbol t).toLp _)

variable (F) in
/-- The operator `D⁻¹ sin(tD)` on `L²(E, F)`, `D = √(-Δ)`: the Fourier multiplier with symbol
`sin(2π t ‖ξ‖) / (2π ‖ξ‖)`, which takes the value `t` at `ξ = 0`. It is bounded although `D⁻¹`
is not. -/
def waveSinPropagator (t : ℝ) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  Lp.fourierMultiplierCLM F ((memLp_waveSinSymbol t).toLp _)

theorem waveCosPropagator_def (t : ℝ) :
    waveCosPropagator (E := E) F t = Lp.fourierMultiplierCLM F ((memLp_waveCosSymbol t).toLp _) :=
  (rfl)

theorem waveSinPropagator_def (t : ℝ) :
    waveSinPropagator (E := E) F t = Lp.fourierMultiplierCLM F ((memLp_waveSinSymbol t).toLp _) :=
  (rfl)

/-- On the Fourier side, `cos(tD)` is pointwise multiplication by `cos(2π t ‖ξ‖)`, almost
everywhere. -/
theorem coeFn_fourier_waveCosPropagator (t : ℝ) (f : Lp F 2 (volume : Measure E)) :
    𝓕 (waveCosPropagator F t f) =ᵐ[volume] fun ξ ↦ waveCosSymbol t ξ • 𝓕 f ξ :=
  Lp.coeFn_fourier_fourierMultiplierCLM_toLp f (memLp_waveCosSymbol t)

/-- On the Fourier side, `D⁻¹ sin(tD)` is pointwise multiplication by
`sin(2π t ‖ξ‖) / (2π ‖ξ‖)`, almost everywhere. -/
theorem coeFn_fourier_waveSinPropagator (t : ℝ) (f : Lp F 2 (volume : Measure E)) :
    𝓕 (waveSinPropagator F t f) =ᵐ[volume] fun ξ ↦ waveSinSymbol t ξ • 𝓕 f ξ :=
  Lp.coeFn_fourier_fourierMultiplierCLM_toLp f (memLp_waveSinSymbol t)

/-- `cos(tD)` commutes with every `L²` Fourier multiplier, applied form. -/
theorem fourierMultiplierCLM_waveCosPropagator_apply (t : ℝ) (m : Lp ℂ ∞ (volume : Measure E))
    (f : Lp F 2 (volume : Measure E)) :
    Lp.fourierMultiplierCLM F m (waveCosPropagator F t f) =
      waveCosPropagator F t (Lp.fourierMultiplierCLM F m f) :=
  Lp.fourierMultiplierCLM_fourierMultiplierCLM_comm _ _ f

/-- `D⁻¹ sin(tD)` commutes with every `L²` Fourier multiplier, applied form. -/
theorem fourierMultiplierCLM_waveSinPropagator_apply (t : ℝ) (m : Lp ℂ ∞ (volume : Measure E))
    (f : Lp F 2 (volume : Measure E)) :
    Lp.fourierMultiplierCLM F m (waveSinPropagator F t f) =
      waveSinPropagator F t (Lp.fourierMultiplierCLM F m f) :=
  Lp.fourierMultiplierCLM_fourierMultiplierCLM_comm _ _ f

/-- `cos(0D)` is the identity. -/
@[simp]
theorem waveCosPropagator_zero :
    waveCosPropagator F (0 : ℝ) = ContinuousLinearMap.id ℂ (Lp F 2 (volume : Measure E)) := by
  rw [waveCosPropagator_def, Lp.fourierMultiplierCLM_of_ae_eq_const (c := 1) ?_, one_smul]
  filter_upwards [(memLp_waveCosSymbol (E := E) 0).coeFn_toLp] with ξ h
  simp [h]

/-- `D⁻¹ sin(0D)` is zero. -/
@[simp]
theorem waveSinPropagator_zero : waveSinPropagator (E := E) F 0 = 0 := by
  rw [waveSinPropagator_def, Lp.fourierMultiplierCLM_of_ae_eq_const (c := 0) ?_]
  · exact zero_smul ℂ (ContinuousLinearMap.id ℂ (Lp F 2 (volume : Measure E)))
  filter_upwards [(memLp_waveSinSymbol (E := E) 0).coeFn_toLp] with ξ h
  simp [h]

/-- `cos(tD)` has operator norm at most `1`. -/
theorem norm_waveCosPropagator_le (t : ℝ) : ‖waveCosPropagator (E := E) F t‖ ≤ 1 :=
  Lp.norm_fourierMultiplierCLM_toLp_le _ zero_le_one
    (Eventually.of_forall (norm_waveCosSymbol_le t))

/-- `D⁻¹ sin(tD)` has operator norm at most `|t|`. -/
theorem norm_waveSinPropagator_le (t : ℝ) : ‖waveSinPropagator (E := E) F t‖ ≤ |t| :=
  Lp.norm_fourierMultiplierCLM_toLp_le _ (abs_nonneg t)
    (Eventually.of_forall (norm_waveSinSymbol_le t))

/-- `t ↦ D⁻¹ sin(tD)` is `1`-Lipschitz in operator norm. -/
theorem norm_waveSinPropagator_sub_le (s t : ℝ) :
    ‖waveSinPropagator (E := E) F s - waveSinPropagator F t‖ ≤ |s - t| := by
  rw [waveSinPropagator_def, waveSinPropagator_def, ← Lp.fourierMultiplierCLM_sub,
    ← MemLp.toLp_sub]
  exact Lp.norm_fourierMultiplierCLM_toLp_le _ (abs_nonneg _)
    (Eventually.of_forall (norm_waveSinSymbol_sub_le s t))

/-- `(t, g) ↦ D⁻¹ sin(tD) g` is jointly continuous. -/
theorem continuous_waveSinPropagator_uncurry :
    Continuous fun p : ℝ × Lp F 2 (volume : Measure E) ↦ waveSinPropagator F p.1 p.2 :=
  ((LipschitzWith.mk_one (f := waveSinPropagator (E := E) F) fun s t ↦
    (dist_eq_norm _ _).trans_le ((norm_waveSinPropagator_sub_le s t).trans_eq
      (Real.dist_eq s t).symm)).continuous.comp continuous_fst).clm_apply continuous_snd

/-- The retarded Duhamel integral `t ↦ ∫_{s < t} D⁻¹ sin((t - s)D) G(s) ds` of an almost
everywhere strongly measurable `G : ℝ → L²` is almost everywhere strongly measurable. Where the
integral does not exist it takes the value `0`. -/
theorem aestronglyMeasurable_setIntegral_Iio_waveSinPropagator_sub
    {G : ℝ → Lp F 2 (volume : Measure E)} (hG : AEStronglyMeasurable G) :
    AEStronglyMeasurable fun t ↦ ∫ s in Set.Iio t, waveSinPropagator F (t - s) (G s) := by
  -- The integrand on the half-plane `s < t`, as a function of `(t, s)`.
  set K : ℝ × ℝ → Lp F 2 (volume : Measure E) := {q : ℝ × ℝ | q.2 < q.1}.indicator
    fun q ↦ waveSinPropagator F (q.1 - q.2) (G q.2)
  have hK : AEStronglyMeasurable K (volume.prod volume) :=
    (continuous_waveSinPropagator_uncurry.comp_aestronglyMeasurable
      ((continuous_fst.sub continuous_snd).aestronglyMeasurable.prodMk hG.comp_snd)).indicator
      (measurableSet_lt measurable_snd measurable_fst)
  refine hK.integral_prod_right'.congr (ae_of_all _ fun t ↦ ?_)
  dsimp only
  rw [← integral_indicator measurableSet_Iio]
  refine integral_congr_ae (ae_of_all _ fun s ↦ ?_)
  -- `(t, s)` lies in the half-plane `s < t` exactly when `s ∈ Iio t`.
  by_cases hs : s < t <;> simp [K, hs]

/-- `cos(tD) = (W₊(t) + W₋(t)) / 2`, where `W₊(t) = exp(itD)` is the half-wave propagator and
`W₋(t) = W₊(-t)`. -/
theorem waveCosPropagator_eq_halfWavePropagator (t : ℝ) :
    waveCosPropagator (E := E) F t =
      (2⁻¹ : ℂ) • (halfWavePropagator F t + halfWavePropagator F (-t)) := by
  rw [halfWavePropagator_def, halfWavePropagator_def, phasePropagator_def, phasePropagator_def,
    ← Lp.fourierMultiplierCLM_add, ← Lp.fourierMultiplierCLM_smul, ← MemLp.toLp_add,
    ← MemLp.toLp_const_smul, waveCosPropagator_def]
  congr 1
  exact MemLp.toLp_congr _ _ (.of_forall fun ξ ↦ waveCosSymbol_eq_phaseSymbol t ξ)

/-- `t ↦ cos(tD) f` is continuous for every `f ∈ L²`. -/
theorem continuous_waveCosPropagator_apply (f : Lp F 2 (volume : Measure E)) :
    Continuous fun t ↦ waveCosPropagator F t f := by
  simp only [waveCosPropagator_eq_halfWavePropagator, _root_.smul_apply,
    _root_.add_apply]
  exact ((continuous_phasePropagator_apply _ f).add
    ((continuous_phasePropagator_apply _ f).comp continuous_neg)).const_smul (2⁻¹ : ℂ)

/-- **The derivative of `D⁻¹ sin(tD) g`**: `∂ₜ (D⁻¹ sin(tD) g) = cos(tD) g` in `L²`, for every
`g ∈ L²`. -/
theorem hasDerivAt_waveSinPropagator_apply (g : Lp F 2 (volume : Measure E)) (t : ℝ) :
    HasDerivAt (fun s ↦ waveSinPropagator F s g) (waveCosPropagator F t g) t := by
  refine Lp.hasDerivAt_fourierMultiplierCLM_toLp_apply memLp_waveSinSymbol
    (memLp_waveCosSymbol t) (a := fun _ ↦ 1) (C := 1) (by simp)
    (Eventually.of_forall fun ξ ↦ by simpa using hasDerivAt_waveSinSymbol t ξ)
    (Eventually.of_forall fun s ↦ Eventually.of_forall fun ξ ↦ by
      simpa using norm_waveSinSymbol_sub_le s t ξ)

/-- `t ↦ D⁻¹ sin(tD) g` is continuous for every `g ∈ L²`. -/
theorem continuous_waveSinPropagator_apply (g : Lp F 2 (volume : Measure E)) :
    Continuous fun t ↦ waveSinPropagator F t g :=
  continuous_iff_continuousAt.2 fun t ↦ (hasDerivAt_waveSinPropagator_apply g t).continuousAt

/-- **The derivative of `cos(tD) f`**: if the distributional Laplacian of `f ∈ L²` is the `L²`
function `h`, then `∂ₜ (cos(tD) f) = D⁻¹ sin(tD) h` in `L²`. -/
theorem hasDerivAt_waveCosPropagator_apply {f h : Lp F 2 (volume : Measure E)}
    (hfh : Δ (f : 𝓢'(E, F)) = (h : 𝓢'(E, F))) (t : ℝ) :
    HasDerivAt (fun s ↦ waveCosPropagator F s f) (waveSinPropagator F t h) t := by
  refine Lp.hasDerivAt_fourierMultiplierCLM_toLp_apply memLp_waveCosSymbol
    (memLp_waveSinSymbol t) (a := fun ξ ↦ (laplacianSymbol ξ : ℂ)) (C := 2 * |t| + 1)
    ((Lp.laplacian_toTemperedDistribution_eq_iff f h).1 hfh)
    (Eventually.of_forall fun ξ ↦ hasDerivAt_waveCosSymbol t ξ) ?_
  filter_upwards [nhdsWithin_le_nhds (continuous_abs.continuousAt.eventually_lt
    continuousAt_const (lt_add_one |t|))] with s hs
  refine Eventually.of_forall fun ξ ↦ (norm_waveCosSymbol_sub_le s t ξ).trans ?_
  have : |s| + |t| ≤ 2 * |t| + 1 := by linarith
  calc ‖(laplacianSymbol ξ : ℂ)‖ * (|s| + |t|) * |s - t|
      ≤ ‖(laplacianSymbol ξ : ℂ)‖ * (2 * |t| + 1) * |s - t| := by gcongr
    _ = (2 * |t| + 1) * ‖(laplacianSymbol ξ : ℂ)‖ * |s - t| := by ring

/-- `cos(tD)` commutes with `Δ`: if `Δ f = h` with `h ∈ L²`, then `Δ (cos(tD) f) = cos(tD) h`. -/
theorem laplacian_waveCosPropagator_apply {f h : Lp F 2 (volume : Measure E)}
    (hfh : Δ (f : 𝓢'(E, F)) = (h : 𝓢'(E, F))) (t : ℝ) :
    Δ ((waveCosPropagator F t f : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) =
      (waveCosPropagator F t h : 𝓢'(E, F)) :=
  Lp.laplacian_fourierMultiplierCLM_apply _ hfh

/-- `D⁻¹ sin(tD)` commutes with `Δ`: if `Δ f = h` with `h ∈ L²`, then
`Δ (D⁻¹ sin(tD) f) = D⁻¹ sin(tD) h`. -/
theorem laplacian_waveSinPropagator_apply {f h : Lp F 2 (volume : Measure E)}
    (hfh : Δ (f : 𝓢'(E, F)) = (h : 𝓢'(E, F))) (t : ℝ) :
    Δ ((waveSinPropagator F t f : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) =
      (waveSinPropagator F t h : 𝓢'(E, F)) :=
  Lp.laplacian_fourierMultiplierCLM_apply _ hfh

end TauCeti
