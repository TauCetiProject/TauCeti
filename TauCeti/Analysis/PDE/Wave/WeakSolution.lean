/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.PDE.Wave.Propagator
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Weak solutions of the forced wave equation on `L²`

On a finite-dimensional real inner product space `E`, let `D = √(-Δ)` be the Fourier multiplier
with symbol `TauCeti.sqrtNegLaplacianSymbol`, `ξ ↦ 2π ‖ξ‖`. The Cauchy problem for the wave
equation

`∂ₜ²u - Δu = G`, `u(0) = f`, `∂ₜu(0) = g`

is solved by Duhamel's formula

`u(t) = cos (tD) f + D⁻¹ sin (tD) g + ∫₀ᵗ D⁻¹ sin ((t - s)D) G(s) ds`

in terms of the propagators `cos (tD)` (`TauCeti.waveCosPropagator`) and `D⁻¹ sin (tD)`
(`TauCeti.waveSinPropagator`). Every strong solution is given by this formula
(`TauCeti.IsWaveSolutionOn.eq_waveCosPropagator_add_waveSinPropagator_add_integral`). Conversely,
this file shows that the
formula `TauCeti.waveDuhamelSolution f g G` solves the forced problem for all data `f, g ∈ L²` and
every continuous forcing `G : ℝ → L²`, in the weak sense.

The solution starts from `f` (`TauCeti.waveDuhamelSolution_zero`), it is bounded by
`‖u(t)‖ ≤ ‖f‖ + |t| ‖g‖ + |∫₀ᵗ |t - s| ‖G(s)‖ ds|` (`TauCeti.norm_waveDuhamelSolution_le`), and
for every `φ ∈ L²` whose distributional Laplacian `ψ = Δφ` lies in `L²`, the scalar function
`t ↦ ⟪φ, u(t)⟫` is twice differentiable, with

`d/dt ⟪φ, u(t)⟫ = ⟪ψ, D⁻¹ sin (tD) f⟫ + ⟪φ, cos (tD) g + ∫₀ᵗ cos ((t - s)D) G(s) ds⟫`,
`d²/dt² ⟪φ, u(t)⟫ = ⟪ψ, u(t)⟫ + ⟪φ, G(t)⟫`

(`TauCeti.hasDerivAt_inner_waveDuhamelSolution`,
`TauCeti.hasDerivAt_deriv_inner_waveDuhamelSolution`). At `t = 0` the first derivative is
`⟪φ, g⟫`, so `u` takes the initial velocity `g` weakly
(`TauCeti.hasDerivAt_inner_waveDuhamelSolution_zero`). Every Schwartz function `φ` is admissible,
with `ψ = Δφ`, so `u` solves the wave equation in the sense of distributions in space
(`TauCeti.hasDerivAt_deriv_inner_toLp_waveDuhamelSolution`).

The Duhamel term is differentiated through the subtraction formula
`D⁻¹ sin ((t - s)D) = D⁻¹ sin (tD) cos (sD) - cos (tD) D⁻¹ sin (sD)`
(`TauCeti.waveSinPropagator_sub`), which splits it into bounded operators of `t` applied to
integrals from `0` to `t`. The propagators are self-adjoint, so they can be moved onto the test
function `φ`, where the time derivatives of `TauCeti.Analysis.PDE.Wave.Propagator` apply.

## Main declarations

* `TauCeti.isSelfAdjoint_waveCosPropagator`, `TauCeti.isSelfAdjoint_waveSinPropagator`:
  self-adjointness of the propagators.
* `TauCeti.waveSinPropagator_sub`, `TauCeti.waveCosPropagator_sub_apply`: the subtraction formulas.
* `TauCeti.waveDuhamelSolution`: the solution formula, and
  `TauCeti.hasDerivAt_inner_waveDuhamelSolution`,
  `TauCeti.hasDerivAt_deriv_inner_waveDuhamelSolution`: the weak wave equation.

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

/-- The subtraction formula for `t ↦ t sinc (t a)`, which is `sin (t a) / a` for `a ≠ 0`. -/
private theorem sub_mul_sinc_sub_mul (a s t : ℝ) :
    (t - s) * sinc ((t - s) * a) =
      t * sinc (t * a) * cos (s * a) - cos (t * a) * (s * sinc (s * a)) := by
  rcases eq_or_ne a 0 with rfl | h
  · simp
  · rw [mul_comm (t - s) a, mul_comm t a, mul_comm s a, mul_sinc_mul_of_ne_zero h,
      mul_sinc_mul_of_ne_zero h, mul_sinc_mul_of_ne_zero h, mul_sub, sin_sub]
    ring

/-- The subtraction formula for `cos (t a)`, in terms of `t ↦ t sinc (t a)`. -/
private theorem cos_sub_mul (a s t : ℝ) :
    cos ((t - s) * a) =
      cos (s * a) * cos (t * a) + s * sinc (s * a) * (t * sinc (t * a)) * a ^ 2 := by
  rcases eq_or_ne a 0 with rfl | h
  · simp
  · rw [mul_comm (t - s) a, mul_comm t a, mul_comm s a, mul_sinc_mul_of_ne_zero h,
      mul_sinc_mul_of_ne_zero h, mul_sub, cos_sub]
    field_simp

section Symbol

variable {E : Type*} [NormedAddCommGroup E]

theorem star_waveCosSymbol (t : ℝ) (ξ : E) : star (waveCosSymbol t ξ) = waveCosSymbol t ξ := by
  rw [waveCosSymbol_apply]
  exact Complex.conj_ofReal _

theorem star_waveSinSymbol (t : ℝ) (ξ : E) : star (waveSinSymbol t ξ) = waveSinSymbol t ξ := by
  rw [waveSinSymbol_apply, ← Complex.ofReal_mul]
  exact Complex.conj_ofReal _

/-- The subtraction formula
`sin ((t - s) a) / a = sin (t a) cos (s a) / a - cos (t a) sin (s a) / a` for the symbol of
`D⁻¹ sin (tD)`, `a = 2π ‖ξ‖`. -/
theorem waveSinSymbol_sub (s t : ℝ) (ξ : E) :
    waveSinSymbol (t - s) ξ =
      waveSinSymbol t ξ * waveCosSymbol s ξ - waveCosSymbol t ξ * waveSinSymbol s ξ := by
  simp only [waveSinSymbol_apply, waveCosSymbol_apply]
  exact_mod_cast congrArg Complex.ofReal (sub_mul_sinc_sub_mul (sqrtNegLaplacianSymbol ξ) s t)

/-- The subtraction formula `cos ((t - s) a) = cos (s a) cos (t a) + a² (sin (s a) / a)
(sin (t a) / a)` for the symbol of `cos (tD)`, with `-a²` the symbol of the Laplacian. -/
theorem waveCosSymbol_sub (s t : ℝ) (ξ : E) :
    waveCosSymbol (t - s) ξ = waveCosSymbol s ξ * waveCosSymbol t ξ -
      waveSinSymbol s ξ * waveSinSymbol t ξ * (laplacianSymbol ξ : ℂ) := by
  have hl : laplacianSymbol ξ = -sqrtNegLaplacianSymbol ξ ^ 2 := by
    rw [sq_sqrtNegLaplacianSymbol, neg_neg]
  simp only [waveSinSymbol_apply, waveCosSymbol_apply, hl,
    cos_sub_mul (sqrtNegLaplacianSymbol ξ) s t]
  push_cast
  ring

end Symbol

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Two elements of `L²` with almost everywhere equal Fourier transforms are equal. -/
private theorem eq_of_fourier_ae_eq {x y : Lp F 2 (volume : Measure E)}
    (h : ((𝓕 x : Lp F 2 (volume : Measure E)) : E → F) =ᵐ[volume]
      (𝓕 y : Lp F 2 (volume : Measure E))) : x = y := by
  simpa using congrArg 𝓕⁻ (Lp.ext h)

/-- `cos (tD)` is self-adjoint. -/
theorem isSelfAdjoint_waveCosPropagator (t : ℝ) :
    IsSelfAdjoint (waveCosPropagator (E := E) F t) := by
  rw [waveCosPropagator_def]
  refine Lp.isSelfAdjoint_fourierMultiplierCLM (Lp.ext ?_)
  filter_upwards [Lp.coeFn_star ((memLp_waveCosSymbol (E := E) t).toLp _),
    (memLp_waveCosSymbol t).coeFn_toLp] with ξ h₁ h₂
  rw [h₁, Pi.star_apply, h₂, star_waveCosSymbol]

/-- `D⁻¹ sin (tD)` is self-adjoint. -/
theorem isSelfAdjoint_waveSinPropagator (t : ℝ) :
    IsSelfAdjoint (waveSinPropagator (E := E) F t) := by
  rw [waveSinPropagator_def]
  refine Lp.isSelfAdjoint_fourierMultiplierCLM (Lp.ext ?_)
  filter_upwards [Lp.coeFn_star ((memLp_waveSinSymbol (E := E) t).toLp _),
    (memLp_waveSinSymbol t).coeFn_toLp] with ξ h₁ h₂
  rw [h₁, Pi.star_apply, h₂, star_waveSinSymbol]

/-- `cos (tD)` moves across the `L²` inner product. -/
theorem inner_waveCosPropagator_apply (t : ℝ) (f g : Lp F 2 (volume : Measure E)) :
    ⟪waveCosPropagator F t f, g⟫ = ⟪f, waveCosPropagator F t g⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, (isSelfAdjoint_waveCosPropagator t).adjoint_eq]

/-- `D⁻¹ sin (tD)` moves across the `L²` inner product. -/
theorem inner_waveSinPropagator_apply (t : ℝ) (f g : Lp F 2 (volume : Measure E)) :
    ⟪waveSinPropagator F t f, g⟫ = ⟪f, waveSinPropagator F t g⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_right, (isSelfAdjoint_waveSinPropagator t).adjoint_eq]

/-- `D⁻¹ sin (sD) cos (tD) = cos (tD) D⁻¹ sin (sD)`. -/
theorem waveSinPropagator_apply_waveCosPropagator_apply (s t : ℝ)
    (x : Lp F 2 (volume : Measure E)) :
    waveSinPropagator F s (waveCosPropagator F t x) =
      waveCosPropagator F t (waveSinPropagator F s x) := by
  rw [waveSinPropagator_def]
  exact fourierMultiplierCLM_waveCosPropagator_apply t _ x

/-- **The subtraction formula**
`D⁻¹ sin ((t - s)D) = D⁻¹ sin (tD) cos (sD) - cos (tD) D⁻¹ sin (sD)`. -/
theorem waveSinPropagator_sub (s t : ℝ) :
    waveSinPropagator (E := E) F (t - s) =
      waveSinPropagator F t ∘L waveCosPropagator F s -
        waveCosPropagator F t ∘L waveSinPropagator F s := by
  ext1 f
  refine eq_of_fourier_ae_eq ?_
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    FourierTransform.fourier_sub]
  filter_upwards [coeFn_fourier_waveSinPropagator (t - s) f,
    coeFn_fourier_waveSinPropagator t (waveCosPropagator F s f),
    coeFn_fourier_waveCosPropagator s f,
    coeFn_fourier_waveCosPropagator t (waveSinPropagator F s f),
    coeFn_fourier_waveSinPropagator s f,
    Lp.coeFn_sub (𝓕 (waveSinPropagator F t (waveCosPropagator F s f)))
      (𝓕 (waveCosPropagator F t (waveSinPropagator F s f)))] with ξ h₁ h₂ h₃ h₄ h₅ h₆
  rw [h₁, h₆, Pi.sub_apply, h₂, h₃, h₄, h₅, waveSinSymbol_sub]
  module

/-- **The subtraction formula for `cos (tD)`**, on the domain of the Laplacian: if the
distributional Laplacian of `φ ∈ L²` is the `L²` function `ψ`, then
`cos ((t - s)D) φ = cos (sD) cos (tD) φ - D⁻¹ sin (sD) D⁻¹ sin (tD) ψ`. -/
theorem waveCosPropagator_sub_apply {φ ψ : Lp F 2 (volume : Measure E)}
    (hφψ : Δ (φ : 𝓢'(E, F)) = (ψ : 𝓢'(E, F))) (s t : ℝ) :
    waveCosPropagator F (t - s) φ =
      waveCosPropagator F s (waveCosPropagator F t φ) -
        waveSinPropagator F s (waveSinPropagator F t ψ) := by
  refine eq_of_fourier_ae_eq ?_
  rw [FourierTransform.fourier_sub]
  filter_upwards [coeFn_fourier_waveCosPropagator (t - s) φ,
    coeFn_fourier_waveCosPropagator s (waveCosPropagator F t φ),
    coeFn_fourier_waveCosPropagator t φ,
    coeFn_fourier_waveSinPropagator s (waveSinPropagator F t ψ),
    coeFn_fourier_waveSinPropagator t ψ, (Lp.laplacian_toTemperedDistribution_eq_iff φ ψ).1 hφψ,
    Lp.coeFn_sub (𝓕 (waveCosPropagator F s (waveCosPropagator F t φ)))
      (𝓕 (waveSinPropagator F s (waveSinPropagator F t ψ)))] with ξ h₁ h₂ h₃ h₄ h₅ h₆ h₇
  rw [h₁, h₇, Pi.sub_apply, h₂, h₃, h₄, h₅, h₆, waveCosSymbol_sub]
  module

/-- For a continuous `G : ℝ → L²`, the map `t ↦ cos (tD) G(t)` is continuous: the operators are
strongly continuous and uniformly bounded. -/
theorem _root_.Continuous.waveCosPropagator_apply {G : ℝ → Lp F 2 (volume : Measure E)}
    (hG : Continuous G) :
    Continuous fun t ↦ waveCosPropagator F t (G t) := by
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  have h₁ : Tendsto (fun s ↦ waveCosPropagator F s (G s) - waveCosPropagator F s (G t)) (𝓝 t)
      (𝓝 0) := by
    refine squeeze_zero_norm (fun s ↦ ?_) (by simpa using ((hG.tendsto t).sub_const (G t)).norm)
    rw [← map_sub]
    exact ((waveCosPropagator F s).le_opNorm _).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_waveCosPropagator_le s))
  rw [ContinuousAt]
  simpa using h₁.add ((continuous_waveCosPropagator_apply (G t)).tendsto t)

/-- For a continuous `G : ℝ → L²`, the map `t ↦ D⁻¹ sin (tD) G(t)` is continuous. -/
theorem _root_.Continuous.waveSinPropagator_apply {G : ℝ → Lp F 2 (volume : Measure E)}
    (hG : Continuous G) :
    Continuous fun t ↦ waveSinPropagator F t (G t) :=
  continuous_waveSinPropagator_uncurry.comp (continuous_id.prodMk hG)

/-! ### The solution formula -/

variable (F) in
/-- **Duhamel's formula** for the Cauchy problem of the wave equation `∂ₜ²u - Δu = G`,
`u(0) = f`, `∂ₜu(0) = g` on `L²`:
`u(t) = cos (tD) f + D⁻¹ sin (tD) g + ∫₀ᵗ D⁻¹ sin ((t - s)D) G(s) ds`. -/
def waveDuhamelSolution (f g : Lp F 2 (volume : Measure E))
    (G : ℝ → Lp F 2 (volume : Measure E)) (t : ℝ) : Lp F 2 (volume : Measure E) :=
  waveCosPropagator F t f + waveSinPropagator F t g +
    ∫ s in (0 : ℝ)..t, waveSinPropagator F (t - s) (G s)

theorem waveDuhamelSolution_def (f g : Lp F 2 (volume : Measure E))
    (G : ℝ → Lp F 2 (volume : Measure E)) (t : ℝ) :
    waveDuhamelSolution F f g G t = waveCosPropagator F t f + waveSinPropagator F t g +
      ∫ s in (0 : ℝ)..t, waveSinPropagator F (t - s) (G s) :=
  (rfl)

/-- The solution starts from the initial displacement. -/
@[simp]
theorem waveDuhamelSolution_zero (f g : Lp F 2 (volume : Measure E))
    (G : ℝ → Lp F 2 (volume : Measure E)) : waveDuhamelSolution F f g G 0 = f := by
  simp [waveDuhamelSolution_def]

/-- The **a priori bound** `‖u(t)‖ ≤ ‖f‖ + |t| ‖g‖ + |∫₀ᵗ |t - s| ‖G(s)‖ ds|`. -/
theorem norm_waveDuhamelSolution_le (f g : Lp F 2 (volume : Measure E))
    {G : ℝ → Lp F 2 (volume : Measure E)} (hG : Continuous G) (t : ℝ) :
    ‖waveDuhamelSolution F f g G t‖ ≤
      ‖f‖ + |t| * ‖g‖ + |∫ s in (0 : ℝ)..t, |t - s| * ‖G s‖| := by
  refine (norm_add₃_le).trans (add_le_add (add_le_add ?_ ?_) ?_)
  · exact ((waveCosPropagator F t).le_opNorm f).trans
      (mul_le_of_le_one_left (norm_nonneg f) (norm_waveCosPropagator_le t))
  · exact ((waveSinPropagator F t).le_opNorm g).trans
      (by gcongr; exact norm_waveSinPropagator_le t)
  · refine intervalIntegral.norm_integral_le_abs_of_norm_le (Eventually.of_forall fun s ↦ ?_)
      ((by fun_prop : Continuous fun s ↦ |t - s| * ‖G s‖).intervalIntegrable 0 t)
    exact ((waveSinPropagator F (t - s)).le_opNorm _).trans
      (by gcongr; exact norm_waveSinPropagator_le _)

section Duhamel

variable {G : ℝ → Lp F 2 (volume : Measure E)}

/-- The integral `∫₀ᵗ cos (sD) G(s) ds` of the Duhamel splitting. -/
private def duhamelCos (G : ℝ → Lp F 2 (volume : Measure E)) (t : ℝ) :
    Lp F 2 (volume : Measure E) :=
  ∫ s in (0 : ℝ)..t, waveCosPropagator F s (G s)

/-- The integral `∫₀ᵗ D⁻¹ sin (sD) G(s) ds` of the Duhamel splitting. -/
private def duhamelSin (G : ℝ → Lp F 2 (volume : Measure E)) (t : ℝ) :
    Lp F 2 (volume : Measure E) :=
  ∫ s in (0 : ℝ)..t, waveSinPropagator F s (G s)

private theorem hasDerivAt_duhamelCos (hG : Continuous G) (t : ℝ) :
    HasDerivAt (duhamelCos G) (waveCosPropagator F t (G t)) t :=
  (hG.waveCosPropagator_apply.integral_hasStrictDerivAt 0 t).hasDerivAt

private theorem hasDerivAt_duhamelSin (hG : Continuous G) (t : ℝ) :
    HasDerivAt (duhamelSin G) (waveSinPropagator F t (G t)) t :=
  (hG.waveSinPropagator_apply.integral_hasStrictDerivAt 0 t).hasDerivAt

/-- The Duhamel term splits as `D⁻¹ sin (tD) ∫₀ᵗ cos (sD) G - cos (tD) ∫₀ᵗ D⁻¹ sin (sD) G`. -/
private theorem integral_waveSinPropagator_sub_apply (hG : Continuous G) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, waveSinPropagator F (t - s) (G s) =
      waveSinPropagator F t (duhamelCos G t) - waveCosPropagator F t (duhamelSin G t) := by
  have hc₁ : Continuous fun s ↦ waveCosPropagator F s (G s) := hG.waveCosPropagator_apply
  have hc₂ : Continuous fun s ↦ waveSinPropagator F s (G s) := hG.waveSinPropagator_apply
  simp_rw [waveSinPropagator_sub, sub_apply, ContinuousLinearMap.comp_apply]
  have hc₃ : Continuous fun s ↦ waveSinPropagator F t (waveCosPropagator F s (G s)) :=
    (waveSinPropagator F t).continuous.comp hc₁
  have hc₄ : Continuous fun s ↦ waveCosPropagator F t (waveSinPropagator F s (G s)) :=
    (waveCosPropagator F t).continuous.comp hc₂
  rw [intervalIntegral.integral_sub (hc₃.intervalIntegrable 0 t) (hc₄.intervalIntegrable 0 t),
    duhamelCos, duhamelSin,
    (waveSinPropagator F t).intervalIntegral_comp_comm (hc₁.intervalIntegrable 0 t),
    (waveCosPropagator F t).intervalIntegral_comp_comm (hc₂.intervalIntegrable 0 t)]

variable {φ ψ : Lp F 2 (volume : Measure E)}

/-- Against a test function `φ` with `Δφ = ψ`, the integral `∫₀ᵗ cos ((t - s)D) G(s) ds` splits as
`⟪cos (tD) φ, ∫₀ᵗ cos (sD) G⟫ - ⟪D⁻¹ sin (tD) ψ, ∫₀ᵗ D⁻¹ sin (sD) G⟫`. -/
private theorem inner_integral_waveCosPropagator_sub_apply
    (hφψ : Δ (φ : 𝓢'(E, F)) = (ψ : 𝓢'(E, F))) (hG : Continuous G) (t : ℝ) :
    ⟪φ, ∫ s in (0 : ℝ)..t, waveCosPropagator F (t - s) (G s)⟫ =
      ⟪waveCosPropagator F t φ, duhamelCos G t⟫ -
        ⟪waveSinPropagator F t ψ, duhamelSin G t⟫ := by
  have hc₁ : Continuous fun s ↦ waveCosPropagator F s (G s) := hG.waveCosPropagator_apply
  have hc₂ : Continuous fun s ↦ waveSinPropagator F s (G s) := hG.waveSinPropagator_apply
  have hc₃ : Continuous fun s ↦ waveCosPropagator F (t - s) (G s) := by
    have := (hG.comp (continuous_sub_left t)).waveCosPropagator_apply.comp (continuous_sub_left t)
    simpa [Function.comp_def] using this
  have hinner (y : Lp F 2 (volume : Measure E)) {h : ℝ → Lp F 2 (volume : Measure E)}
      (hh : Continuous h) : ⟪y, ∫ s in (0 : ℝ)..t, h s⟫ = ∫ s in (0 : ℝ)..t, ⟪y, h s⟫ :=
    ((innerSL ℂ y).intervalIntegral_comp_comm (hh.intervalIntegrable 0 t)).symm
  rw [duhamelCos, duhamelSin, hinner _ hc₃, hinner _ hc₁, hinner _ hc₂,
    ← intervalIntegral.integral_sub ((continuous_const.inner hc₁).intervalIntegrable 0 t)
      ((continuous_const.inner hc₂).intervalIntegrable 0 t)]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  rw [← inner_waveCosPropagator_apply, waveCosPropagator_sub_apply hφψ, inner_sub_left,
    inner_waveCosPropagator_apply, inner_waveSinPropagator_apply]

/-- **The weak velocity of the solution of the wave equation.** For a test function `φ ∈ L²` with
`Δφ = ψ ∈ L²`, the pairing `t ↦ ⟪φ, u(t)⟫` of the solution
`u(t) = cos (tD) f + D⁻¹ sin (tD) g + ∫₀ᵗ D⁻¹ sin ((t - s)D) G(s) ds` is differentiable, with
derivative `⟪ψ, D⁻¹ sin (tD) f⟫ + ⟪φ, cos (tD) g + ∫₀ᵗ cos ((t - s)D) G(s) ds⟫`, the pairing of
`φ` with the velocity `∂ₜu = D⁻¹ sin (tD) Δf + cos (tD) g + ∫₀ᵗ cos ((t - s)D) G(s) ds`. -/
theorem hasDerivAt_inner_waveDuhamelSolution (hφψ : Δ (φ : 𝓢'(E, F)) = (ψ : 𝓢'(E, F)))
    (f g : Lp F 2 (volume : Measure E)) (hG : Continuous G) (t : ℝ) :
    HasDerivAt (fun t ↦ ⟪φ, waveDuhamelSolution F f g G t⟫)
      (⟪ψ, waveSinPropagator F t f⟫ +
        ⟪φ, waveCosPropagator F t g + ∫ s in (0 : ℝ)..t, waveCosPropagator F (t - s) (G s)⟫)
      t := by
  -- Move the propagators onto `φ`, so that only `φ` and `ψ` are differentiated in time.
  have hfun : (fun t ↦ ⟪φ, waveDuhamelSolution F f g G t⟫) = fun t ↦
      ⟪waveCosPropagator F t φ, f⟫ + ⟪φ, waveSinPropagator F t g⟫ +
        (⟪waveSinPropagator F t φ, duhamelCos G t⟫ -
          ⟪waveCosPropagator F t φ, duhamelSin G t⟫) := by
    ext t
    rw [waveDuhamelSolution_def, integral_waveSinPropagator_sub_apply hG]
    simp only [inner_add_right, inner_sub_right, inner_waveSinPropagator_apply,
      inner_waveCosPropagator_apply]
  rw [hfun, inner_add_right, inner_integral_waveCosPropagator_sub_apply hφψ hG]
  have h₁ := (hasDerivAt_waveCosPropagator_apply hφψ t).inner ℂ (hasDerivAt_const t f)
  have h₂ := (hasDerivAt_const t φ).inner ℂ (hasDerivAt_waveSinPropagator_apply g t)
  have h₃ := (hasDerivAt_waveSinPropagator_apply φ t).inner ℂ (hasDerivAt_duhamelCos hG t)
  have h₄ := (hasDerivAt_waveCosPropagator_apply hφψ t).inner ℂ (hasDerivAt_duhamelSin hG t)
  convert (h₁.add h₂).add (h₃.sub h₄) using 1
  simp only [inner_zero_left, inner_zero_right, inner_waveSinPropagator_apply,
    inner_waveCosPropagator_apply, waveSinPropagator_apply_waveCosPropagator_apply]
  ring

/-- The weak velocity of `hasDerivAt_inner_waveDuhamelSolution` has derivative
`⟪ψ, u(t)⟫ + ⟪φ, G(t)⟫`. -/
private theorem hasDerivAt_inner_waveDuhamelVelocity
    (hφψ : Δ (φ : 𝓢'(E, F)) = (ψ : 𝓢'(E, F))) (f g : Lp F 2 (volume : Measure E))
    (hG : Continuous G) (t : ℝ) :
    HasDerivAt (fun t ↦ ⟪ψ, waveSinPropagator F t f⟫ +
        ⟪φ, waveCosPropagator F t g + ∫ s in (0 : ℝ)..t, waveCosPropagator F (t - s) (G s)⟫)
      (⟪ψ, waveDuhamelSolution F f g G t⟫ + ⟪φ, G t⟫) t := by
  have hfun : (fun t ↦ ⟪ψ, waveSinPropagator F t f⟫ +
      ⟪φ, waveCosPropagator F t g + ∫ s in (0 : ℝ)..t, waveCosPropagator F (t - s) (G s)⟫) =
      fun t ↦ ⟪ψ, waveSinPropagator F t f⟫ + ⟪waveCosPropagator F t φ, g⟫ +
        (⟪waveCosPropagator F t φ, duhamelCos G t⟫ -
          ⟪waveSinPropagator F t ψ, duhamelSin G t⟫) := by
    ext t
    rw [inner_add_right, inner_integral_waveCosPropagator_sub_apply hφψ hG,
      ← inner_waveCosPropagator_apply, add_assoc]
  -- `cos² (tD) + sin² (tD) = 1`, against `φ`.
  have hφ : ⟪φ, G t⟫ = ⟪φ, waveCosPropagator F t (waveCosPropagator F t (G t))⟫ -
      ⟪ψ, waveSinPropagator F t (waveSinPropagator F t (G t))⟫ := by
    conv_lhs => rw [show φ = waveCosPropagator F (t - t) φ by simp,
      waveCosPropagator_sub_apply hφψ]
    simp only [inner_sub_left, inner_waveCosPropagator_apply, inner_waveSinPropagator_apply]
  rw [hfun, waveDuhamelSolution_def, integral_waveSinPropagator_sub_apply hG]
  have h₁ := (hasDerivAt_const t ψ).inner ℂ (hasDerivAt_waveSinPropagator_apply f t)
  have h₂ := (hasDerivAt_waveCosPropagator_apply hφψ t).inner ℂ (hasDerivAt_const t g)
  have h₃ := (hasDerivAt_waveCosPropagator_apply hφψ t).inner ℂ (hasDerivAt_duhamelCos hG t)
  have h₄ := (hasDerivAt_waveSinPropagator_apply ψ t).inner ℂ (hasDerivAt_duhamelSin hG t)
  convert (h₁.add h₂).add (h₃.sub h₄) using 1
  simp only [inner_add_right, inner_sub_right, inner_zero_left, inner_zero_right,
    inner_waveSinPropagator_apply, inner_waveCosPropagator_apply]
  linear_combination hφ

/-- **The weak wave equation.** For a test function `φ ∈ L²` with `Δφ = ψ ∈ L²`, the derivative
of `t ↦ ⟪φ, u(t)⟫` is itself differentiable, with derivative `⟪ψ, u(t)⟫ + ⟪φ, G(t)⟫`: the solution
satisfies `∂ₜ²u = Δu + G` against `φ`. -/
theorem hasDerivAt_deriv_inner_waveDuhamelSolution (hφψ : Δ (φ : 𝓢'(E, F)) = (ψ : 𝓢'(E, F)))
    (f g : Lp F 2 (volume : Measure E)) (hG : Continuous G) (t : ℝ) :
    HasDerivAt (deriv fun t ↦ ⟪φ, waveDuhamelSolution F f g G t⟫)
      (⟪ψ, waveDuhamelSolution F f g G t⟫ + ⟪φ, G t⟫) t := by
  rw [funext fun t ↦ (hasDerivAt_inner_waveDuhamelSolution hφψ f g hG t).deriv]
  exact hasDerivAt_inner_waveDuhamelVelocity hφψ f g hG t

/-- **The weak initial velocity.** The pairing `t ↦ ⟪φ, u(t)⟫` has derivative `⟪φ, g⟫` at
`t = 0`. -/
theorem hasDerivAt_inner_waveDuhamelSolution_zero (hφψ : Δ (φ : 𝓢'(E, F)) = (ψ : 𝓢'(E, F)))
    (f g : Lp F 2 (volume : Measure E)) (hG : Continuous G) :
    HasDerivAt (fun t ↦ ⟪φ, waveDuhamelSolution F f g G t⟫) ⟪φ, g⟫ 0 := by
  simpa using hasDerivAt_inner_waveDuhamelSolution hφψ f g hG 0

/-- **The wave equation in the sense of distributions.** For every Schwartz function `φ`, the
derivative of `t ↦ ⟪φ, u(t)⟫` has derivative `⟪Δφ, u(t)⟫ + ⟪φ, G(t)⟫`. -/
theorem hasDerivAt_deriv_inner_toLp_waveDuhamelSolution (φ : 𝓢(E, F))
    (f g : Lp F 2 (volume : Measure E)) (hG : Continuous G) (t : ℝ) :
    HasDerivAt (deriv fun t ↦ ⟪φ.toLp 2, waveDuhamelSolution F f g G t⟫)
      (⟪(Δ φ).toLp 2, waveDuhamelSolution F f g G t⟫ + ⟪φ.toLp 2, G t⟫) t :=
  hasDerivAt_deriv_inner_waveDuhamelSolution (by simp) f g hG t

end Duhamel

end TauCeti
