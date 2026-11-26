/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Wave.Energy
import TauCeti.Analysis.Calculus.Taylor.OrderOne

/-!
# Weak solutions of the forced wave equation on `L²`

On a finite-dimensional real inner product space `E`, let `D = √(-Δ)` be the Fourier multiplier
with symbol `TauCeti.sqrtNegLaplacianSymbol`, `ξ ↦ 2π ‖ξ‖`. The Cauchy problem for the wave
equation

`∂ₜ²u - Δu = G`, `u(0) = f`, `∂ₜu(0) = g`

is solved by Duhamel's formula

`u(t) = cos (tD) f + D⁻¹ sin (tD) g + ∫₀ᵗ D⁻¹ sin ((t - s)D) G(s) ds`

in terms of the propagators `cos (tD)` (`TauCeti.waveCosPropagator`) and `D⁻¹ sin (tD)`
(`TauCeti.waveSinPropagator`). A strong solution on an order-connected set of times containing
`0` and `t`, whose forcing is integrable between `0` and `t`, is given at time `t` by this formula
(`TauCeti.IsWaveSolutionOn.eq_waveCosPropagator_add_waveSinPropagator_add_integral`), that is by
`TauCeti.waveDuhamelSolution` with the data `u(0)` and `∂ₜu(0)`
(`TauCeti.IsWaveSolutionOn.eq_waveDuhamelSolution`). Conversely,
this file shows that the formula `TauCeti.waveDuhamelSolution f g G` solves the forced problem
for all data `f, g ∈ L²` and every continuous forcing `G : ℝ → L²`, in the weak sense.

The solution starts from `f` (`TauCeti.waveDuhamelSolution_zero`). At time `t` it is
homogeneous in the data and the forcing (`TauCeti.waveDuhamelSolution_smul`), and additive in the
data and in forcings integrable between `0` and `t` (`TauCeti.waveDuhamelSolution_add`); so it is
linear on pairs of data `f, g ∈ L²` and continuous forcings. For forcing integrable between `0`
and `t` it is bounded by `‖u(t)‖ ≤ ‖f‖ + |t| ‖g‖ + |∫₀ᵗ |t - s| ‖G(s)‖ ds|`
(`TauCeti.norm_waveDuhamelSolution_le`), and for `0 ≤ t ≤ T` its Duhamel term is the retarded
integral `∫_{s < t} D⁻¹ sin ((t - s)D) G(s) ds` of the forcing restricted to `[0, T]`
(`TauCeti.waveDuhamelSolution_eq_setIntegral_Iio`), the form treated by the retarded Strichartz
estimates. For continuous forcing it is continuous in time
(`TauCeti.continuous_waveDuhamelSolution`), and for every `φ ∈ L²` whose distributional
Laplacian `ψ = Δφ` lies in `L²`, the scalar function `t ↦ ⟪φ, u(t)⟫` is twice differentiable,
with

`d/dt ⟪φ, u(t)⟫ = ⟪ψ, D⁻¹ sin (tD) f⟫ + ⟪φ, cos (tD) g + ∫₀ᵗ cos ((t - s)D) G(s) ds⟫`,
`d²/dt² ⟪φ, u(t)⟫ = ⟪ψ, u(t)⟫ + ⟪φ, G(t)⟫`

(`TauCeti.hasDerivAt_inner_waveDuhamelSolution`,
`TauCeti.hasDerivAt_deriv_inner_waveDuhamelSolution`). At `t = 0` the first derivative is
`⟪φ, g⟫`, so `u` takes the initial velocity `g` weakly
(`TauCeti.hasDerivAt_inner_waveDuhamelSolution_zero`). Every Schwartz function `φ` is admissible,
with `ψ = Δφ`, so `u` solves the wave equation in the sense of distributions in space
(`TauCeti.hasDerivAt_deriv_inner_toLp_waveDuhamelSolution`).

Integrating twice in time, Taylor's formula of order one gives the **weak formulation**: for all
such `φ, ψ` and every time `t`,

`⟪φ, u(t)⟫ = ⟪φ, f⟫ + t ⟪φ, g⟫ + ∫₀ᵗ (t - s) (⟪ψ, u(s)⟫ + ⟪φ, G(s)⟫) ds`

(`TauCeti.inner_waveDuhamelSolution`, and `TauCeti.inner_toLp_waveDuhamelSolution` for Schwartz
`φ`), which makes sense for every `u` continuous in time with values in `L²`.

By the subtraction formula `TauCeti.waveSinPropagator_sub`, for continuous forcing `G` the
retarded term is

`∫₀ᵗ D⁻¹ sin ((t - s)D) G(s) ds =`
`D⁻¹ sin (tD) ∫₀ᵗ cos (sD) G(s) ds - cos (tD) ∫₀ᵗ D⁻¹ sin (sD) G(s) ds`.

The propagators are self-adjoint (`TauCeti.isSelfAdjoint_waveCosPropagator`,
`TauCeti.isSelfAdjoint_waveSinPropagator`), so they can be moved onto the test function `φ`. There
they are differentiated by `TauCeti.hasDerivAt_waveSinPropagator_apply`,
`∂ₜ (D⁻¹ sin (tD) φ) = cos (tD) φ` for every `φ ∈ L²`, and by
`TauCeti.hasDerivAt_waveCosPropagator_apply`, `∂ₜ (cos (tD) φ) = D⁻¹ sin (tD) ψ` when
`Δφ = ψ ∈ L²`.

## Main declarations

* `TauCeti.waveDuhamelSolution`: the solution formula, with
  `TauCeti.continuous_waveDuhamelSolution`, `TauCeti.waveDuhamelSolution_add`,
  `TauCeti.waveDuhamelSolution_smul` and `TauCeti.waveDuhamelSolution_eq_setIntegral_Iio`;
* `TauCeti.hasDerivAt_inner_waveDuhamelSolution`,
  `TauCeti.hasDerivAt_deriv_inner_waveDuhamelSolution`: the weak wave equation.
* `TauCeti.inner_waveDuhamelSolution`, `TauCeti.inner_toLp_waveDuhamelSolution`: Duhamel's formula
  satisfies the weak formulation, integrated twice in time.

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ### The solution formula -/

variable (F) in
/-- **Duhamel's formula** `u(t) = cos (tD) f + D⁻¹ sin (tD) g + ∫₀ᵗ D⁻¹ sin ((t - s)D) G(s) ds`
on `L²`, for data `f, g` and forcing `G`. The formula is defined for every `G`, the Bochner
integral being `0` where it does not exist. For continuous `G` it is a weak solution of the
Cauchy problem `∂ₜ²u - Δu = G`, `u(0) = f`, `∂ₜu(0) = g`
(`TauCeti.hasDerivAt_deriv_inner_waveDuhamelSolution`,
`TauCeti.hasDerivAt_inner_waveDuhamelSolution_zero`). -/
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

/-- Without forcing, the solution is the free solution `cos (tD) f + D⁻¹ sin (tD) g`. -/
@[simp]
theorem waveDuhamelSolution_zero_forcing (f g : Lp F 2 (volume : Measure E)) (t : ℝ) :
    waveDuhamelSolution F f g 0 t = waveCosPropagator F t f + waveSinPropagator F t g := by
  simp [waveDuhamelSolution_def]

/-- With zero data and zero forcing, the solution vanishes at all times. -/
@[simp]
theorem waveDuhamelSolution_zero_zero_zero :
    waveDuhamelSolution F (0 : Lp F 2 (volume : Measure E)) 0 0 = 0 :=
  funext fun t ↦ by simp

/-- The solution is homogeneous in the data and the forcing. -/
theorem waveDuhamelSolution_smul (c : ℂ) (f g : Lp F 2 (volume : Measure E))
    (G : ℝ → Lp F 2 (volume : Measure E)) (t : ℝ) :
    waveDuhamelSolution F (c • f) (c • g) (c • G) t = c • waveDuhamelSolution F f g G t := by
  simp only [waveDuhamelSolution_def, map_smul, Pi.smul_apply, intervalIntegral.integral_smul,
    smul_add]

/-- **Superposition**: for forcings integrable between `0` and `t`, the solution at time `t` is
additive in the data and the forcing. -/
theorem waveDuhamelSolution_add (f₁ f₂ g₁ g₂ : Lp F 2 (volume : Measure E))
    {G₁ G₂ : ℝ → Lp F 2 (volume : Measure E)} {t : ℝ} (hG₁ : IntervalIntegrable G₁ volume 0 t)
    (hG₂ : IntervalIntegrable G₂ volume 0 t) :
    waveDuhamelSolution F (f₁ + f₂) (g₁ + g₂) (G₁ + G₂) t =
      waveDuhamelSolution F f₁ g₁ G₁ t + waveDuhamelSolution F f₂ g₂ G₂ t := by
  simp only [waveDuhamelSolution_def, map_add, Pi.add_apply,
    intervalIntegral.integral_add hG₁.waveSinPropagator_sub_apply hG₂.waveSinPropagator_sub_apply]
  abel

/-- The **a priori bound** `‖u(t)‖ ≤ ‖f‖ + |t| ‖g‖ + |∫₀ᵗ |t - s| ‖G(s)‖ ds|`, for forcing `G`
integrable between `0` and `t`. -/
theorem norm_waveDuhamelSolution_le (f g : Lp F 2 (volume : Measure E))
    {G : ℝ → Lp F 2 (volume : Measure E)} {t : ℝ} (hG : IntervalIntegrable G volume 0 t) :
    ‖waveDuhamelSolution F f g G t‖ ≤
      ‖f‖ + |t| * ‖g‖ + |∫ s in (0 : ℝ)..t, |t - s| * ‖G s‖| := by
  refine (norm_add₃_le).trans (add_le_add (add_le_add ?_ ?_) ?_)
  · exact ((waveCosPropagator F t).le_opNorm f).trans
      (mul_le_of_le_one_left (norm_nonneg f) (norm_waveCosPropagator_le t))
  · exact ((waveSinPropagator F t).le_opNorm g).trans
      (by gcongr; exact norm_waveSinPropagator_le t)
  · refine intervalIntegral.norm_integral_le_abs_of_norm_le (Eventually.of_forall fun s ↦ ?_)
      (hG.norm.continuousOn_mul (by fun_prop : Continuous fun s ↦ |t - s|).continuousOn)
    exact ((waveSinPropagator F (t - s)).le_opNorm _).trans
      (by gcongr; exact norm_waveSinPropagator_le _)

/-- For `0 ≤ t ≤ T`, the Duhamel term of the solution at time `t` is the retarded integral
`∫_{s < t} D⁻¹ sin ((t - s)D) G(s) ds` of the forcing restricted to `[0, T]` and extended by zero,
the form treated by the retarded Strichartz estimates
(`ContDiffBump.exists_eLpNorm_eLpNorm_setIntegral_Iio_waveSinPropagator_sub_le_tsum`). -/
theorem waveDuhamelSolution_eq_setIntegral_Iio (f g : Lp F 2 (volume : Measure E))
    (G : ℝ → Lp F 2 (volume : Measure E)) {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    waveDuhamelSolution F f g G t = waveCosPropagator F t f + waveSinPropagator F t g +
      ∫ s in Set.Iio t, waveSinPropagator F (t - s) ((Set.Icc 0 T).indicator G s) := by
  have hind : (fun s ↦ waveSinPropagator F (t - s) ((Set.Icc 0 T).indicator G s)) =
      (Set.Icc 0 T).indicator fun s ↦ waveSinPropagator F (t - s) (G s) :=
    funext fun s ↦ by by_cases hs : s ∈ Set.Icc 0 T <;> simp [hs]
  have hset : Set.Iio t ∩ Set.Icc 0 T = Set.Ico 0 t :=
    Set.ext fun s ↦ ⟨fun ⟨h₁, h₂, _⟩ ↦ ⟨h₂, h₁⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₂, h₁, h₂.le.trans htT⟩⟩
  rw [waveDuhamelSolution_def, hind, setIntegral_indicator measurableSet_Icc, hset,
    integral_Ico_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le ht]

/-- A strong solution of `∂ₜ²u - Δu = G` on an order-connected set of times `s` containing `0` and
`t`, with `G` integrable between `0` and `t`, is given at time `t` by Duhamel's formula with the
data `u(0)` and `u'(0)`. -/
theorem IsWaveSolutionOn.eq_waveDuhamelSolution {u u' u'' G : ℝ → Lp F 2 (volume : Measure E)}
    {s : Set ℝ} [s.OrdConnected] (hu : IsWaveSolutionOn u u' u'' G s) {t : ℝ} (h0 : 0 ∈ s)
    (ht : t ∈ s) (hG : IntervalIntegrable G volume 0 t) :
    u t = waveDuhamelSolution F (u 0) (u' 0) G t := by
  rw [hu.eq_waveCosPropagator_add_waveSinPropagator_add_integral h0 ht hG, sub_zero,
    waveDuhamelSolution_def]

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

/-- For continuous forcing `G`, the Duhamel term splits as
`D⁻¹ sin (tD) ∫₀ᵗ cos (sD) G - cos (tD) ∫₀ᵗ D⁻¹ sin (sD) G`. -/
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

/-- For continuous forcing, the solution is continuous in time with values in `L²`. -/
theorem continuous_waveDuhamelSolution (f g : Lp F 2 (volume : Measure E)) (hG : Continuous G) :
    Continuous (waveDuhamelSolution F f g G) :=
  ((continuous_waveCosPropagator_apply f).add (continuous_waveSinPropagator_apply g)).add
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (a₀ := 0)
      (f := fun t s ↦ waveSinPropagator F (t - s) (G s)) (continuous_waveSinPropagator_uncurry.comp
        ((continuous_fst.sub continuous_snd).prodMk (hG.comp continuous_snd))) continuous_id)

variable {φ ψ : Lp F 2 (volume : Measure E)}

/-- Against a test function `φ` with `Δφ = ψ`, for continuous forcing `G`, the integral
`∫₀ᵗ cos ((t - s)D) G(s) ds` splits as
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
`Δφ = ψ ∈ L²` and continuous forcing `G`, the pairing `t ↦ ⟪φ, u(t)⟫` of the solution
`u(t) = cos (tD) f + D⁻¹ sin (tD) g + ∫₀ᵗ D⁻¹ sin ((t - s)D) G(s) ds` is differentiable, with
derivative `⟪ψ, D⁻¹ sin (tD) f⟫ + ⟪φ, cos (tD) g + ∫₀ᵗ cos ((t - s)D) G(s) ds⟫`. Formally this
pairs `φ` with the velocity `D⁻¹ sin (tD) Δf + cos (tD) g + ∫₀ᵗ cos ((t - s)D) G(s) ds`; as `Δf`
need not lie in `L²`, its first term is not an application of the `L²` operator
`TauCeti.waveSinPropagator`, and is interpreted by moving the Laplacian onto the test function. -/
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
  have hcomm (x : Lp F 2 (volume : Measure E)) :
      waveSinPropagator F t (waveCosPropagator F t x) =
        waveCosPropagator F t (waveSinPropagator F t x) := by
    rw [waveSinPropagator_def]
    exact fourierMultiplierCLM_waveCosPropagator_apply t _ x
  convert (h₁.add h₂).add (h₃.sub h₄) using 1
  simp only [inner_zero_left, inner_zero_right, inner_waveSinPropagator_apply,
    inner_waveCosPropagator_apply, hcomm]
  ring

/-- For continuous forcing `G`, the weak velocity of `hasDerivAt_inner_waveDuhamelSolution` has
derivative `⟪ψ, u(t)⟫ + ⟪φ, G(t)⟫`. -/
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

/-- **The weak wave equation.** For a test function `φ ∈ L²` with `Δφ = ψ ∈ L²` and continuous
forcing `G`, the derivative of `t ↦ ⟪φ, u(t)⟫` is itself differentiable, with derivative
`⟪ψ, u(t)⟫ + ⟪φ, G(t)⟫`: the solution satisfies `∂ₜ²u = Δu + G` against `φ`. -/
theorem hasDerivAt_deriv_inner_waveDuhamelSolution (hφψ : Δ (φ : 𝓢'(E, F)) = (ψ : 𝓢'(E, F)))
    (f g : Lp F 2 (volume : Measure E)) (hG : Continuous G) (t : ℝ) :
    HasDerivAt (deriv fun t ↦ ⟪φ, waveDuhamelSolution F f g G t⟫)
      (⟪ψ, waveDuhamelSolution F f g G t⟫ + ⟪φ, G t⟫) t := by
  rw [funext fun t ↦ (hasDerivAt_inner_waveDuhamelSolution hφψ f g hG t).deriv]
  exact hasDerivAt_inner_waveDuhamelVelocity hφψ f g hG t

/-- **The weak initial velocity.** For a test function `φ ∈ L²` with `Δφ = ψ ∈ L²` and continuous
forcing `G`, the pairing `t ↦ ⟪φ, u(t)⟫` has derivative `⟪φ, g⟫` at `t = 0`. -/
theorem hasDerivAt_inner_waveDuhamelSolution_zero (hφψ : Δ (φ : 𝓢'(E, F)) = (ψ : 𝓢'(E, F)))
    (f g : Lp F 2 (volume : Measure E)) (hG : Continuous G) :
    HasDerivAt (fun t ↦ ⟪φ, waveDuhamelSolution F f g G t⟫) ⟪φ, g⟫ 0 := by
  simpa using hasDerivAt_inner_waveDuhamelSolution hφψ f g hG 0

/-- **The wave equation in the sense of distributions.** For every Schwartz function `φ` and
continuous forcing `G`, the derivative of `t ↦ ⟪φ, u(t)⟫` has derivative
`⟪Δφ, u(t)⟫ + ⟪φ, G(t)⟫`. -/
theorem hasDerivAt_deriv_inner_toLp_waveDuhamelSolution (φ : 𝓢(E, F))
    (f g : Lp F 2 (volume : Measure E)) (hG : Continuous G) (t : ℝ) :
    HasDerivAt (deriv fun t ↦ ⟪φ.toLp 2, waveDuhamelSolution F f g G t⟫)
      (⟪(Δ φ).toLp 2, waveDuhamelSolution F f g G t⟫ + ⟪φ.toLp 2, G t⟫) t :=
  hasDerivAt_deriv_inner_waveDuhamelSolution (by simp) f g hG t

/-- **Duhamel's formula is a weak solution** of the wave equation `∂ₜ²u - Δu = G`, `u(0) = f`,
`∂ₜu(0) = g`, for continuous forcing `G`: for all `φ, ψ ∈ L²` with `Δφ = ψ` and every time `t`,

`⟪φ, u t⟫ = ⟪φ, f⟫ + t ⟪φ, g⟫ + ∫₀ᵗ (t - r) (⟪ψ, u r⟫ + ⟪φ, G r⟫) dr`. -/
theorem inner_waveDuhamelSolution (hφψ : Δ (φ : 𝓢'(E, F)) = (ψ : 𝓢'(E, F)))
    (f g : Lp F 2 (volume : Measure E)) (hG : Continuous G) (t : ℝ) :
    ⟪φ, waveDuhamelSolution F f g G t⟫ = ⟪φ, f⟫ + t • ⟪φ, g⟫ +
      ∫ r in (0 : ℝ)..t, (t - r) • (⟪ψ, waveDuhamelSolution F f g G r⟫ + ⟪φ, G r⟫) := by
  have hc : Continuous fun r ↦ ⟪ψ, waveDuhamelSolution F f g G r⟫ + ⟪φ, G r⟫ :=
    (continuous_const.inner (continuous_waveDuhamelSolution f g hG)).add
      (continuous_const.inner hG)
  rw [intervalIntegral.eq_add_sub_smul_add_integral_sub_smul
    (fun τ _ ↦ (hasDerivAt_inner_waveDuhamelSolution hφψ f g hG τ).differentiableAt.hasDerivAt)
    (fun τ _ ↦ hasDerivAt_deriv_inner_waveDuhamelSolution hφψ f g hG τ) hc.continuousOn,
    (hasDerivAt_inner_waveDuhamelSolution_zero hφψ f g hG).deriv, waveDuhamelSolution_zero,
    sub_zero]

/-- **The wave equation in the sense of distributions, integrated in time.** Duhamel's formula
satisfies the weak formulation against every Schwartz function `φ`:
`⟪φ, u t⟫ = ⟪φ, f⟫ + t ⟪φ, g⟫ + ∫₀ᵗ (t - r) (⟪Δφ, u r⟫ + ⟪φ, G r⟫) dr`. -/
theorem inner_toLp_waveDuhamelSolution (φ : 𝓢(E, F)) (f g : Lp F 2 (volume : Measure E))
    (hG : Continuous G) (t : ℝ) :
    ⟪φ.toLp 2, waveDuhamelSolution F f g G t⟫ = ⟪φ.toLp 2, f⟫ + t • ⟪φ.toLp 2, g⟫ +
      ∫ r in (0 : ℝ)..t,
        (t - r) • (⟪(Δ φ).toLp 2, waveDuhamelSolution F f g G r⟫ + ⟪φ.toLp 2, G r⟫) :=
  inner_waveDuhamelSolution (by simp) f g hG t

end Duhamel

end TauCeti
