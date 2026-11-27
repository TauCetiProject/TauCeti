/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Wave.Energy
import TauCeti.Analysis.Calculus.Taylor.OrderOne
import TauCeti.MeasureTheory.Function.Holder
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Duality

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
(`TauCeti.hasDerivAt_deriv_inner_toLp_waveDuhamelSolution`). Integrating by parts twice in time,
`∫ θ''(t) ⟪φ, u(t)⟫ dt = ∫ θ(t) (⟪ψ, u(t)⟫ + ⟪φ, G(t)⟫) dt` for every compactly supported `C²`
function `θ` (`TauCeti.integral_deriv_deriv_mul_inner_waveDuhamelSolution`), which is the equation
tested against `θ(t) φ(x)`.

This tested form passes to limits that need not lie in `L²`. If free waves `uᵢ` with data in `L²`
converge to `U : ℝ → L^r` in `L^r` at almost every time and in the mixed norm `L^q_t L^r_x`,
`1 ≤ q`, then `∫ θ''(t) ∫ ⟪φ, U(t)⟫ dx dt = ∫ θ(t) ∫ ⟪Δφ, U(t)⟫ dx dt` for every Schwartz `φ`
(`TauCeti.integral_deriv_deriv_mul_integral_inner_eq_of_tendsto_waveDuhamelSolution`), by Hölder's
inequality in space and in time
(`TauCeti.tendsto_integral_mul_integral_inner_of_tendsto_eLpNorm_eLpNorm_sub`). This identifies
the evolutions of data in homogeneous Besov spaces, defined as such limits, as solutions of the
wave equation.

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

The retarded Duhamel integral `u(t) = ∫_{s < t} D⁻¹ sin ((t - s)D) G(s) ds`, the solution with zero
data at `t = -∞`, solves the forced equation for forcing `G` that is only integrable, not
continuous, provided `s ↦ D⁻¹ sin (sD) G(s)` is integrable too:
`∫ θ''(t) ⟪φ, u(t)⟫ dt = ∫ θ(t) (⟪ψ, u(t)⟫ + ⟪φ, G(t)⟫) dt`
(`TauCeti.integral_deriv_deriv_mul_inner_setIntegral_Iio_waveSinPropagator_sub`). Here Fubini's
theorem reduces the claim to integrations by parts against the free waves
`t ↦ D⁻¹ sin ((t - s)D) G(s)` started at each time `s`, which vanish at `t = s` with velocity
`G(s)`.
The second hypothesis is needed because `‖D⁻¹ sin (sD)‖` grows like `|s|`; it holds for forcing
terms frequency-localized away from the origin. Both sides of this identity pass to limits in a
mixed norm `L^q_t L^r_x` (`TauCeti.tendsto_integral_mul_inner_of_tendsto_eLpNorm_eLpNorm_sub`),
so a limit of sums `∑ⱼ uⱼ` of retarded integrals solves `∂ₜ²U - ΔU = ∑ⱼ Gⱼ` in the sense of
distributions
(`TauCeti.hasSum_integral_mul_integral_inner_of_tendsto_sum_setIntegral_Iio_waveSinPropagator_sub`).

## Main declarations

* `TauCeti.waveDuhamelSolution`: the solution formula, with
  `TauCeti.continuous_waveDuhamelSolution`, `TauCeti.waveDuhamelSolution_add`,
  `TauCeti.waveDuhamelSolution_smul` and `TauCeti.waveDuhamelSolution_eq_setIntegral_Iio`;
* `TauCeti.hasDerivAt_inner_waveDuhamelSolution`,
  `TauCeti.hasDerivAt_deriv_inner_waveDuhamelSolution`: the weak wave equation;
* `TauCeti.integral_deriv_deriv_mul_inner_waveDuhamelSolution`: the wave equation tested against
  `θ(t) φ(x)`;
* `TauCeti.integral_deriv_deriv_mul_integral_inner_eq_of_tendsto_waveDuhamelSolution`: limits of
  free waves in a mixed norm `L^q_t L^r_x` solve the wave equation in the sense of distributions;
* `TauCeti.inner_waveDuhamelSolution`, `TauCeti.inner_toLp_waveDuhamelSolution`: Duhamel's formula
  satisfies the weak formulation, integrated twice in time.
* `TauCeti.integral_deriv_deriv_mul_inner_setIntegral_Iio_waveSinPropagator_sub`: the retarded
  integral of an integrable forcing term solves the forced wave equation, tested against
  `θ(t) φ(x)`;
* `TauCeti.hasSum_integral_mul_integral_inner_of_tendsto_sum_setIntegral_Iio_waveSinPropagator_sub`:
  limits in a mixed norm of sums of retarded integrals solve the wave equation forced by the sum
  of the forcing terms, in the sense of distributions.

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

/-- Every `L²` Fourier multiplier commutes with the solution: for a forcing integrable between `0`
and `t`, applying it to the solution at time `t` gives the solution at time `t` with the multiplier
applied to the data and to the forcing. -/
theorem fourierMultiplierCLM_waveDuhamelSolution (m : Lp ℂ ∞ (volume : Measure E))
    (f g : Lp F 2 (volume : Measure E)) {G : ℝ → Lp F 2 (volume : Measure E)} {t : ℝ}
    (hG : IntervalIntegrable G volume 0 t) :
    Lp.fourierMultiplierCLM F m (waveDuhamelSolution F f g G t) =
      waveDuhamelSolution F (Lp.fourierMultiplierCLM F m f) (Lp.fourierMultiplierCLM F m g)
        (fun s ↦ Lp.fourierMultiplierCLM F m (G s)) t := by
  rw [waveDuhamelSolution_def, waveDuhamelSolution_def, map_add, map_add,
    fourierMultiplierCLM_waveCosPropagator_apply, fourierMultiplierCLM_waveSinPropagator_apply,
    ← ContinuousLinearMap.intervalIntegral_comp_comm _ hG.waveSinPropagator_sub_apply]
  simp_rw [fourierMultiplierCLM_waveSinPropagator_apply]

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

/-- If the forcing `G` is almost everywhere strongly measurable on `[0, T]`, then so is the
solution `t ↦ u(t)` given by Duhamel's formula: on `[0, T]` it is the free solution plus the
retarded integral of the forcing restricted to `[0, T]`. -/
theorem aestronglyMeasurable_waveDuhamelSolution_restrict (f g : Lp F 2 (volume : Measure E))
    {G : ℝ → Lp F 2 (volume : Measure E)} {T : ℝ}
    (hG : AEStronglyMeasurable G (volume.restrict (Set.Icc 0 T))) :
    AEStronglyMeasurable (fun t ↦ waveDuhamelSolution F f g G t)
      (volume.restrict (Set.Icc 0 T)) := by
  have hGi : AEStronglyMeasurable ((Set.Icc 0 T).indicator G) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Icc).2 hG
  refine (((continuous_waveCosPropagator_apply f).add
    (continuous_waveSinPropagator_apply g)).aestronglyMeasurable.add
      (aestronglyMeasurable_setIntegral_Iio_waveSinPropagator_sub hGi)).restrict.congr ?_
  exact ae_restrict_of_forall_mem measurableSet_Icc fun t ht ↦
    (waveDuhamelSolution_eq_setIntegral_Iio f g G ht.1 ht.2).symm

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

/-- **The wave equation tested in space and time.** For a test function `φ ∈ L²` with
`Δφ = ψ ∈ L²`, continuous forcing `G` and a compactly supported `C²` function `θ` of time, the
solution `u(t) = cos (tD) f + D⁻¹ sin (tD) g + ∫₀ᵗ D⁻¹ sin ((t - s)D) G(s) ds` satisfies

`∫ θ''(t) ⟪φ, u(t)⟫ dt = ∫ θ(t) (⟪ψ, u(t)⟫ + ⟪φ, G(t)⟫) dt`,

that is `∂ₜ²u - Δu = G` tested against `θ(t) φ(x)`. -/
theorem integral_deriv_deriv_mul_inner_waveDuhamelSolution
    (hφψ : Δ (φ : 𝓢'(E, F)) = (ψ : 𝓢'(E, F))) (f g : Lp F 2 (volume : Measure E))
    (hG : Continuous G) {θ : ℝ → ℂ} (hθ : ContDiff ℝ 2 θ) (hθc : HasCompactSupport θ) :
    ∫ t, deriv (deriv θ) t * ⟪φ, waveDuhamelSolution F f g G t⟫ =
      ∫ t, θ t * (⟪ψ, waveDuhamelSolution F f g G t⟫ + ⟪φ, G t⟫) := by
  set a : ℝ → ℂ := fun t ↦ ⟪φ, waveDuhamelSolution F f g G t⟫
  have ha (t : ℝ) : HasDerivAt a (deriv a t) t :=
    (hasDerivAt_inner_waveDuhamelSolution hφψ f g hG t).differentiableAt.hasDerivAt
  have ha' (t : ℝ) := hasDerivAt_deriv_inner_waveDuhamelSolution hφψ f g hG t
  have hθ' : ContDiff ℝ 1 (deriv θ) := hθ.deriv' (n := 1)
  have hθ'' (t : ℝ) : HasDerivAt (deriv θ) (deriv (deriv θ) t) t :=
    (hθ'.differentiable one_ne_zero t).hasDerivAt
  have hθ₀ (t : ℝ) : HasDerivAt θ (deriv θ t) t := (hθ.differentiable (by norm_num) t).hasDerivAt
  have hint {v w : ℝ → ℂ} (hv : Continuous v) (hw : Continuous w) (hvc : HasCompactSupport v) :
      Integrable (v * w) := (hv.mul hw).integrable_of_hasCompactSupport hvc.mul_right
  have hca : Continuous a := continuous_iff_continuousAt.2 fun t ↦ (ha t).continuousAt
  have hca' : Continuous (deriv a) := continuous_iff_continuousAt.2 fun t ↦ (ha' t).continuousAt
  have hcb : Continuous fun t ↦ ⟪ψ, waveDuhamelSolution F f g G t⟫ + ⟪φ, G t⟫ :=
    (continuous_const.inner (continuous_waveDuhamelSolution f g hG)).add
      (continuous_const.inner hG)
  -- Integrate by parts twice: `∫ θ'' a = -∫ θ' a' = ∫ θ a''`.
  have h₁ := integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ ↦ hθ'' t) (fun t _ ↦ ha t)
    (hint hθ'.continuous hca' hθc.deriv) (hint (hθ'.continuous_deriv le_rfl) hca hθc.deriv.deriv)
    (hint hθ'.continuous hca hθc.deriv)
  have h₂ := integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ ↦ hθ₀ t) (fun t _ ↦ ha' t)
    (hint hθ.continuous hcb hθc) (hint hθ'.continuous hca' hθc.deriv)
    (hint hθ.continuous hca' hθc)
  rw [h₂, h₁, neg_neg]

open Topology in
/-- **Limits of free waves in mixed norm solve the wave equation.** Let
`uᵢ(t) = cos (tD) fᵢ + D⁻¹ sin (tD) gᵢ` be the free waves with data `fᵢ, gᵢ ∈ L²`, indexed along
a countably generated filter, and let `U : ℝ → L^r` with `uᵢ(t) → U(t)` in `L^r` for almost every
`t` and `uᵢ → U` in the mixed norm `L^q_t L^r_x`, for some `1 ≤ q, r ≤ ∞`. Then `U` solves
`∂ₜ²U = ΔU` in the sense of distributions, tested against `θ(t) φ(x)`: for every Schwartz function
`φ` and every compactly supported `C²` function `θ` of time,

`∫ θ''(t) ∫ ⟪φ(x), U(t)(x)⟫ dx dt = ∫ θ(t) ∫ ⟪Δφ(x), U(t)(x)⟫ dx dt`.

Neither `U(t)` nor any limit of the data needs to lie in `L²`. -/
theorem integral_deriv_deriv_mul_integral_inner_eq_of_tendsto_waveDuhamelSolution {ι : Type*}
    {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated] {q r : ℝ≥0∞} [Fact (1 ≤ r)] (hq : 1 ≤ q)
    {f g : ι → Lp F 2 (volume : Measure E)} {U : ℝ → Lp F r (volume : Measure E)}
    (hae : ∀ᵐ t, Tendsto (fun i ↦
      eLpNorm (⇑(U t) - ⇑(waveDuhamelSolution F (f i) (g i) 0 t)) r volume) l (𝓝 0))
    (hlim : Tendsto (fun i ↦ eLpNorm (fun t ↦
      eLpNorm (⇑(U t) - ⇑(waveDuhamelSolution F (f i) (g i) 0 t)) r volume) q volume) l (𝓝 0))
    (φ : 𝓢(E, F)) {θ : ℝ → ℂ} (hθ : ContDiff ℝ 2 θ) (hθc : HasCompactSupport θ) :
    ∫ t, deriv (deriv θ) t * ∫ x, ⟪φ x, U t x⟫ = ∫ t, θ t * ∫ x, ⟪(Δ φ) x, U t x⟫ := by
  -- Against `ϑ(t) χ(x)`, the pairings of the free waves converge to those of `U`.
  have hconv (χ : 𝓢(E, F)) {ϑ : ℝ → ℂ} (hϑ : Continuous ϑ) (hϑc : HasCompactSupport ϑ) :
      Tendsto (fun i ↦ ∫ t, ϑ t * ⟪χ.toLp 2, waveDuhamelSolution F (f i) (g i) 0 t⟫) l
        (𝓝 (∫ t, ϑ t * ∫ x, ⟪χ x, U t x⟫)) := by
    have hcont (i : ι) : Continuous (waveDuhamelSolution F (f i) (g i) 0) :=
      continuous_waveDuhamelSolution (f i) (g i) continuous_zero
    exact tendsto_integral_mul_inner_of_tendsto_eLpNorm_eLpNorm_sub hq hae hlim (χ.coeFn_toLp 2)
      (χ.memLp _) (hϑ.memLp_of_hasCompactSupport hϑc) (fun i ↦ (hcont i).aestronglyMeasurable)
      fun i ↦
        (hϑ.mul (continuous_const.inner (hcont i))).integrable_of_hasCompactSupport hϑc.mul_right
  have hφ : Δ ((φ.toLp 2 : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) =
      (((Δ φ).toLp 2 : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) := by
    simp
  have heq (i : ι) := integral_deriv_deriv_mul_inner_waveDuhamelSolution hφ (f i) (g i)
    continuous_zero hθ hθc
  simp only [Pi.zero_apply, inner_zero_right, add_zero] at heq
  have hθ' : ContDiff ℝ 1 (deriv θ) := hθ.deriv' (n := 1)
  exact tendsto_nhds_unique ((hconv φ (hθ'.continuous_deriv le_rfl) hθc.deriv.deriv).congr heq)
    (hconv (Δ φ) hθ.continuous hθc)

/-! ### The retarded integral

The retarded Duhamel integral `u(t) = ∫_{s < t} D⁻¹ sin ((t - s)D) G(s) ds` solves the forced
wave equation with zero data at `t = -∞`. For integrable `G` it need not exist, since
`‖D⁻¹ sin (sD)‖` grows like `|s|`; it does when `s ↦ D⁻¹ sin (sD) G(s)` is integrable too, as for
forcing terms frequency-localized away from the origin. Tested against `θ(t) φ(x)`, the equation
follows by Fubini's theorem from the integration by parts against the free wave started at each
time `s`. -/

/-- **Fubini for the retarded pairing.** For `ϑ` continuous with compact support and `χ ∈ L²`, the
pairing `∫ ϑ(t) ⟪χ, u(t)⟫ dt` of the retarded integral `u(t) = ∫_{s < t} D⁻¹ sin ((t - s)D) G(s) ds`
is integrable in `t` and equals `∫ ∫_{t > s} ϑ(t) ⟪χ, D⁻¹ sin ((t - s)D) G(s)⟫ dt ds`, whose inner
integral is integrable in `s`. -/
private theorem integral_mul_inner_setIntegral_Iio_waveSinPropagator_sub (hG : Integrable G)
    (hSG : Integrable fun s ↦ waveSinPropagator F s (G s)) {ϑ : ℝ → ℂ} (hϑ : Continuous ϑ)
    (hϑc : HasCompactSupport ϑ) (χ : Lp F 2 (volume : Measure E)) :
    Integrable (fun t ↦ ϑ t * ⟪χ, ∫ s in Set.Iio t, waveSinPropagator F (t - s) (G s)⟫) ∧
      Integrable (fun s ↦ ∫ t in Set.Ioi s, ϑ t * ⟪χ, waveSinPropagator F (t - s) (G s)⟫) ∧
      ∫ t, ϑ t * ⟪χ, ∫ s in Set.Iio t, waveSinPropagator F (t - s) (G s)⟫ =
        ∫ s, ∫ t in Set.Ioi s, ϑ t * ⟪χ, waveSinPropagator F (t - s) (G s)⟫ := by
  set f : ℝ × ℝ → ℂ := {p | p.2 < p.1}.indicator
    fun p ↦ ϑ p.1 * ⟪χ, waveSinPropagator F (p.1 - p.2) (G p.2)⟫
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.2 < p.1} :=
    measurableSet_lt measurable_snd measurable_fst
  -- `‖f(t, s)‖ ≤ ‖χ‖ (‖ϑ(t)‖ |t| ‖G(s)‖ + ‖ϑ(t)‖ ‖D⁻¹ sin (sD) G(s)‖)`, a sum of products.
  have hf : Integrable f (volume.prod volume) := by
    have h₁ : Integrable (fun t ↦ ‖ϑ t‖ * |t|) :=
      (hϑ.norm.mul continuous_abs).integrable_of_hasCompactSupport hϑc.norm.mul_right
    have h₂ : Integrable (fun t ↦ ‖ϑ t‖) := hϑ.norm.integrable_of_hasCompactSupport hϑc.norm
    refine (((h₁.mul_prod hG.norm).add (h₂.mul_prod hSG.norm)).const_mul ‖χ‖).mono' ?_
      (.of_forall fun p ↦ ?_)
    · exact (((hϑ.comp continuous_fst).aestronglyMeasurable).mul
        ((continuous_const.inner continuous_id).comp_aestronglyMeasurable
          (aestronglyMeasurable_waveSinPropagator_sub_prod hG.aestronglyMeasurable))).indicator
          hmeas
    · simp only [f, Set.indicator_apply]
      split_ifs
      · rw [norm_mul]
        calc ‖ϑ p.1‖ * ‖⟪χ, waveSinPropagator F (p.1 - p.2) (G p.2)⟫‖
            ≤ ‖ϑ p.1‖ * (‖χ‖ * (|p.1| * ‖G p.2‖ + ‖waveSinPropagator F p.2 (G p.2)‖)) := by
              gcongr
              exact (norm_inner_le_norm _ _).trans
                (mul_le_mul_of_nonneg_left (norm_waveSinPropagator_sub_apply_le _ _ _)
                  (norm_nonneg _))
          _ = _ := by simp only [Pi.add_apply]; ring
      · rw [norm_zero]
        simp only [Pi.add_apply]
        positivity
  have hslice (t : ℝ) : (fun s ↦ f (t, s)) = (Set.Iio t).indicator
      fun s ↦ ϑ t * ⟪χ, waveSinPropagator F (t - s) (G s)⟫ := by
    ext s
    simp [f, Set.indicator_apply]
  have hslice' (s : ℝ) : (fun t ↦ f (t, s)) = (Set.Ioi s).indicator
      fun t ↦ ϑ t * ⟪χ, waveSinPropagator F (t - s) (G s)⟫ := by
    ext t
    simp [f, Set.indicator_apply]
  have hleft (t : ℝ) : ∫ s, f (t, s) =
      ϑ t * ⟪χ, ∫ s in Set.Iio t, waveSinPropagator F (t - s) (G s)⟫ := by
    rw [hslice, integral_indicator measurableSet_Iio, integral_const_mul,
      integral_inner ((integrable_waveSinPropagator_sub_apply hG hSG t).integrableOn)]
  have hright (s : ℝ) : ∫ t, f (t, s) =
      ∫ t in Set.Ioi s, ϑ t * ⟪χ, waveSinPropagator F (t - s) (G s)⟫ := by
    rw [hslice', integral_indicator measurableSet_Ioi]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hleft] using hf.integral_prod_left
  · simpa only [hright] using hf.integral_prod_right
  · simp_rw [← hleft, ← hright]
    exact integral_integral_swap hf

/-- For `ϑ` continuous with compact support and `χ ∈ L²`, the pairing `t ↦ ϑ(t) ⟪χ, u(t)⟫` with the
retarded integral `u(t) = ∫_{s < t} D⁻¹ sin ((t - s)D) G(s) ds` is integrable, provided `G` and
`s ↦ D⁻¹ sin (sD) G(s)` are. -/
theorem integrable_mul_inner_setIntegral_Iio_waveSinPropagator_sub (hG : Integrable G)
    (hSG : Integrable fun s ↦ waveSinPropagator F s (G s)) {ϑ : ℝ → ℂ} (hϑ : Continuous ϑ)
    (hϑc : HasCompactSupport ϑ) (χ : Lp F 2 (volume : Measure E)) :
    Integrable fun t ↦ ϑ t * ⟪χ, ∫ s in Set.Iio t, waveSinPropagator F (t - s) (G s)⟫ :=
  (integral_mul_inner_setIntegral_Iio_waveSinPropagator_sub hG hSG hϑ hϑc χ).1

/-- **Integration by parts against a wave started at time `s`.** For `φ ∈ L²` with
`Δφ = ψ ∈ L²`, `g ∈ L²` and a compactly supported `C²` function `θ`, the function
`k(t) = ⟪φ, D⁻¹ sin ((t - s)D) g⟫` vanishes at `t = s` with derivative `⟪φ, g⟫` there and
satisfies `k'' = ⟪ψ, D⁻¹ sin ((t - s)D) g⟫`, so
`∫_{t > s} θ''(t) k(t) dt = θ(s) ⟪φ, g⟫ + ∫_{t > s} θ(t) ⟪ψ, D⁻¹ sin ((t - s)D) g⟫ dt`. -/
private theorem setIntegral_Ioi_deriv_deriv_mul_inner_waveSinPropagator_sub
    (hφψ : Δ (φ : 𝓢'(E, F)) = (ψ : 𝓢'(E, F))) (g : Lp F 2 (volume : Measure E)) {θ : ℝ → ℂ}
    (hθ : ContDiff ℝ 2 θ) (hθc : HasCompactSupport θ) (s : ℝ) :
    ∫ t in Set.Ioi s, deriv (deriv θ) t * ⟪φ, waveSinPropagator F (t - s) g⟫ =
      θ s * ⟪φ, g⟫ + ∫ t in Set.Ioi s, θ t * ⟪ψ, waveSinPropagator F (t - s) g⟫ := by
  set k : ℝ → ℂ := fun t ↦ ⟪φ, waveSinPropagator F (t - s) g⟫
  set k' : ℝ → ℂ := fun t ↦ ⟪φ, waveCosPropagator F (t - s) g⟫
  set k'' : ℝ → ℂ := fun t ↦ ⟪ψ, waveSinPropagator F (t - s) g⟫
  have hk (t : ℝ) : HasDerivAt k (k' t) t := by
    have h := (hasDerivAt_waveSinPropagator_apply (F := F) (E := E) g (t - s)).comp_sub_const t s
    have := (hasDerivAt_const t φ).inner ℂ h
    rw [inner_zero_left, add_zero] at this
    exact this
  have hk' (t : ℝ) : HasDerivAt k' (k'' t) t := by
    have h := (hasDerivAt_waveCosPropagator_apply hφψ (t - s)).comp_sub_const t s
    have := h.inner ℂ (hasDerivAt_const t g)
    rw [inner_zero_right, zero_add, inner_waveSinPropagator_apply] at this
    refine this.congr_of_eventuallyEq (.of_forall fun t ↦ ?_)
    exact (inner_waveCosPropagator_apply _ _ _).symm
  have hck : Continuous k := continuous_iff_continuousAt.2 fun t ↦ (hk t).continuousAt
  have hck' : Continuous k' := continuous_iff_continuousAt.2 fun t ↦ (hk' t).continuousAt
  have hck'' : Continuous k'' :=
    continuous_const.inner ((continuous_waveSinPropagator_apply g).comp (continuous_sub_right s))
  have hθ' : ContDiff ℝ 1 (deriv θ) := hθ.deriv' (n := 1)
  have hθ₀ (t : ℝ) : HasDerivAt θ (deriv θ t) t := (hθ.differentiable (by norm_num) t).hasDerivAt
  have hθ'' (t : ℝ) : HasDerivAt (deriv θ) (deriv (deriv θ) t) t :=
    (hθ'.differentiable one_ne_zero t).hasDerivAt
  have hint {v w : ℝ → ℂ} (hv : Continuous v) (hw : Continuous w) (hc : HasCompactSupport (v * w)) :
      IntegrableOn (v * w) (Set.Ioi s) :=
    ((hv.mul hw).integrable_of_hasCompactSupport hc).integrableOn
  have hs {v w : ℝ → ℂ} (hv : Continuous v) (hw : Continuous w) :
      Tendsto (v * w) (𝓝[>] s) (𝓝 (v s * w s)) :=
    ((hv.mul hw).tendsto s).mono_left nhdsWithin_le_nhds
  have hk0 : k s = 0 := by simp [k]
  have hk'0 : k' s = ⟪φ, g⟫ := by simp [k']
  -- Integrate by parts twice: `∫ θ'' k = -∫ θ' k' = θ(s) k'(s) + ∫ θ k''`, the boundary terms at
  -- infinity vanishing by compact support.
  have h₁ := integral_Ioi_mul_deriv_eq_deriv_mul (fun t _ ↦ hθ'' t) (fun t _ ↦ hk t)
    (hint hθ'.continuous hck' hθc.deriv.mul_right)
    (hint (hθ'.continuous_deriv le_rfl) hck hθc.deriv.deriv.mul_right)
    (hs hθ'.continuous hck) (hθc.deriv.mul_right.is_zero_at_infty.mono_left atTop_le_cocompact)
  have h₂ := integral_Ioi_mul_deriv_eq_deriv_mul (fun t _ ↦ hθ₀ t) (fun t _ ↦ hk' t)
    (hint hθ.continuous hck'' hθc.mul_right) (hint hθ'.continuous hck' hθc.deriv.mul_right)
    (hs hθ.continuous hck') (hθc.mul_right.is_zero_at_infty.mono_left atTop_le_cocompact)
  simp only [hk0, mul_zero, sub_zero, zero_sub, hk'0] at h₁ h₂
  -- Fold the integrands into `k` and `k''`, the form in which `h₁` and `h₂` are stated.
  change ∫ t in Set.Ioi s, deriv (deriv θ) t * k t = θ s * ⟪φ, g⟫ + ∫ t in Set.Ioi s, θ t * k'' t
  linear_combination h₁ - h₂

/-- **The retarded integral solves the forced wave equation, tested in space and time.** Let
`G : ℝ → L²` be integrable with `s ↦ D⁻¹ sin (sD) G(s)` integrable, and let
`u(t) = ∫_{s < t} D⁻¹ sin ((t - s)D) G(s) ds` be its retarded Duhamel integral, the solution of
`∂ₜ²u - Δu = G` with zero data at `t = -∞`. For a test function `φ ∈ L²` with `Δφ = ψ ∈ L²` and a
compactly supported `C²` function `θ` of time,

`∫ θ''(t) ⟪φ, u(t)⟫ dt = ∫ θ(t) (⟪ψ, u(t)⟫ + ⟪φ, G(t)⟫) dt`.

The second hypothesis holds when the values of `G` are frequency-localized away from the origin,
where the operators `D⁻¹ sin (sD)` are bounded uniformly in `s`; without it the retarded integral
need not exist, since `‖D⁻¹ sin (sD)‖` grows like `|s|`. -/
theorem integral_deriv_deriv_mul_inner_setIntegral_Iio_waveSinPropagator_sub
    (hφψ : Δ (φ : 𝓢'(E, F)) = (ψ : 𝓢'(E, F))) (hG : Integrable G)
    (hSG : Integrable fun s ↦ waveSinPropagator F s (G s)) {θ : ℝ → ℂ} (hθ : ContDiff ℝ 2 θ)
    (hθc : HasCompactSupport θ) :
    ∫ t, deriv (deriv θ) t * ⟪φ, ∫ s in Set.Iio t, waveSinPropagator F (t - s) (G s)⟫ =
      ∫ t, θ t * (⟪ψ, ∫ s in Set.Iio t, waveSinPropagator F (t - s) (G s)⟫ + ⟪φ, G t⟫) := by
  have hθ' : ContDiff ℝ 1 (deriv θ) := hθ.deriv' (n := 1)
  obtain ⟨-, -, h₁⟩ := integral_mul_inner_setIntegral_Iio_waveSinPropagator_sub hG hSG
    (hθ'.continuous_deriv le_rfl) hθc.deriv.deriv φ
  obtain ⟨hi₁, hi₂, h₂⟩ := integral_mul_inner_setIntegral_Iio_waveSinPropagator_sub hG hSG
    hθ.continuous hθc ψ
  have hθG : Integrable fun t ↦ θ t * ⟪φ, G t⟫ :=
    (hG.const_inner φ).locallyIntegrable.integrable_smul_left_of_hasCompactSupport hθ.continuous hθc
  simp_rw [mul_add]
  rw [integral_add hi₁ hθG, h₁, h₂, ← integral_add hi₂ hθG]
  exact integral_congr_ae (ae_of_all _ fun s ↦
    (setIntegral_Ioi_deriv_deriv_mul_inner_waveSinPropagator_sub hφψ (G s) hθ hθc s).trans
      (add_comm _ _))

/-- The forced wave equation for the retarded integral of `G`, tested against `θ(t) ψ(x)` for a
Schwartz function `ψ`, with the pairing with `G` written as an integral over space. -/
private theorem integral_deriv_deriv_mul_inner_setIntegral_Iio_sub_eq (hG : Integrable G)
    (hSG : Integrable fun s ↦ waveSinPropagator F s (G s)) (ψ : 𝓢(E, F)) {θ : ℝ → ℂ}
    (hθ : ContDiff ℝ 2 θ) (hθc : HasCompactSupport θ) :
    (∫ t, deriv (deriv θ) t *
        ⟪ψ.toLp 2, ∫ τ in Set.Iio t, waveSinPropagator F (t - τ) (G τ)⟫) -
      ∫ t, θ t * ⟪(Δ ψ).toLp 2, ∫ τ in Set.Iio t, waveSinPropagator F (t - τ) (G τ)⟫ =
        ∫ t, θ t * ∫ x, ⟪ψ x, G t x⟫ := by
  have hφ : Δ ((ψ.toLp 2 : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) =
      (((Δ ψ).toLp 2 : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) := by
    simp
  have hpair (t : ℝ) : ∫ x, ⟪ψ x, G t x⟫ = ⟪ψ.toLp 2, G t⟫ := by
    rw [show ψ.toLp 2 volume = (ψ.memLp 2).toLp ψ from
      Lp.ext ((ψ.coeFn_toLp 2).trans (ψ.memLp 2).coeFn_toLp.symm)]
    exact (L2.toLp_inner_of_ae_eq (𝕜 := ℂ) (ψ.memLp 2) EventuallyEq.rfl).symm
  refine (congrArg (· - _) (integral_deriv_deriv_mul_inner_setIntegral_Iio_waveSinPropagator_sub
    hφ hG hSG hθ hθc)).trans ?_
  have hθG : Integrable fun t ↦ θ t * ⟪ψ.toLp 2, G t⟫ :=
    (hG.const_inner _).locallyIntegrable.integrable_smul_left_of_hasCompactSupport hθ.continuous hθc
  simp_rw [mul_add, hpair]
  rw [integral_add (integrable_mul_inner_setIntegral_Iio_waveSinPropagator_sub hG hSG
    hθ.continuous hθc _) hθG]
  ring

/-- **Limits of sums of retarded integrals solve the forced wave equation.** Let `Gⱼ : ℝ → L²`,
`j ∈ ι`, be integrable forcing terms with each `s ↦ D⁻¹ sin (sD) Gⱼ(s)` integrable, and let
`U : ℝ → L^r` be a limit of the finite sums of their retarded integrals
`uⱼ(t) = ∫_{τ < t} D⁻¹ sin ((t - τ)D) Gⱼ(τ) dτ`, in `L^r` for almost every `t` and in the mixed
norm `L^q_t L^r_x` for some `1 ≤ q`. Then `∂ₜ²U - ΔU = ∑ⱼ Gⱼ` in the sense of distributions,
tested against `θ(t) ψ(x)`: for every Schwartz function `ψ` and every compactly supported `C²`
function `θ` of time, the series `∑ⱼ ∫ θ(t) ∫ ⟪ψ(x), Gⱼ(t)(x)⟫ dx dt` converges, with sum

`∫ θ''(t) ∫ ⟪ψ(x), U(t)(x)⟫ dx dt - ∫ θ(t) ∫ ⟪Δψ(x), U(t)(x)⟫ dx dt`. -/
theorem hasSum_integral_mul_integral_inner_of_tendsto_sum_setIntegral_Iio_waveSinPropagator_sub
    {ι : Type*} [Countable ι] {q r : ℝ≥0∞} [Fact (1 ≤ r)] (hq : 1 ≤ q)
    {G : ι → ℝ → Lp F 2 (volume : Measure E)} (hint : ∀ j, Integrable (G j))
    (hSG : ∀ j, Integrable fun s ↦ waveSinPropagator F s (G j s))
    {U : ℝ → Lp F r (volume : Measure E)}
    (hae : ∀ᵐ t, Tendsto (fun s : Finset ι ↦ eLpNorm (⇑(U t) - ⇑(∑ j ∈ s,
      ∫ τ in Set.Iio t, waveSinPropagator F (t - τ) (G j τ))) r volume) atTop (𝓝 0))
    (hlim : Tendsto (fun s : Finset ι ↦ eLpNorm (fun t ↦ eLpNorm (⇑(U t) - ⇑(∑ j ∈ s,
      ∫ τ in Set.Iio t, waveSinPropagator F (t - τ) (G j τ))) r volume) q volume) atTop (𝓝 0))
    (ψ : 𝓢(E, F)) {θ : ℝ → ℂ} (hθ : ContDiff ℝ 2 θ) (hθc : HasCompactSupport θ) :
    HasSum (fun j ↦ ∫ t, θ t * ∫ x, ⟪ψ x, G j t x⟫)
      ((∫ t, deriv (deriv θ) t * ∫ x, ⟪ψ x, U t x⟫) - ∫ t, θ t * ∫ x, ⟪(Δ ψ) x, U t x⟫) := by
  have hum (j : ι) := aestronglyMeasurable_setIntegral_Iio_waveSinPropagator_sub
    (hint j).aestronglyMeasurable
  have hθ' : ContDiff ℝ 1 (deriv θ) := hθ.deriv' (n := 1)
  have hi (χ : 𝓢(E, F)) {ϑ : ℝ → ℂ} (hϑ : Continuous ϑ) (hϑc : HasCompactSupport ϑ) (j : ι) :=
    integrable_mul_inner_setIntegral_Iio_waveSinPropagator_sub (hint j) (hSG j) hϑ hϑc (χ.toLp 2)
  -- Against `ϑ(t) χ(x)`, the pairings of the partial sums converge to those of `U`.
  have hconv (χ : 𝓢(E, F)) {ϑ : ℝ → ℂ} (hϑ : Continuous ϑ) (hϑc : HasCompactSupport ϑ) :
      Tendsto (fun s : Finset ι ↦ ∫ t, ϑ t * ⟪χ.toLp 2, ∑ j ∈ s,
        ∫ τ in Set.Iio t, waveSinPropagator F (t - τ) (G j τ)⟫) atTop
        (𝓝 (∫ t, ϑ t * ∫ x, ⟪χ x, U t x⟫)) :=
    tendsto_integral_mul_inner_of_tendsto_eLpNorm_eLpNorm_sub hq hae hlim (χ.coeFn_toLp 2)
      (χ.memLp _) (hϑ.memLp_of_hasCompactSupport hϑc)
      (fun s ↦ Finset.aestronglyMeasurable_fun_sum s fun j _ ↦ hum j) fun s ↦ by
        simp_rw [inner_sum, Finset.mul_sum]
        exact integrable_finsetSum s fun j _ ↦ hi χ hϑ hϑc j
  -- `HasSum` is by definition the convergence of the partial sums along `atTop`.
  refine ((hconv ψ (hθ'.continuous_deriv le_rfl) hθc.deriv.deriv).sub
    (hconv (Δ ψ) hθ.continuous hθc)).congr fun s ↦ ?_
  simp_rw [inner_sum, Finset.mul_sum]
  rw [integral_finsetSum s fun j _ ↦ hi ψ (hθ'.continuous_deriv le_rfl) hθc.deriv.deriv j,
    integral_finsetSum s fun j _ ↦ hi (Δ ψ) hθ.continuous hθc j, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ ↦
    integral_deriv_deriv_mul_inner_setIntegral_Iio_sub_eq (hint j) (hSG j) ψ hθ hθc

end Duhamel

end TauCeti
