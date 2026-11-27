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
(`TauCeti.continuous_waveDuhamelSolution`). So it is for locally integrable forcing
(`TauCeti.continuous_waveDuhamelSolution_of_locallyIntegrable`), and on `[a, b] ∋ 0` for forcing
integrable on `[a, b]` (`TauCeti.continuousOn_waveDuhamelSolution_of_integrableOn`), where it
depends only on the forcing on `[a, b]` (`TauCeti.waveDuhamelSolution_indicator_Icc`). For
continuous forcing and every `φ ∈ L²` whose distributional Laplacian `ψ = Δφ` lies in `L²`, the
scalar function `t ↦ ⟪φ, u(t)⟫` is twice differentiable, with

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

The tested form holds for forcing that is only integrable: if `a ≤ 0 ≤ b`, `G` is integrable on
`[a, b]` and `θ` vanishes outside `[a, b]`, then
`∫ θ''(t) ⟪φ, u(t)⟫ dt = ∫ θ(t) ⟪ψ, u(t)⟫ dt + ∫ θ(t) ⟪φ, G(t)⟫ dt`
(`TauCeti.integral_deriv_deriv_mul_inner_waveDuhamelSolution_of_integrableOn`). Continuous
forcings `Gₙ` approximate `G` in `L¹`, and on `[a, b]` the solutions depend on the forcing through
the a priori bound `‖u(t)‖ ≤ ‖f‖ + |t| ‖g‖ + |t| ∫_{Ι 0 t} ‖G‖`
(`TauCeti.norm_waveDuhamelSolution_le_mul_setIntegral`), so each term of the identity passes to the
limit.

This tested form passes to limits that need not lie in `L²`. Let `a ≤ 0 ≤ b`. If solutions `uᵢ`
with data in `L²` and forcings `Gᵢ` integrable on `[a, b]` converge to `U : ℝ → L^r` in `L^r` at
almost every time of `[a, b]` and in the mixed norm `L^q([a, b]; L^r_x)`, `1 ≤ q`, then for every
Schwartz `φ` and every `θ` vanishing outside `[a, b]` the tested forcings `∫ θ(t) ⟪φ, Gᵢ(t)⟫ dt`
converge to `∫ θ''(t) ∫ ⟪φ, U(t)⟫ dx dt - ∫ θ(t) ∫ ⟪Δφ, U(t)⟫ dx dt`
(`TauCeti.tendsto_integral_mul_inner_of_tendsto_waveDuhamelSolution`), by Hölder's inequality in
space and in time (`TauCeti.tendsto_integral_mul_integral_inner_of_tendsto_eLpNorm_eLpNorm_sub`):
`∂ₜ²U - ΔU` is the limit of the forcings on `(a, b)` in the sense of distributions. For limits of
free waves, `∫ θ''(t) ∫ ⟪φ, U(t)⟫ dx dt = ∫ θ(t) ∫ ⟪Δφ, U(t)⟫ dx dt` for every compactly supported
`θ` (`TauCeti.integral_deriv_deriv_mul_integral_inner_eq_of_tendsto_waveDuhamelSolution`). This
identifies the evolutions of data in homogeneous Besov spaces, defined as such limits, as solutions
of the wave equation.

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
  `TauCeti.continuous_waveDuhamelSolution`,
  `TauCeti.continuous_waveDuhamelSolution_of_locallyIntegrable`,
  `TauCeti.continuousOn_waveDuhamelSolution_of_integrableOn`, `TauCeti.waveDuhamelSolution_add`,
  `TauCeti.waveDuhamelSolution_sum`, `TauCeti.waveDuhamelSolution_smul`,
  `TauCeti.waveDuhamelSolution_congr`, `TauCeti.waveDuhamelSolution_indicator_Icc` and
  `TauCeti.waveDuhamelSolution_eq_setIntegral_Iio`;
* `TauCeti.norm_waveDuhamelSolution_le` and `TauCeti.norm_waveDuhamelSolution_le_mul_setIntegral`:
  a priori bounds;
* `TauCeti.hasDerivAt_inner_waveDuhamelSolution`,
  `TauCeti.hasDerivAt_deriv_inner_waveDuhamelSolution`: the weak wave equation;
* `TauCeti.integral_deriv_deriv_mul_inner_waveDuhamelSolution`: the wave equation tested against
  `θ(t) φ(x)`, and `TauCeti.integral_deriv_deriv_mul_inner_waveDuhamelSolution_of_integrableOn` for
  integrable forcing;
* `TauCeti.integral_deriv_deriv_mul_integral_inner_eq_of_tendsto_waveDuhamelSolution`: limits of
  free waves in a mixed norm `L^q_t L^r_x` solve the wave equation in the sense of distributions;
* `TauCeti.tendsto_integral_mul_inner_of_tendsto_waveDuhamelSolution`: limits of forced waves in
  a mixed norm `L^q([a, b]; L^r_x)` solve the forced wave equation on `(a, b)`;
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
open scoped Interval
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

/-- The **a priori bound** `‖u(t)‖ ≤ ‖f‖ + |t| ‖g‖ + |t| ∫_{Ι 0 t} ‖G(s)‖ ds`, for forcing `G`
integrable between `0` and `t`. -/
theorem norm_waveDuhamelSolution_le_mul_setIntegral (f g : Lp F 2 (volume : Measure E))
    {G : ℝ → Lp F 2 (volume : Measure E)} {t : ℝ} (hG : IntervalIntegrable G volume 0 t) :
    ‖waveDuhamelSolution F f g G t‖ ≤ ‖f‖ + |t| * ‖g‖ + |t| * ∫ s in Ι 0 t, ‖G s‖ := by
  have hG' : Integrable (fun s ↦ |t| * ‖G s‖) (volume.restrict (Ι 0 t)) :=
    (intervalIntegrable_iff.1 hG).norm.const_mul _
  -- Between `0` and `t`, the weight `|t - s|` is at most `|t|`.
  have h : |∫ s in (0 : ℝ)..t, |t - s| * ‖G s‖| ≤ |t| * ∫ s in Ι 0 t, ‖G s‖ := calc
    _ ≤ ∫ s in Ι 0 t, ‖|t - s| * ‖G s‖‖ := intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ s in Ι 0 t, |t| * ‖G s‖ := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _) hG'
        (ae_restrict_of_forall_mem measurableSet_uIoc fun s hs ↦ ?_)
      dsimp only
      rw [norm_mul, norm_norm, Real.norm_of_nonneg (abs_nonneg _)]
      exact mul_le_mul_of_nonneg_right
        (by simpa using Set.abs_sub_right_of_mem_uIcc (Set.uIoc_subset_uIcc hs)) (norm_nonneg _)
    _ = |t| * ∫ s in Ι 0 t, ‖G s‖ := integral_const_mul _ _
  linarith [norm_waveDuhamelSolution_le f g hG]

/-- The solution at time `t` depends on the forcing only through its values between `0` and
`t`. -/
theorem waveDuhamelSolution_congr (f g : Lp F 2 (volume : Measure E))
    {G₁ G₂ : ℝ → Lp F 2 (volume : Measure E)} {t : ℝ} (h : Set.EqOn G₁ G₂ (Set.uIcc 0 t)) :
    waveDuhamelSolution F f g G₁ t = waveDuhamelSolution F f g G₂ t := by
  rw [waveDuhamelSolution_def, waveDuhamelSolution_def,
    intervalIntegral.integral_congr fun s hs ↦ congrArg (waveSinPropagator F (t - s)) (h hs)]

/-- **Superposition** for finite families: for forcings integrable between `0` and `t`, the
solution at time `t` with the summed data and forcing is the sum of the solutions. -/
theorem waveDuhamelSolution_sum {ι : Type*} (s : Finset ι) (f g : ι → Lp F 2 (volume : Measure E))
    {G : ι → ℝ → Lp F 2 (volume : Measure E)} {t : ℝ}
    (hG : ∀ i ∈ s, IntervalIntegrable (G i) volume 0 t) :
    waveDuhamelSolution F (∑ i ∈ s, f i) (∑ i ∈ s, g i) (∑ i ∈ s, G i) t =
      ∑ i ∈ s, waveDuhamelSolution F (f i) (g i) (G i) t := by
  simp only [waveDuhamelSolution_def, map_sum, Finset.sum_apply,
    intervalIntegral.integral_finsetSum fun i hi ↦ (hG i hi).waveSinPropagator_sub_apply,
    Finset.sum_add_distrib]

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

/-- The solution depends Lipschitz continuously on the forcing: for forcings `G₁` and `G₂`
integrable between `0` and `t`, `‖u₁(t) - u₂(t)‖ ≤ |t| ∫_{Ι 0 t} ‖G₁(s) - G₂(s)‖ ds`. -/
theorem norm_waveDuhamelSolution_sub_waveDuhamelSolution_le (f g : Lp F 2 (volume : Measure E))
    {G₁ G₂ : ℝ → Lp F 2 (volume : Measure E)} {t : ℝ} (hG₁ : IntervalIntegrable G₁ volume 0 t)
    (hG₂ : IntervalIntegrable G₂ volume 0 t) :
    ‖waveDuhamelSolution F f g G₁ t - waveDuhamelSolution F f g G₂ t‖ ≤
      |t| * ∫ s in Ι 0 t, ‖G₁ s - G₂ s‖ := by
  have h := waveDuhamelSolution_add (F := F) (G₁ := G₂) (G₂ := G₁ - G₂) f 0 g 0 hG₂
    (hG₁.sub hG₂)
  rw [add_zero, add_zero, show G₂ + (G₁ - G₂) = G₁ by abel] at h
  rw [h, add_sub_cancel_left]
  simpa using norm_waveDuhamelSolution_le_mul_setIntegral (F := F) (G := G₁ - G₂) 0 0
    (hG₁.sub hG₂)

/-- On `[a, b] ∋ 0`, the solution depends only on the forcing on `[a, b]`: it agrees with the
solution with the forcing `1_{[a, b]} G`. -/
theorem waveDuhamelSolution_indicator_Icc (f g : Lp F 2 (volume : Measure E)) {a b t : ℝ}
    (ha : a ≤ 0) (hb : 0 ≤ b) (ht : t ∈ Set.Icc a b) :
    waveDuhamelSolution F f g ((Set.Icc a b).indicator G) t = waveDuhamelSolution F f g G t :=
  waveDuhamelSolution_congr f g fun _ hs ↦
    Set.indicator_of_mem (Set.uIcc_subset_Icc ⟨ha, hb⟩ ht hs) G

/-- On `[a, b] ∋ 0`, for forcing integrable on `[a, b]`, the solution is continuous on `[a, b]` with
values in `L²`: there it agrees with the solution with the integrable forcing `H = 1_{[a, b]} G`,
which near each time is a uniform limit of solutions with continuous forcings approximating `H` in
`L¹`. -/
theorem continuousOn_waveDuhamelSolution_of_integrableOn (f g : Lp F 2 (volume : Measure E))
    {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) (hG : IntegrableOn G (Set.Icc a b)) :
    ContinuousOn (waveDuhamelSolution F f g G) (Set.Icc a b) := by
  set H := (Set.Icc a b).indicator G
  have hH : Integrable H := hG.integrable_indicator measurableSet_Icc
  refine ContinuousOn.congr (f := waveDuhamelSolution F f g H) (Continuous.continuousOn ?_)
    fun _ ht ↦ (waveDuhamelSolution_indicator_Icc f g ha hb ht).symm
  refine continuous_of_locally_uniform_approx_of_continuousAt fun x u hu ↦ ?_
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
  have hx : 0 < |x| + 2 := by positivity
  obtain ⟨K, -, hHK, hKc, hK⟩ := hH.exists_hasCompactSupport_integral_sub_le (div_pos hε hx)
  refine ⟨Set.Ioo (x - 1) (x + 1), Ioo_mem_nhds (by linarith) (by linarith),
    waveDuhamelSolution F f g K, (continuous_waveDuhamelSolution f g hKc).continuousAt,
    fun y hy ↦ hεu ?_⟩
  have hy : |y| < |x| + 2 :=
    abs_lt.2 ⟨by linarith [neg_abs_le x, hy.1], by linarith [le_abs_self x, hy.2]⟩
  rw [dist_eq_norm]
  calc ‖waveDuhamelSolution F f g H y - waveDuhamelSolution F f g K y‖
      ≤ |y| * ∫ s in Ι 0 y, ‖H s - K s‖ :=
        norm_waveDuhamelSolution_sub_waveDuhamelSolution_le f g hH.intervalIntegrable
          hK.intervalIntegrable
    _ ≤ |y| * (ε / (|x| + 2)) := by
        gcongr
        exact (setIntegral_le_integral (hH.sub hK).norm
          (Eventually.of_forall fun _ ↦ norm_nonneg _)).trans hHK
    _ < (|x| + 2) * (ε / (|x| + 2)) := mul_lt_mul_of_pos_right hy (div_pos hε hx)
    _ = ε := by field_simp

/-- For locally integrable forcing, the solution is continuous in time with values in `L²`: near
each time `x` it is continuous on `[-(|x| + 1), |x| + 1]`, where the forcing is integrable. -/
theorem continuous_waveDuhamelSolution_of_locallyIntegrable (f g : Lp F 2 (volume : Measure E))
    (hG : LocallyIntegrable G) : Continuous (waveDuhamelSolution F f g G) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  have hx : 0 ≤ |x| + 1 := by positivity
  refine (continuousOn_waveDuhamelSolution_of_integrableOn f g (neg_nonpos.2 hx) hx
    (hG.integrableOn_isCompact isCompact_Icc)).continuousAt (Icc_mem_nhds ?_ ?_)
  · linarith [neg_abs_le x]
  · linarith [le_abs_self x]

/-- If continuous forcings `Kₙ` converge to an integrable forcing `G` in `L¹`, the solutions
tested against `w(t) χ` converge, for every continuous compactly supported `w`. -/
private theorem tendsto_integral_mul_inner_waveDuhamelSolution_of_tendsto
    (f g χ : Lp F 2 (volume : Measure E)) {K : ℕ → ℝ → Lp F 2 (volume : Measure E)}
    (hKc : ∀ n, Continuous (K n)) (hK : ∀ n, Integrable (K n)) (hG : Integrable G)
    (hKG : Tendsto (fun n ↦ ∫ s, ‖K n s - G s‖) atTop (𝓝 0)) {w : ℝ → ℂ} (hw : Continuous w)
    (hwc : HasCompactSupport w) :
    Tendsto (fun n ↦ ∫ t, w t * ⟪χ, waveDuhamelSolution F f g (K n) t⟫) atTop
      (𝓝 (∫ t, w t * ⟪χ, waveDuhamelSolution F f g G t⟫)) := by
  have hle {k : ℝ → Lp F 2 (volume : Measure E)} (hk : Integrable k) (t : ℝ) :
      ∫ s in Ι 0 t, ‖k s‖ ≤ ∫ s, ‖k s‖ :=
    setIntegral_le_integral hk.norm (Eventually.of_forall fun _ ↦ norm_nonneg _)
  -- At time `t` the solutions are at distance at most `|t| ∫ ‖Kₙ - G‖` from the limit.
  have hdist (n : ℕ) (t : ℝ) :
      ‖waveDuhamelSolution F f g (K n) t - waveDuhamelSolution F f g G t‖ ≤
        |t| * ∫ s, ‖K n s - G s‖ :=
    (norm_waveDuhamelSolution_sub_waveDuhamelSolution_le f g (hK n).intervalIntegrable
      hG.intervalIntegrable).trans
        (mul_le_mul_of_nonneg_left (hle ((hK n).sub hG) t) (abs_nonneg t))
  have hu (t : ℝ) : ‖waveDuhamelSolution F f g G t‖ ≤ ‖f‖ + |t| * ‖g‖ + |t| * ∫ s, ‖G s‖ :=
    (norm_waveDuhamelSolution_le_mul_setIntegral f g hG.intervalIntegrable).trans
      (by linarith [mul_le_mul_of_nonneg_left (hle hG t) (abs_nonneg t)])
  refine tendsto_integral_filter_of_dominated_convergence
    (fun t ↦ ‖w t‖ * (‖χ‖ * (‖f‖ + |t| * ‖g‖ + |t| * ((∫ s, ‖G s‖) + 1))))
    (Eventually.of_forall fun n ↦ (hw.mul (continuous_const.inner
      (continuous_waveDuhamelSolution f g (hKc n)))).aestronglyMeasurable) ?_
    ((by fun_prop : Continuous fun t ↦ ‖w t‖ *
      (‖χ‖ * (‖f‖ + |t| * ‖g‖ + |t| * ((∫ s, ‖G s‖) + 1)))).integrable_of_hasCompactSupport
        hwc.norm.mul_right) (Eventually.of_forall fun t ↦ ?_)
  · -- Once `∫ ‖Kₙ - G‖ ≤ 1`, the solutions are bounded by `‖u(t)‖ + |t|`.
    filter_upwards [hKG.eventually (eventually_le_nhds zero_lt_one)] with n hn
    refine Eventually.of_forall fun t ↦ ?_
    rw [norm_mul]
    gcongr
    refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    have := mul_le_mul_of_nonneg_left hn (abs_nonneg t)
    linarith [norm_le_insert' (waveDuhamelSolution F f g (K n) t)
      (waveDuhamelSolution F f g G t), hdist n t, hu t]
  · refine (tendsto_const_nhds.inner (tendsto_iff_norm_sub_tendsto_zero.2
      (squeeze_zero (fun _ ↦ norm_nonneg _) (hdist · t) ?_))).const_mul (w t)
    simpa using hKG.const_mul |t|

/-- `TauCeti.integral_deriv_deriv_mul_inner_waveDuhamelSolution` for forcing integrable on `ℝ`. -/
private theorem integral_deriv_deriv_mul_inner_waveDuhamelSolution_of_integrable
    (hφψ : Δ (φ : 𝓢'(E, F)) = (ψ : 𝓢'(E, F))) (f g : Lp F 2 (volume : Measure E))
    (hG : Integrable G) {θ : ℝ → ℂ} (hθ : ContDiff ℝ 2 θ) (hθc : HasCompactSupport θ) :
    ∫ t, deriv (deriv θ) t * ⟪φ, waveDuhamelSolution F f g G t⟫ =
      (∫ t, θ t * ⟪ψ, waveDuhamelSolution F f g G t⟫) + ∫ t, θ t * ⟪φ, G t⟫ := by
  -- Approximate `G` in `L¹` by continuous forcings `K n`, for which the identity holds.
  choose K _ hKG hKc hK using fun n : ℕ ↦
    hG.exists_hasCompactSupport_integral_sub_le (Nat.one_div_pos_of_nat (n := n) (α := ℝ))
  have hKG' : Tendsto (fun n ↦ ∫ s, ‖K n s - G s‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      (fun n ↦ (integral_congr_ae (Eventually.of_forall fun s ↦
        norm_sub_rev (K n s) (G s))).trans_le (hKG n)) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨C, hC⟩ := hθ.continuous.bounded_above_of_compact_support hθc
  have hint {k : ℝ → Lp F 2 (volume : Measure E)} (hk : Integrable k) :
      Integrable fun t ↦ θ t * ⟪φ, k t⟫ :=
    (hk.const_inner φ).bdd_mul hθ.continuous.aestronglyMeasurable (Eventually.of_forall hC)
  -- The forcing term converges, since `θ` is bounded.
  have hforce : Tendsto (fun n ↦ ∫ t, θ t * ⟪φ, K n t⟫) atTop (𝓝 (∫ t, θ t * ⟪φ, G t⟫)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (g := fun n ↦ C * ‖φ‖ * ∫ s, ‖K n s - G s‖) (fun _ ↦ norm_nonneg _)
      (fun n ↦ ?_) (by simpa using hKG'.const_mul (C * ‖φ‖))
    rw [← integral_sub (hint (hK n)) (hint hG)]
    calc ‖∫ t, (θ t * ⟪φ, K n t⟫ - θ t * ⟪φ, G t⟫)‖
        ≤ ∫ t, C * ‖φ‖ * ‖K n t - G t‖ := by
          refine norm_integral_le_of_norm_le (((hK n).sub hG).norm.const_mul _)
            (Eventually.of_forall fun t ↦ ?_)
          rw [← mul_sub, ← inner_sub_right, norm_mul, mul_assoc]
          exact mul_le_mul (hC t) (norm_inner_le_norm _ _) (norm_nonneg _)
            ((norm_nonneg _).trans (hC t))
      _ = C * ‖φ‖ * ∫ t, ‖K n t - G t‖ := integral_const_mul _ _
  have hn (n : ℕ) : ∫ t, deriv (deriv θ) t * ⟪φ, waveDuhamelSolution F f g (K n) t⟫ =
      (∫ t, θ t * ⟪ψ, waveDuhamelSolution F f g (K n) t⟫) + ∫ t, θ t * ⟪φ, K n t⟫ := by
    have h₁ : Integrable fun t ↦ θ t * ⟪ψ, waveDuhamelSolution F f g (K n) t⟫ :=
      (hθ.continuous.mul (continuous_const.inner
        (continuous_waveDuhamelSolution f g (hKc n)))).integrable_of_hasCompactSupport
          hθc.mul_right
    rw [integral_deriv_deriv_mul_inner_waveDuhamelSolution hφψ f g (hKc n) hθ hθc,
      ← integral_add h₁ (hint (hK n))]
    simp only [mul_add]
  have hθ' : ContDiff ℝ 1 (deriv θ) := hθ.deriv' (n := 1)
  exact tendsto_nhds_unique
    ((tendsto_integral_mul_inner_waveDuhamelSolution_of_tendsto f g φ hKc hK hG hKG'
      (hθ'.continuous_deriv le_rfl) hθc.deriv.deriv).congr hn)
    ((tendsto_integral_mul_inner_waveDuhamelSolution_of_tendsto f g ψ hKc hK hG hKG'
      hθ.continuous hθc).add hforce)

/-- A function of time with support in `s` vanishes outside `s`, and so does its second
derivative. -/
private theorem eq_zero_and_deriv_deriv_eq_zero_of_tsupport_subset {θ : ℝ → ℂ} {s : Set ℝ}
    (hθs : tsupport θ ⊆ s) : (∀ t ∉ s, θ t = 0) ∧ ∀ t ∉ s, deriv (deriv θ) t = 0 :=
  ⟨fun _ ht ↦ image_eq_zero_of_notMem_tsupport fun h ↦ ht (hθs h),
    fun _ ht ↦ image_eq_zero_of_notMem_tsupport fun h ↦
      ht (hθs (tsupport_deriv_subset (tsupport_deriv_subset h)))⟩

/-- **The wave equation tested in space and time, for integrable forcing.** Let `a ≤ 0 ≤ b`, let
the forcing `G` be integrable on `[a, b]`, and let `θ` be a `C²` function of time vanishing
outside `[a, b]`. For a test function `φ ∈ L²` with `Δφ = ψ ∈ L²`, the solution
`u(t) = cos (tD) f + D⁻¹ sin (tD) g + ∫₀ᵗ D⁻¹ sin ((t - s)D) G(s) ds` satisfies

`∫ θ''(t) ⟪φ, u(t)⟫ dt = ∫ θ(t) ⟪ψ, u(t)⟫ dt + ∫ θ(t) ⟪φ, G(t)⟫ dt`,

that is `∂ₜ²u - Δu = G` tested against `θ(t) φ(x)`. For continuous forcing and every compactly
supported `θ` this is `TauCeti.integral_deriv_deriv_mul_inner_waveDuhamelSolution`. -/
theorem integral_deriv_deriv_mul_inner_waveDuhamelSolution_of_integrableOn
    (hφψ : Δ (φ : 𝓢'(E, F)) = (ψ : 𝓢'(E, F))) (f g : Lp F 2 (volume : Measure E)) {a b : ℝ}
    (ha : a ≤ 0) (hb : 0 ≤ b) (hG : IntegrableOn G (Set.Icc a b)) {θ : ℝ → ℂ}
    (hθ : ContDiff ℝ 2 θ) (hθab : tsupport θ ⊆ Set.Icc a b) :
    ∫ t, deriv (deriv θ) t * ⟪φ, waveDuhamelSolution F f g G t⟫ =
      (∫ t, θ t * ⟪ψ, waveDuhamelSolution F f g G t⟫) + ∫ t, θ t * ⟪φ, G t⟫ := by
  -- Only the values of `G` on `[a, b]` enter, so `G` may be replaced by `H = 1_{[a, b]} G`.
  set H := (Set.Icc a b).indicator G
  have huH {t : ℝ} (ht : t ∈ Set.Icc a b) :
      waveDuhamelSolution F f g G t = waveDuhamelSolution F f g H t :=
    (waveDuhamelSolution_indicator_Icc f g ha hb ht).symm
  obtain ⟨hθ0, hθ''0⟩ := eq_zero_and_deriv_deriv_eq_zero_of_tsupport_subset hθab
  have key {w X Y : ℝ → ℂ} (hw : ∀ t ∉ Set.Icc a b, w t = 0)
      (hXY : ∀ t ∈ Set.Icc a b, X t = Y t) : ∫ t, w t * X t = ∫ t, w t * Y t := by
    refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    by_cases ht : t ∈ Set.Icc a b
    · simp only [hXY t ht]
    · simp only [hw t ht, zero_mul]
  calc ∫ t, deriv (deriv θ) t * ⟪φ, waveDuhamelSolution F f g G t⟫
      = ∫ t, deriv (deriv θ) t * ⟪φ, waveDuhamelSolution F f g H t⟫ :=
        key hθ''0 fun t ht ↦ by rw [huH ht]
    _ = (∫ t, θ t * ⟪ψ, waveDuhamelSolution F f g H t⟫) + ∫ t, θ t * ⟪φ, H t⟫ :=
        integral_deriv_deriv_mul_inner_waveDuhamelSolution_of_integrable hφψ f g
          (hG.integrable_indicator measurableSet_Icc) hθ
          (isCompact_Icc.of_isClosed_subset (isClosed_tsupport θ) hθab)
    _ = (∫ t, θ t * ⟪ψ, waveDuhamelSolution F f g G t⟫) + ∫ t, θ t * ⟪φ, G t⟫ := by
        congr 1
        · exact key hθ0 fun t ht ↦ by rw [huH ht]
        · exact key hθ0 fun t ht ↦ by rw [show H t = G t from Set.indicator_of_mem ht G]

/-- On `[a, b] ∋ 0`, the solution with forcing integrable on `[a, b]` is bounded by
`‖f‖ + (b - a) ‖g‖ + (b - a) ∫_{[a, b]} ‖G‖`. -/
private theorem norm_waveDuhamelSolution_le_of_integrableOn (f g : Lp F 2 (volume : Measure E))
    {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) (hG : IntegrableOn G (Set.Icc a b)) {t : ℝ}
    (ht : t ∈ Set.Icc a b) :
    ‖waveDuhamelSolution F f g G t‖ ≤
      ‖f‖ + (b - a) * ‖g‖ + (b - a) * ∫ s in Set.Icc a b, ‖G s‖ := by
  have hsub : Set.uIcc 0 t ⊆ Set.Icc a b := Set.uIcc_subset_Icc ⟨ha, hb⟩ ht
  have htT : |t| ≤ b - a := abs_le.2 ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine (norm_waveDuhamelSolution_le_mul_setIntegral f g
    (hG.mono_set hsub).intervalIntegrable).trans ?_
  have := setIntegral_mono_set hG.norm (Eventually.of_forall fun _ ↦ norm_nonneg _)
    (Eventually.of_forall fun x hx ↦ (Set.uIoc_subset_uIcc.trans hsub) hx)
  have : 0 ≤ b - a := by linarith
  gcongr

open Topology in
/-- If solutions `uᵢ` with forcings integrable on `[a, b] ∋ 0` converge to `U` in `L^r` at almost
every time of `[a, b]` and in `L^q([a, b]; L^r_x)`, their pairings with `ϑ(t) χ(x)` converge to
those of `U`, for every continuous `ϑ` vanishing outside `[a, b]`. -/
private theorem tendsto_integral_mul_inner_waveDuhamelSolution_of_tendsto_eLpNorm {ι : Type*}
    {l : Filter ι} [l.IsCountablyGenerated] {q r : ℝ≥0∞} [Fact (1 ≤ r)] (hq : 1 ≤ q) {a b : ℝ}
    (ha : a ≤ 0) (hb : 0 ≤ b) {f g : ι → Lp F 2 (volume : Measure E)}
    {G : ι → ℝ → Lp F 2 (volume : Measure E)} (hG : ∀ i, IntegrableOn (G i) (Set.Icc a b))
    {U : ℝ → Lp F r (volume : Measure E)}
    (hae : ∀ᵐ t ∂volume.restrict (Set.Icc a b), Tendsto (fun i ↦
      eLpNorm (⇑(U t) - ⇑(waveDuhamelSolution F (f i) (g i) (G i) t)) r volume) l (𝓝 0))
    (hlim : Tendsto (fun i ↦ eLpNorm (fun t ↦
      eLpNorm (⇑(U t) - ⇑(waveDuhamelSolution F (f i) (g i) (G i) t)) r volume) q
        (volume.restrict (Set.Icc a b))) l (𝓝 0))
    (χ : 𝓢(E, F)) {ϑ : ℝ → ℂ} (hϑ : Continuous ϑ) (hϑc : HasCompactSupport ϑ)
    (hϑ0 : ∀ t ∉ Set.Icc a b, ϑ t = 0) :
    Tendsto (fun i ↦ ∫ t, ϑ t * ⟪χ.toLp 2, waveDuhamelSolution F (f i) (g i) (G i) t⟫) l
      (𝓝 (∫ t, ϑ t * ∫ x, ⟪χ x, U t x⟫)) := by
  have := (ENNReal.HolderConjugate.conjExponent hq).symm
  have := (ENNReal.HolderConjugate.conjExponent (Fact.out : (1 : ℝ≥0∞) ≤ r)).symm
  have hpair (h : Lp F 2 (volume : Measure E)) : ∫ x, ⟪χ x, h x⟫ = ⟪χ.toLp 2, h⟫ :=
    (L2.toLp_inner_of_ae_eq (χ.memLp 2) Filter.EventuallyEq.rfl).symm
  obtain ⟨C, hC⟩ := hϑ.bounded_above_of_compact_support hϑc
  have hmeas (i : ι) : AEStronglyMeasurable
      (fun t ↦ ⟪χ.toLp 2, waveDuhamelSolution F (f i) (g i) (G i) t⟫)
      (volume.restrict (Set.Icc a b)) :=
    (continuousOn_const.inner (continuousOn_waveDuhamelSolution_of_integrableOn (f i) (g i) ha hb
      (hG i))).aestronglyMeasurable measurableSet_Icc
  -- Both sides are integrals over `[a, b]`, where Hölder's inequality applies.
  have hset (X : ℝ → ℂ) : ∫ t in Set.Icc a b, ϑ t * X t = ∫ t, ϑ t * X t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht ↦ by rw [hϑ0 t ht, zero_mul]
  have hfun : (fun i ↦ ∫ t, ϑ t * ⟪χ.toLp 2, waveDuhamelSolution F (f i) (g i) (G i) t⟫) =
      fun i ↦ ∫ t in Set.Icc a b, ϑ t * ∫ x, ⟪χ x, waveDuhamelSolution F (f i) (g i) (G i) t x⟫ :=
    funext fun i ↦ by rw [hset]; simp_rw [hpair]
  rw [hfun, ← hset fun t ↦ ∫ x, ⟪χ x, U t x⟫]
  refine tendsto_integral_mul_integral_inner_of_tendsto_eLpNorm_eLpNorm_sub
    (p := q.conjExponent) (r := r.conjExponent)
    ((hϑ.memLp_of_hasCompactSupport hϑc).restrict _) (χ.memLp _)
    (ae_of_all _ fun t ↦ Lp.memLp (U t))
    (ae_of_all _ fun t i ↦ MemLp.integrable_inner_of_holderConjugate (q := 2) (q' := 2)
      (χ.memLp 2) (Lp.memLp _)) (fun i ↦ by simp_rw [hpair]; exact hmeas i) (fun i ↦ ?_) hae hlim
  -- The pairings are integrable on `[a, b]`, where the solutions are bounded.
  simp_rw [hpair]
  refine Integrable.of_bound (hϑ.aestronglyMeasurable.mul (hmeas i))
    (C * (‖χ.toLp 2‖ * (‖f i‖ + (b - a) * ‖g i‖ + (b - a) * ∫ s in Set.Icc a b, ‖G i s‖)))
    (ae_restrict_of_forall_mem measurableSet_Icc fun t ht ↦ ?_)
  rw [norm_mul]
  exact mul_le_mul (hC t) ((norm_inner_le_norm _ _).trans
    (by gcongr; exact norm_waveDuhamelSolution_le_of_integrableOn _ _ ha hb (hG i) ht))
    (norm_nonneg _) ((norm_nonneg _).trans (hC t))

open Topology in
/-- **Limits of forced waves in mixed norm solve the forced wave equation.** Let `a ≤ 0 ≤ b` and
let `uᵢ(t) = cos (tD) fᵢ + D⁻¹ sin (tD) gᵢ + ∫₀ᵗ D⁻¹ sin ((t - s)D) Gᵢ(s) ds` be the solutions with
data `fᵢ, gᵢ ∈ L²` and forcings `Gᵢ` integrable on `[a, b]`, indexed along a countably generated
filter, and let `U : ℝ → L^r` with `uᵢ(t) → U(t)` in `L^r` for almost every `t ∈ [a, b]` and
`uᵢ → U` in the mixed norm `L^q([a, b]; L^r_x)`, for some `1 ≤ q, r ≤ ∞`. Then for every Schwartz
function `φ` and every `C²` function `θ` of time vanishing outside `[a, b]`, the forcings tested
against `θ(t) φ(x)` converge to `U` tested against `θ''(t) φ(x) - θ(t) Δφ(x)`:

`∫ θ(t) ⟪φ, Gᵢ(t)⟫ dt → ∫ θ''(t) ∫ ⟪φ(x), U(t)(x)⟫ dx dt - ∫ θ(t) ∫ ⟪Δφ(x), U(t)(x)⟫ dx dt`.

That is, `∂ₜ²U - ΔU` is the limit of the forcings on `(a, b)` in the sense of distributions.
Neither `U(t)` nor any limit of the data or the forcings needs to lie in `L²`. -/
theorem tendsto_integral_mul_inner_of_tendsto_waveDuhamelSolution {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {q r : ℝ≥0∞} [Fact (1 ≤ r)] (hq : 1 ≤ q) {a b : ℝ} (ha : a ≤ 0)
    (hb : 0 ≤ b) {f g : ι → Lp F 2 (volume : Measure E)}
    {G : ι → ℝ → Lp F 2 (volume : Measure E)} (hG : ∀ i, IntegrableOn (G i) (Set.Icc a b))
    {U : ℝ → Lp F r (volume : Measure E)}
    (hae : ∀ᵐ t ∂volume.restrict (Set.Icc a b), Tendsto (fun i ↦
      eLpNorm (⇑(U t) - ⇑(waveDuhamelSolution F (f i) (g i) (G i) t)) r volume) l (𝓝 0))
    (hlim : Tendsto (fun i ↦ eLpNorm (fun t ↦
      eLpNorm (⇑(U t) - ⇑(waveDuhamelSolution F (f i) (g i) (G i) t)) r volume) q
        (volume.restrict (Set.Icc a b))) l (𝓝 0))
    (φ : 𝓢(E, F)) {θ : ℝ → ℂ} (hθ : ContDiff ℝ 2 θ) (hθab : tsupport θ ⊆ Set.Icc a b) :
    Tendsto (fun i ↦ ∫ t, θ t * ⟪φ.toLp 2, G i t⟫) l
      (𝓝 ((∫ t, deriv (deriv θ) t * ∫ x, ⟪φ x, U t x⟫) - ∫ t, θ t * ∫ x, ⟪(Δ φ) x, U t x⟫)) := by
  have hθc : HasCompactSupport θ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport θ) hθab
  have hθ' : ContDiff ℝ 1 (deriv θ) := hθ.deriv' (n := 1)
  obtain ⟨hθ0, hθ''0⟩ := eq_zero_and_deriv_deriv_eq_zero_of_tsupport_subset hθab
  -- Each solution satisfies the equation with its own forcing.
  have hφ : Δ ((φ.toLp 2 : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) =
      (((Δ φ).toLp 2 : Lp F 2 (volume : Measure E)) : 𝓢'(E, F)) := by
    simp
  have heq (i : ι) := integral_deriv_deriv_mul_inner_waveDuhamelSolution_of_integrableOn hφ
    (f i) (g i) ha hb (hG i) hθ hθab
  exact ((tendsto_integral_mul_inner_waveDuhamelSolution_of_tendsto_eLpNorm hq ha hb hG hae hlim
      φ (hθ'.continuous_deriv le_rfl) hθc.deriv.deriv hθ''0).sub
    (tendsto_integral_mul_inner_waveDuhamelSolution_of_tendsto_eLpNorm hq ha hb hG hae hlim (Δ φ)
      hθ.continuous hθc hθ0)).congr fun i ↦ by rw [heq i, add_sub_cancel_left]

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
  -- This is the case `G = 0` of the forced limit, on an interval `[a, b]` containing `0` and the
  -- support of `θ`.
  obtain ⟨a, ha⟩ := hθc.isCompact.bddBelow
  obtain ⟨b, hb⟩ := hθc.isCompact.bddAbove
  have h := tendsto_integral_mul_inner_of_tendsto_waveDuhamelSolution (G := fun _ ↦ 0) hq
    (min_le_right a 0) (le_max_right b 0) (fun _ ↦ integrableOn_zero) (ae_restrict_of_ae hae)
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ zero_le)
      fun _ ↦ eLpNorm_mono_measure _ Measure.restrict_le_self) φ hθ
    fun t ht ↦ ⟨min_le_of_left_le (ha ht), le_max_of_le_left (hb ht)⟩
  simp only [Pi.zero_apply, inner_zero_right, mul_zero, integral_zero] at h
  exact sub_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds h).symm

end Duhamel

end TauCeti
