/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import TauCeti.Analysis.PDE.HeatKernel.Semigroup
import TauCeti.Analysis.Fourier.LpSpace
import TauCeti.MeasureTheory.Function.Lp.Operator.Multiplication

/-!
# The heat semigroup on `L²` as a Fourier multiplier

On a finite-dimensional real inner product space `E`, the heat semigroup `e^{tΔ}` on `L²(E; F)`,
with values in a complex Hilbert space `F`, is the Fourier multiplier with symbol
`exp(-4π² t ‖ξ‖²)`:

`𝓕 (e^{tΔ} f) ξ = exp(-4π² t ‖ξ‖²) • 𝓕 f ξ` for almost every `ξ`.

Here `𝓕` is Mathlib's Fourier transform on `L²` (`MeasureTheory.Lp.fourierTransformₗᵢ`), in the
normalization `𝓕 f(ξ) = ∫ e^{-2πi⟪x, ξ⟫} f(x) dx`. The derivative of the symbol at `t = 0` is
`-4π² ‖ξ‖²`, the symbol of the Laplacian `Δ` in this normalization.

## Main declarations

* `TauCeti.coeFn_fourier_heatSemigroup`: the Fourier representation of the heat semigroup on
  `L²`.

## The argument

For an integrable `f`, the Fourier integral of `K_t ⋆ f` is `exp(-4π² t ‖ξ‖²) • 𝓕 f ξ`
(`TauCeti.fourier_heatKernel_convolution`). On Schwartz functions, which are integrable and
square integrable, the `L²` Fourier transform is the Fourier integral
(`MeasureTheory.Integrable.coeFn_fourier_toLp`), so the identity holds there. Both sides are
continuous in `f ∈ L²`, the right-hand side being a bounded multiplication operator
(`BoundedContinuousFunction.mulLp`), and Schwartz functions are dense in `L²`.

## References

* L. C. Evans, *Partial Differential Equations*, Section 4.3.1.
* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Chapter II, 2.12 (the diffusion semigroup).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Real
open scoped BoundedContinuousFunction ENNReal NNReal FourierTransform Convolution

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- **The heat semigroup on `L²` is a Fourier multiplier.** For `f ∈ L²(E; F)`, the `L²`
Fourier transform of `e^{tΔ} f` is almost everywhere `ξ ↦ exp(-4π² t ‖ξ‖²) • 𝓕 f ξ`. -/
theorem coeFn_fourier_heatSemigroup (hp : (2 : ℝ≥0∞) ≠ ∞) (t : ℝ≥0)
    (f : Lp F 2 (volume : Measure E)) :
    ⇑(𝓕 (heatSemigroup hp t f) : Lp F 2 (volume : Measure E)) =ᵐ[volume]
      fun ξ ↦ Real.exp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) • (𝓕 f : Lp F 2 (volume : Measure E)) ξ := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have ht' : 0 < (t : ℝ) := by positivity
  -- The symbol, as a bounded continuous operator-valued function.
  let m : E →ᵇ (F →L[ℂ] F) := .ofNormedAddCommGroup
    (fun ξ ↦ (Real.exp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) : ℂ) • ContinuousLinearMap.id ℂ F)
    (by fun_prop) 1 fun ξ ↦ by
      calc _ ≤ ‖(Real.exp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) : ℂ)‖ * ‖ContinuousLinearMap.id ℂ F‖ :=
            norm_smul_le _ _
        _ ≤ 1 * 1 := by
            gcongr
            · rw [Complex.norm_real, Real.norm_of_nonneg (exp_pos _).le, exp_le_one_iff,
                neg_nonpos]
              positivity
            · exact ContinuousLinearMap.norm_id_le
        _ = 1 := one_mul 1
  have hm (ξ : E) (v : F) : m ξ v = Real.exp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) • v := by
    rw [← Complex.coe_smul]
    simp [m]
  -- Both sides are continuous in `f`, and they agree on the dense set of Schwartz functions.
  have key : (fun f : Lp F 2 (volume : Measure E) ↦
      (𝓕 (heatSemigroup hp t f) : Lp F 2 (volume : Measure E))) =
      fun f ↦ m.mulLp volume 2 hp (𝓕 f) := by
    refine (SchwartzMap.denseRange_toLpCLM (F := F) (E := E) hp).equalizer (by fun_prop)
      (by fun_prop) (funext fun φ ↦ ?_)
    simp only [Function.comp_apply, SchwartzMap.toLpCLM_apply]
    have hφ : MemLp (φ : E → F) 2 := φ.memLp 2
    have hφL : φ.toLp 2 = hφ.toLp φ := Lp.ext ((φ.coeFn_toLp 2).trans hφ.coeFn_toLp.symm)
    have hconv := heatSemigroup_ae_eq_convolution hp ht hφ
    have hh₁ : Integrable (heatKernel t ⋆ (φ : E → F)) :=
      (integrable_heatKernel ht').integrable_convolution _ φ.integrable
    have hh₂ : MemLp (heatKernel t ⋆ (φ : E → F)) 2 := (Lp.memLp _).ae_eq hconv
    have hS : heatSemigroup hp t (φ.toLp 2) = hh₂.toLp _ :=
      Lp.ext (hφL ▸ hconv.trans hh₂.coeFn_toLp.symm)
    symm
    rw [BoundedContinuousFunction.mulLp_eq_iff, hS]
    filter_upwards [φ.integrable.coeFn_fourier_toLp hφ, hh₁.coeFn_fourier_toLp hh₂]
      with ξ hξ hhξ
    rw [hm, hφL, hξ, hhξ, fourier_heatKernel_convolution ht' φ.integrable]
  filter_upwards [congrFun key f ▸ m.coeFn_mulLp hp (𝓕 f)] with ξ hξ
  rw [hξ, hm]

end TauCeti
