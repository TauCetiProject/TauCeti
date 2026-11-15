/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import TauCeti.Analysis.Fourier.L2Multiplier
public import TauCeti.Analysis.PDE.HeatKernel.Semigroup

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

* `TauCeti.heatSemigroup_eq_fourierMultiplierCLM`: on `L²`, `e^{tΔ}` is the multiplier
  `MeasureTheory.Lp.fourierMultiplierCLM` with symbol `exp(-4π² t ‖ξ‖²)`.
* `TauCeti.coeFn_fourier_heatSemigroup`: the Fourier representation of the heat semigroup on
  `L²`.

## The argument

For `t > 0` the heat semigroup is convolution with the integrable heat kernel `K_t`, and on `L²`
convolution with an integrable kernel `k` is the Fourier multiplier with symbol `𝓕 k`
(`TauCeti.convolutionLp_eq_fourierMultiplierCLM`, `TauCeti.coeFn_fourier_convolutionLp`).
The symbol of `K_t` is `exp(-4π² t ‖ξ‖²)` (`TauCeti.fourier_heatKernel`). At `t = 0` the
semigroup is the identity, the multiplier with constant symbol `1`.

## References

* L. C. Evans, *Partial Differential Equations*, Section 4.3.1.
* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Chapter II, 2.12 (the diffusion semigroup).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Real
open scoped ENNReal NNReal FourierTransform

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- **The heat semigroup on `L²` is a Fourier multiplier.** If the symbol `m ∈ L^∞` is almost
everywhere `ξ ↦ exp(-4π² t ‖ξ‖²)`, then `e^{tΔ}` on `L²(E; F)` is the multiplier with symbol
`m`. -/
theorem heatSemigroup_eq_fourierMultiplierCLM (t : ℝ≥0) {m : Lp ℂ ∞ (volume : Measure E)}
    (hm : m =ᵐ[volume] fun ξ ↦ (Real.exp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) : ℂ)) :
    (heatSemigroup (p := 2) ENNReal.ofNat_ne_top t :
        Lp F 2 (volume : Measure E) →L[ℝ] Lp F 2 (volume : Measure E)) =
      (Lp.fourierMultiplierCLM F m).restrictScalars ℝ := by
  rcases eq_or_ne t 0 with rfl | ht
  · -- At time `0` the symbol is the constant `1`.
    rw [heatSemigroup_zero, Lp.fourierMultiplierCLM_of_ae_eq_const (c := 1) (by simpa using hm)]
    ext1 f
    simp
  have ht' : 0 < (t : ℝ) := by positivity
  rw [heatSemigroup_apply _ ht]
  exact convolutionLp_eq_fourierMultiplierCLM (integrable_heatKernel ht')
    (hm.trans (ae_of_all _ fun ξ ↦ (fourier_heatKernel ht' ξ).symm))

/-- **The Fourier transform of the heat semigroup on `L²`.** For `f ∈ L²(E; F)`, the `L²`
Fourier transform of `e^{tΔ} f` is almost everywhere `ξ ↦ exp(-4π² t ‖ξ‖²) • 𝓕 f ξ`. -/
theorem coeFn_fourier_heatSemigroup (t : ℝ≥0) (f : Lp F 2 (volume : Measure E)) :
    ⇑(𝓕 (heatSemigroup (p := 2) ENNReal.ofNat_ne_top t f) :
        Lp F 2 (volume : Measure E)) =ᵐ[volume]
      fun ξ ↦ Real.exp (-(4 * π ^ 2 * t * ‖ξ‖ ^ 2)) • (𝓕 f : Lp F 2 (volume : Measure E)) ξ := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  have ht' : 0 < (t : ℝ) := by positivity
  rw [heatSemigroup_apply _ ht]
  filter_upwards [coeFn_fourier_convolutionLp (integrable_heatKernel ht') f] with ξ hξ
  rw [hξ, fourier_heatKernel ht', Complex.coe_smul]

end TauCeti
