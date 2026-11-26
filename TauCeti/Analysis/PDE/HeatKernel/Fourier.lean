/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import TauCeti.Analysis.Fourier.L2Multiplier
public import TauCeti.Analysis.PDE.HeatKernel.Generator
public import TauCeti.Analysis.Semigroups.Rescale

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
* `TauCeti.coeFn_fourier_heatSemigroup_rescale` and
  `TauCeti.eq_heatSemigroup_rescale_of_coeFn_fourier`: the heat semigroup run at speed `c`,
  `t ↦ e^{c t Δ}`, is the Fourier multiplier semigroup with symbol `exp(-4π² c t ‖ξ‖²)`, and it is
  the only C₀-semigroup on `L²` with this symbol.
* `TauCeti.generator_eq_smul_weakLaplacianLp_of_coeFn_fourier`: a C₀-semigroup on `L²` with
  symbol `exp(-σ t ‖ξ‖²)`, `σ > 0`, has generator `σ (2π)⁻² Δ`.

## The normalization of the symbol

The Laplacian has symbol `-4π² ‖ξ‖²` in this normalization of the Fourier transform, so the
generator of a multiplier semigroup is read off from the derivative of its symbol at `t = 0`. A
model of the heat flow with the symbol `exp(-t ‖ξ‖²)`, the natural one for the normalization
`∫ e^{-i⟪x, ξ⟫} f(x) dx`, is the heat semigroup at speed `(2π)⁻²`: its generator is `(2π)⁻² Δ`,
not `Δ` (`TauCeti.generator_eq_smul_weakLaplacianLp_of_coeFn_fourier` at `σ = 1`). Confusing the
two normalizations changes the generator by the factor `4π²`.

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

/-- **The rescaled heat semigroup on `L²` is a Fourier multiplier.** The heat semigroup run at
speed `c`, `t ↦ e^{c t Δ}`, has symbol `exp(-4π² c t ‖ξ‖²)`: for `f ∈ L²(E; F)`, the `L²` Fourier
transform of `e^{c t Δ} f` is almost everywhere `ξ ↦ exp(-4π² c t ‖ξ‖²) • 𝓕 f ξ`. -/
theorem coeFn_fourier_heatSemigroup_rescale (c t : ℝ≥0) (f : Lp F 2 (volume : Measure E)) :
    ⇑(𝓕 ((heatSemigroup (p := 2) ENNReal.ofNat_ne_top).rescale c t f) :
        Lp F 2 (volume : Measure E)) =ᵐ[volume]
      fun ξ ↦ Real.exp (-(4 * π ^ 2 * c * t * ‖ξ‖ ^ 2)) •
        (𝓕 f : Lp F 2 (volume : Measure E)) ξ := by
  rw [Semigroups.StronglyContinuousSemigroup.rescale_apply,
    Semigroups.ContractionSemigroup.toStronglyContinuousSemigroup_apply]
  filter_upwards [coeFn_fourier_heatSemigroup (c * t) f] with ξ hξ
  rw [hξ, NNReal.coe_mul, ← mul_assoc]

/-- **A C₀-semigroup on `L²` is determined by its Fourier symbol.** If every operator `T t` of a
C₀-semigroup on `L²(E; F)` is the Fourier multiplier with symbol `exp(-4π² c t ‖ξ‖²)`, then `T` is
the heat semigroup run at speed `c`, `t ↦ e^{c t Δ}`. -/
theorem eq_heatSemigroup_rescale_of_coeFn_fourier {c : ℝ≥0}
    {T : Semigroups.StronglyContinuousSemigroup (Lp F 2 (volume : Measure E))}
    (hT : ∀ (t : ℝ≥0) (f : Lp F 2 (volume : Measure E)),
      ⇑(𝓕 (T t f) : Lp F 2 (volume : Measure E)) =ᵐ[volume]
        fun ξ ↦ Real.exp (-(4 * π ^ 2 * c * t * ‖ξ‖ ^ 2)) •
          (𝓕 f : Lp F 2 (volume : Measure E)) ξ) :
    T = (heatSemigroup (p := 2) ENNReal.ofNat_ne_top).rescale c := by
  refine Semigroups.StronglyContinuousSemigroup.ext fun t => ContinuousLinearMap.ext fun f => ?_
  -- The two vectors have the same `L²` Fourier transform, and the Fourier transform is injective.
  have h : (𝓕 (T t f) : Lp F 2 (volume : Measure E)) =
      𝓕 ((heatSemigroup (p := 2) ENNReal.ofNat_ne_top).rescale c t f) :=
    Lp.ext ((hT t f).trans (coeFn_fourier_heatSemigroup_rescale c t f).symm)
  simpa using congrArg 𝓕⁻ h

/-- **The generator of a heat flow with symbol `exp(-σ t ‖ξ‖²)`.** If every operator `T t` of a
C₀-semigroup on `L²(E; F)` is the Fourier multiplier with symbol `exp(-σ t ‖ξ‖²)`, `σ > 0`, then
the generator of `T` is `σ (2π)⁻² Δ`, with `Δ` the Laplacian in the sense of distributions on its
domain `{f ∈ L² : Δf ∈ L²}`. At `σ = 1` this is the semigroup with symbol `exp(-t ‖ξ‖²)`, whose
generator is `(2π)⁻² Δ`; the heat semigroup `e^{tΔ}` is the case `σ = 4π²`. -/
theorem generator_eq_smul_weakLaplacianLp_of_coeFn_fourier {σ : ℝ} (hσ : 0 < σ)
    {T : Semigroups.StronglyContinuousSemigroup (Lp F 2 (volume : Measure E))}
    (hT : ∀ (t : ℝ≥0) (f : Lp F 2 (volume : Measure E)),
      ⇑(𝓕 (T t f) : Lp F 2 (volume : Measure E)) =ᵐ[volume]
        fun ξ ↦ Real.exp (-(σ * t * ‖ξ‖ ^ 2)) • (𝓕 f : Lp F 2 (volume : Measure E)) ξ) :
    T.generator = (σ / (2 * π) ^ 2) • weakLaplacianLp E F 2 := by
  -- `T` is the heat semigroup run at speed `c = σ / (2π)²`.
  have hc_coe : ((σ / (2 * π) ^ 2).toNNReal : ℝ) = σ / (2 * π) ^ 2 :=
    Real.coe_toNNReal _ (by positivity)
  have hc : (σ / (2 * π) ^ 2).toNNReal ≠ 0 := (Real.toNNReal_pos.2 (by positivity)).ne'
  have hcσ : 4 * π ^ 2 * ((σ / (2 * π) ^ 2).toNNReal : ℝ) = σ := by
    rw [hc_coe]
    field_simp
    ring
  rw [eq_heatSemigroup_rescale_of_coeFn_fourier (T := T) (c := (σ / (2 * π) ^ 2).toNNReal)
      (by simpa only [hcσ] using hT),
    Semigroups.StronglyContinuousSemigroup.rescale_generator _ hc,
    generator_heatSemigroup_eq_weakLaplacianLp, hc_coe]

end TauCeti
