/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Distribution.SchwartzSpace.LinearIsometry
public import TauCeti.Analysis.Distribution.TemperedDistribution.ChangeOfVariables
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Pullback of tempered distributions along linear isometries

Let `A` be a linear isometry of a finite-dimensional real inner product space `E`. The pullback
`A^* T = T ∘ A` of tempered distributions along `A` (`TemperedDistribution.compCLM`) carries the
Fourier multiplier with symbol `g` to the one with symbol `g ∘ A`. So it commutes with every
Fourier multiplier whose symbol is invariant under `A`, in particular with the Bessel potentials
`J^s`, whose symbol `⟨ξ⟩ ^ s` depends only on `‖ξ‖`. Since `A` preserves Lebesgue
measure, it pulls the distribution of `u ∈ Lᵖ` back to the distribution of the `Lᵖ` function
`u ∘ A`, of the same norm. Together these make `A^*` an isometry of every Bessel-potential space
`H^{s,p}`.

## Main declarations

* `TemperedDistribution.fourierMultiplierCLM_compCLM_linearIsometryEquiv`:
  `T_{g ∘ A} (A^* T) = A^* (T_g T)`.
* `TemperedDistribution.besselPotential_compCLM_linearIsometryEquiv`: `J^s (A^* T) = A^* (J^s T)`.
* `TemperedDistribution.compCLM_linearIsometryEquiv_toTemperedDistribution`: `A^*` on `Lᵖ`
  functions is composition with `A` (`Lp.compMeasurePreserving`).
-/

public section

noncomputable section

open MeasureTheory FourierTransform
open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F]

namespace TemperedDistribution

/-- The pullback of tempered distributions along a linear isometry `A` intertwines Fourier
multipliers, carrying the symbol `g` to `g ∘ A`: `T_{g ∘ A} (A^* T) = A^* (T_g T)`. In particular
a Fourier multiplier whose symbol is invariant under `A` commutes with the pullback along `A`. -/
theorem fourierMultiplierCLM_compCLM_linearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E) (g : E → ℂ)
    (T : 𝓢'(E, F)) :
    fourierMultiplierCLM F (g ∘ A) (compCLM F A.toLinearEquiv.toEquiv
        A.toLinearEquiv.hasTemperateGrowth_toEquiv
        A.toLinearEquiv.hasTemperateGrowth_toEquiv_symm T) =
      compCLM F A.toLinearEquiv.toEquiv A.toLinearEquiv.hasTemperateGrowth_toEquiv
        A.toLinearEquiv.hasTemperateGrowth_toEquiv_symm (fourierMultiplierCLM F g T) := by
  by_cases hg : g.HasTemperateGrowth
  · have hg' : g ∘ A.symm.toContinuousLinearEquiv.symm = g ∘ A := funext fun x ↦ by simp
    ext u
    simp only [fourierMultiplierCLM_apply_apply, compCLM_apply_apply,
      SchwartzMap.pushforwardCLM_linearIsometryEquiv,
      SchwartzMap.fourier_compCLMOfContinuousLinearEquiv_linearIsometryEquiv,
      SchwartzMap.fourierInv_compCLMOfContinuousLinearEquiv_linearIsometryEquiv,
      SchwartzMap.smulLeftCLM_compCLMOfContinuousLinearEquiv ℂ hg, hg']
  · have hgA : ¬(g ∘ A).HasTemperateGrowth :=
      A.toContinuousLinearEquiv.hasTemperateGrowth_comp_iff.not.mpr hg
    ext u
    simp [fourierMultiplierCLM_apply_apply, SchwartzMap.smulLeftCLM, hg, hgA]

/-- The Bessel potentials `J^s` commute with the pullback of tempered distributions along a linear
isometry. -/
@[simp]
theorem besselPotential_compCLM_linearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E) (s : ℝ) (T : 𝓢'(E, F)) :
    besselPotential E F s (compCLM F A.toLinearEquiv.toEquiv
        A.toLinearEquiv.hasTemperateGrowth_toEquiv
        A.toLinearEquiv.hasTemperateGrowth_toEquiv_symm T) =
      compCLM F A.toLinearEquiv.toEquiv A.toLinearEquiv.hasTemperateGrowth_toEquiv
        A.toLinearEquiv.hasTemperateGrowth_toEquiv_symm (besselPotential E F s T) := by
  have h := fourierMultiplierCLM_compCLM_linearIsometryEquiv A
    (fun x ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) T
  rwa [show (fun x ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ)) ∘ A =
    fun x ↦ (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) from funext fun x ↦ by simp] at h

/-- The pullback along a linear isometry `A` of the distribution of `u ∈ Lᵖ` is the distribution of
the `Lᵖ` function `u ∘ A`. -/
@[simp]
theorem compCLM_linearIsometryEquiv_toTemperedDistribution [CompleteSpace F] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (A : E ≃ₗᵢ[ℝ] E) (u : Lp F p (volume : Measure E)) :
    compCLM F A.toLinearEquiv.toEquiv A.toLinearEquiv.hasTemperateGrowth_toEquiv
        A.toLinearEquiv.hasTemperateGrowth_toEquiv_symm (u : 𝓢'(E, F)) =
      (Lp.compMeasurePreserving A A.measurePreserving u : 𝓢'(E, F)) := by
  ext f
  rw [compCLM_apply_apply, Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply,
    SchwartzMap.integral_pushforwardCLM_smul]
  exact integral_congr_ae ((Lp.coeFn_compMeasurePreserving u A.measurePreserving).mono
    fun x hx ↦ by
      simp only [hx, Function.comp_apply, LinearEquiv.coe_toEquiv,
        LinearIsometryEquiv.coe_toLinearEquiv])

end TemperedDistribution
