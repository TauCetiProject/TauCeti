/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.LaplacianSymbol
public import TauCeti.Analysis.Fourier.PhaseGroup

/-!
# The half-wave propagators on `L²`

On a finite-dimensional real inner product space `E`, let `D = √(-Δ)` be the Fourier multiplier
with symbol `TauCeti.sqrtNegLaplacianSymbol`, `ξ ↦ 2π ‖ξ‖`, in Mathlib's normalization of the
Fourier transform. The wave operator factors as `∂ₜ² - Δ = (∂ₜ - iD)(∂ₜ + iD)`, and the
**half-wave propagators** `W±(t) = exp(±itD)` solve the half-wave equations `∂ₜu = ±iDu`. They
are the unitary operators `exp(itω(D))` of `TauCeti.phasePropagator` with the phases
`ω = ±2π ‖·‖`: the Fourier multipliers on `L²(E, F)` with the unimodular symbols

`ξ ↦ exp(±2πi t ‖ξ‖)`.

This file names `W₊(t) = TauCeti.halfWavePropagator F t`; reversing the phase reverses time, so
`W₋(t) = W₊(-t)` (`TauCeti.halfWavePropagator_neg`). The group law, unitarity, strong continuity
and commutation with Fourier multipliers are the general laws of `TauCeti.phasePropagator`, and
`TauCeti.phaseGroup E F TauCeti.sqrtNegLaplacianSymbol` is the strongly continuous unitary
half-wave group. Unlike the Schrödinger propagator, `W±(t)` is not bounded from `L¹` to `L^∞`
for `t ≠ 0`: its dispersive estimate `‖W±(t) P_j f‖_∞ ≲ 2^{jn} (1 + 2^j |t|)^{-(n-1)/2} ‖f‖₁` is
stated for the frequency-localized pieces `P_j f`, whose Fourier transforms live on the dyadic
annuli `‖ξ‖ ≈ 2^j` (Tao, Section 2.2).

## Main declarations

* `TauCeti.halfWavePropagator`: the propagator `W₊(t) = exp(itD)` on `L²(E, F)`.
* `TauCeti.coeFn_fourier_halfWavePropagator`: `𝓕 (W₊(t) f) = exp(2πi t ‖·‖) • 𝓕 f`.
* `TauCeti.halfWavePropagator_neg`: `W₊(-t) = W₋(t)`, the multiplier with phase `-2π ‖·‖`.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.2.
-/

public section

noncomputable section

open scoped FourierTransform
open MeasureTheory Complex Real

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable (F) in
/-- The **half-wave propagator** `W₊(t) = exp(itD)` on `L²(E, F)`, `D = √(-Δ)`: the Fourier
multiplier with symbol `exp(2πi t ‖ξ‖)`. -/
abbrev halfWavePropagator (t : ℝ) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  phasePropagator F sqrtNegLaplacianSymbol t

theorem halfWavePropagator_def (t : ℝ) :
    halfWavePropagator F t = phasePropagator (E := E) F sqrtNegLaplacianSymbol t :=
  (rfl)

/-- On the Fourier side, `W₊(t)` is pointwise multiplication by `exp(2πi t ‖ξ‖)`, almost
everywhere. -/
theorem coeFn_fourier_halfWavePropagator (t : ℝ) (f : Lp F 2 (volume : Measure E)) :
    𝓕 (halfWavePropagator F t f) =ᵐ[volume]
      fun ξ ↦ cexp (((2 * π * t * ‖ξ‖ : ℝ) : ℂ) * I) • 𝓕 f ξ := by
  filter_upwards [coeFn_fourier_phasePropagator sqrtNegLaplacianSymbol t f] with ξ h
  rw [halfWavePropagator_def, h, phaseSymbol_apply, sqrtNegLaplacianSymbol_apply]
  congr 4
  ring

/-- The backward half-wave propagator `W₊(-t)` is `W₋(t) = exp(-itD)`, the Fourier multiplier with
the phase `-2π ‖·‖`. -/
theorem halfWavePropagator_neg (t : ℝ) :
    halfWavePropagator F (-t) = phasePropagator (E := E) F (-sqrtNegLaplacianSymbol) t := by
  rw [halfWavePropagator_def, phasePropagator_neg]

end TauCeti
