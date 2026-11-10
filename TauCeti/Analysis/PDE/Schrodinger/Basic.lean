/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.LaplacianSymbol
public import TauCeti.Analysis.Fourier.PhaseGroup

/-!
# The Schrödinger propagator on `L²`

On a finite-dimensional real inner product space `E`, the free Schrödinger equation
`i ∂ₜu + Δu = 0` is solved by the **Schrödinger propagator** `S(t) = exp(itΔ)`. In Mathlib's
normalization of the Fourier transform, `𝓕 f(ξ) = ∫ e^{-2πi⟪x, ξ⟫} f(x) dx`, the Laplacian is the
Fourier multiplier with the real symbol `TauCeti.laplacianSymbol`, `ξ ↦ -4π² ‖ξ‖²`, so `S(t)` is
the unitary operator `exp(itω(D))` of `TauCeti.phasePropagator` with this phase: the Fourier
multiplier on `L²(E, F)` with the unimodular symbol

`ξ ↦ exp(-4π² i t ‖ξ‖²)`.

Its group law, unitarity, strong continuity and commutation with Fourier multipliers are the
general laws of `TauCeti.phasePropagator`, and `TauCeti.phaseGroup E F TauCeti.laplacianSymbol`
is the strongly continuous unitary Schrödinger group. The dispersive estimate
`‖S(t) f‖_∞ ≤ (4π|t|)^{-n/2} ‖f‖₁` is proved in `TauCeti.Analysis.PDE.Schrodinger.Dispersive`.

## Main declarations

* `TauCeti.schrodingerPropagator`: the propagator `S(t)` on `L²(E, F)`.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.2.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable (F) in
/-- The **Schrödinger propagator** `S(t) = exp(itΔ)` on `L²(E, F)`: the Fourier multiplier with
symbol `exp(-4π² i t ‖ξ‖²)`. -/
abbrev schrodingerPropagator (t : ℝ) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp F 2 (volume : Measure E) :=
  phasePropagator F laplacianSymbol t

theorem schrodingerPropagator_def (t : ℝ) :
    schrodingerPropagator F t = phasePropagator (E := E) F laplacianSymbol t :=
  (rfl)

end TauCeti
