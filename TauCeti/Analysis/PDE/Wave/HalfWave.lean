/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fourier.LaplacianSymbol
public import TauCeti.Analysis.Fourier.PhaseGroup
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

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
* `TauCeti.halfWavePropagator_add_apply`, `TauCeti.adjoint_halfWavePropagator` and
  `TauCeti.halfWavePropagator_comp_fourierMultiplierCLM`: the group law, the adjoint
  `W₊(t)* = W₊(-t)` and commutation with Fourier multipliers
  (applied form: `TauCeti.fourierMultiplierCLM_halfWavePropagator_apply`).
* `TauCeti.adjoint_halfWavePropagator_comp_fourierMultiplierCLM` and
  `TauCeti.halfWavePropagator_comp_fourierMultiplierCLM_apply_adjoint`: for `U(t) = W₊(t) T_m`,
  the adjoint `U(t)* = T_{star m} W₊(-t)` and the time pairings
  `U(s) U(t)* = W₊(s - t) T_m T_{star m}`.
* `TauCeti.contDiffOn_phaseSymbol_sqrtNegLaplacianSymbol`: the symbol `exp(2πi t ‖ξ‖)` is smooth
  away from the origin.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.2.
-/

public section

noncomputable section

open scoped ENNReal FourierTransform ContDiff
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

/-- **The group law** `W₊(s + t) = W₊(s) W₊(t)`. -/
theorem halfWavePropagator_add_apply (s t : ℝ) (f : Lp F 2 (volume : Measure E)) :
    halfWavePropagator F (s + t) f = halfWavePropagator F s (halfWavePropagator F t f) :=
  phasePropagator_add_apply _ s t f

/-- The adjoint of `W₊(t)` is `W₊(-t)`. -/
theorem adjoint_halfWavePropagator (t : ℝ) :
    ContinuousLinearMap.adjoint (halfWavePropagator (E := E) F t) = halfWavePropagator F (-t) :=
  adjoint_phasePropagator _ t

/-- `W₊(t)` is a contraction on `L²`. -/
theorem norm_halfWavePropagator_le (t : ℝ) : ‖halfWavePropagator (E := E) F t‖ ≤ 1 :=
  norm_phasePropagator_le _ t

/-- If the symbol `m` is bounded by `B` almost everywhere, then `‖W₊(t) T_m‖ ≤ B`. -/
theorem norm_halfWavePropagator_comp_fourierMultiplierCLM_le {m : Lp ℂ ∞ (volume : Measure E)}
    {B : ℝ} (hm : ∀ᵐ ξ ∂volume, ‖m ξ‖ ≤ B) (t : ℝ) :
    ‖halfWavePropagator F t ∘L Lp.fourierMultiplierCLM F m‖ ≤ B := by
  calc _ ≤ ‖halfWavePropagator (E := E) F t‖ * ‖Lp.fourierMultiplierCLM F m‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * B := by
        gcongr
        · exact norm_halfWavePropagator_le _
        · -- `volume` on `E` is nonzero, so the bound is attained somewhere and `B ≥ 0`.
          have ⟨_, hξ⟩ := hm.exists
          exact (Lp.norm_fourierMultiplierCLM_le m).trans
            (Lp.norm_le_of_ae_bound_top ((norm_nonneg _).trans hξ) hm)
    _ = B := one_mul B

/-- `W₊(t)` commutes with every `L²` Fourier multiplier. -/
theorem halfWavePropagator_comp_fourierMultiplierCLM (t : ℝ) (m : Lp ℂ ∞ (volume : Measure E)) :
    halfWavePropagator F t ∘L Lp.fourierMultiplierCLM F m =
      Lp.fourierMultiplierCLM F m ∘L halfWavePropagator F t :=
  phasePropagator_comp_fourierMultiplierCLM _ t m

/-- `W₊(t)` commutes with every `L²` Fourier multiplier, applied form. -/
theorem fourierMultiplierCLM_halfWavePropagator_apply (t : ℝ) (m : Lp ℂ ∞ (volume : Measure E))
    (f : Lp F 2 (volume : Measure E)) :
    Lp.fourierMultiplierCLM F m (halfWavePropagator F t f) =
      halfWavePropagator F t (Lp.fourierMultiplierCLM F m f) :=
  (ContinuousLinearMap.ext_iff.1 (halfWavePropagator_comp_fourierMultiplierCLM t m) f).symm

/-- The adjoint of `W₊(t) T_m` is `T_{star m} W₊(-t)`. -/
theorem adjoint_halfWavePropagator_comp_fourierMultiplierCLM (t : ℝ)
    (m : Lp ℂ ∞ (volume : Measure E)) :
    ContinuousLinearMap.adjoint (halfWavePropagator F t ∘L Lp.fourierMultiplierCLM F m) =
      Lp.fourierMultiplierCLM F (star m) ∘L halfWavePropagator F (-t) := by
  rw [ContinuousLinearMap.adjoint_comp, Lp.adjoint_fourierMultiplierCLM,
    adjoint_halfWavePropagator]

/-- The adjoint of `W₊(t) T_m` is `T_{star m} W₊(-t)`, applied form. -/
theorem adjoint_halfWavePropagator_comp_fourierMultiplierCLM_apply (t : ℝ)
    (m : Lp ℂ ∞ (volume : Measure E)) (g : Lp F 2 (volume : Measure E)) :
    ContinuousLinearMap.adjoint (halfWavePropagator F t ∘L Lp.fourierMultiplierCLM F m) g =
      Lp.fourierMultiplierCLM F (star m) (halfWavePropagator F (-t) g) := by
  rw [adjoint_halfWavePropagator_comp_fourierMultiplierCLM, ContinuousLinearMap.comp_apply]

/-- The time pairings `U(s) U(t)*` of `U(t) = W₊(t) T_m` are `W₊(s - t) T_m T_{star m}`. -/
theorem halfWavePropagator_comp_fourierMultiplierCLM_apply_adjoint (s t : ℝ)
    (m : Lp ℂ ∞ (volume : Measure E)) (g : Lp F 2 (volume : Measure E)) :
    (halfWavePropagator F s ∘L Lp.fourierMultiplierCLM F m)
        (ContinuousLinearMap.adjoint (halfWavePropagator F t ∘L Lp.fourierMultiplierCLM F m) g) =
      halfWavePropagator F (s - t)
        (Lp.fourierMultiplierCLM F m (Lp.fourierMultiplierCLM F (star m) g)) := by
  rw [adjoint_halfWavePropagator_comp_fourierMultiplierCLM_apply, ContinuousLinearMap.comp_apply,
    fourierMultiplierCLM_halfWavePropagator_apply, fourierMultiplierCLM_halfWavePropagator_apply,
    ← halfWavePropagator_add_apply, ← sub_eq_add_neg]

/-- On the Fourier side, `W₊(t)` is pointwise multiplication by `exp(2πi t ‖ξ‖)`, almost
everywhere. -/
theorem coeFn_fourier_halfWavePropagator (t : ℝ) (f : Lp F 2 (volume : Measure E)) :
    𝓕 (halfWavePropagator F t f) =ᵐ[volume]
      fun ξ ↦ cexp (((2 * π * t * ‖ξ‖ : ℝ) : ℂ) * I) • 𝓕 f ξ := by
  filter_upwards [coeFn_fourier_phasePropagator sqrtNegLaplacianSymbol t f] with ξ h
  rw [halfWavePropagator_def, h, phaseSymbol_apply, sqrtNegLaplacianSymbol_apply]
  congr 4
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The half-wave symbol `exp(2πi t ‖ξ‖)` is smooth away from the origin, where the norm is. -/
theorem contDiffOn_phaseSymbol_sqrtNegLaplacianSymbol {n : WithTop ℕ∞} (t : ℝ) :
    ContDiffOn ℝ n (phaseSymbol (sqrtNegLaplacianSymbol (E := E)) t) {0}ᶜ := fun ξ hξ ↦ by
  have h : phaseSymbol (sqrtNegLaplacianSymbol (E := E)) t =
      fun η ↦ cexp (((t * (2 * π * ‖η‖) : ℝ) : ℂ) * I) :=
    funext fun η ↦ by rw [phaseSymbol_apply, sqrtNegLaplacianSymbol_apply]
  rw [h]
  exact ((ofRealCLM.contDiff.contDiffAt.comp ξ (contDiffAt_const.mul (contDiffAt_const.mul
    (contDiffAt_norm ℝ (Set.mem_compl_singleton_iff.1 hξ))))).mul
      contDiffAt_const).cexp.contDiffWithinAt

/-- The backward half-wave propagator `W₊(-t)` is `W₋(t) = exp(-itD)`, the Fourier multiplier with
the phase `-2π ‖·‖`. -/
theorem halfWavePropagator_neg (t : ℝ) :
    halfWavePropagator F (-t) = phasePropagator (E := E) F (-sqrtNegLaplacianSymbol) t := by
  rw [halfWavePropagator_def, phasePropagator_neg]

end TauCeti
