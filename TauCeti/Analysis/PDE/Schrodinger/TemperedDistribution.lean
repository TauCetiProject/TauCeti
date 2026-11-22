/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Schrodinger.Basic
public import TauCeti.Analysis.Distribution.TemperedDistribution.LittlewoodPaley
public import Mathlib.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Fourier.L2Multiplier

/-!
# The Schrödinger propagator on tempered distributions

On a finite-dimensional real inner product space `E`, the Schrödinger propagator
`S(t) = exp(itΔ)` is the Fourier multiplier with the unimodular symbol
`exp(-4π² i t ‖ξ‖²)` (`TauCeti.phaseSymbol TauCeti.laplacianSymbol t`). This symbol has temperate
growth, so `S(t)` is a continuous linear operator on all tempered distributions
(`TemperedDistribution.schrodingerPropagator`). Formally, `t ↦ S(t) u` solves the free
Schrödinger equation `i ∂ₜu + Δu = 0` with initial value `u` in `𝓢'`; the time derivative is not
proved here. On `L²` it is the unitary propagator `TauCeti.schrodingerPropagator`
(`TemperedDistribution.schrodingerPropagator_toTemperedDistribution`).

Since Fourier multipliers with symbols of temperate growth commute, `S(t)` commutes with every
such multiplier, in particular with the directional derivatives, the Laplacian, the Bessel
potentials `J^s` and the Littlewood–Paley blocks `Δⱼ`. Commuting with `J^s` and preserving `L²`,
it preserves every Bessel-potential space `H^{s,2}`
(`TemperedDistribution.MemSobolev.schrodingerPropagator`). These commutations transport the
estimates for `S(t)` on `L²`, such as the Strichartz estimates, to derivatives, to the Sobolev
scale and to the dyadic blocks of the solution.

## Main declarations

* `TemperedDistribution.schrodingerPropagator`: the propagator `S(t)` on `𝓢'(E, F)`.
* `TemperedDistribution.schrodingerPropagator_zero`,
  `TemperedDistribution.schrodingerPropagator_schrodingerPropagator_apply`: the group law.
* `TemperedDistribution.schrodingerPropagator_toTemperedDistribution`: agreement with the
  propagator on `L²`.
* `TemperedDistribution.schrodingerPropagator_fourierMultiplierCLM_comm`,
  `TemperedDistribution.lineDerivOp_schrodingerPropagator`,
  `TemperedDistribution.laplacian_schrodingerPropagator`,
  `TemperedDistribution.besselPotential_schrodingerPropagator`,
  `TemperedDistribution.littlewoodPaleyBlock_schrodingerPropagator`: commutation with Fourier
  multipliers, derivatives, the Laplacian, Bessel potentials and Littlewood–Paley blocks.
* `TemperedDistribution.MemSobolev.schrodingerPropagator`: `S(t)` preserves `H^{s,2}`.

## References

* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Sections 2.1 and 2.2.
-/

public section

noncomputable section

open MeasureTheory
open scoped SchwartzMap LineDeriv Laplacian

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F]

namespace TemperedDistribution

section NormedSpace

variable [NormedSpace ℂ F]

variable (E F) in
/-- **The Schrödinger propagator** `S(t) = exp(itΔ)` on tempered distributions: the Fourier
multiplier with symbol `exp(-4π² i t ‖ξ‖²)`. On `L²` it is the unitary propagator
`TauCeti.schrodingerPropagator`
(`TemperedDistribution.schrodingerPropagator_toTemperedDistribution`). -/
def schrodingerPropagator (t : ℝ) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  fourierMultiplierCLM F (TauCeti.phaseSymbol TauCeti.laplacianSymbol t)

/-- Unfolding `TemperedDistribution.schrodingerPropagator`. -/
theorem schrodingerPropagator_eq_fourierMultiplierCLM (t : ℝ) :
    schrodingerPropagator E F t =
      fourierMultiplierCLM F (TauCeti.phaseSymbol TauCeti.laplacianSymbol t) :=
  (rfl)

variable (E F) in
/-- At time `0` the Schrödinger propagator is the identity. -/
@[simp]
theorem schrodingerPropagator_zero : schrodingerPropagator E F 0 = ContinuousLinearMap.id ℂ _ := by
  have h : TauCeti.phaseSymbol TauCeti.laplacianSymbol 0 = fun _ : E ↦ (1 : ℂ) :=
    funext (TauCeti.phaseSymbol_zero _)
  rw [schrodingerPropagator, h, fourierMultiplierCLM_const, one_smul]

/-- **The group law** `S(t) S(s) = S(s + t)` on tempered distributions. -/
@[simp]
theorem schrodingerPropagator_schrodingerPropagator_apply (s t : ℝ) (u : 𝓢'(E, F)) :
    schrodingerPropagator E F t (schrodingerPropagator E F s u) =
      schrodingerPropagator E F (s + t) u := by
  rw [schrodingerPropagator, schrodingerPropagator, schrodingerPropagator,
    fourierMultiplierCLM_fourierMultiplierCLM_apply
      (TauCeti.hasTemperateGrowth_phaseSymbol_laplacianSymbol s)
      (TauCeti.hasTemperateGrowth_phaseSymbol_laplacianSymbol t)]
  congr 2
  funext ξ
  rw [Pi.mul_apply, TauCeti.phaseSymbol_add]

/-- The group law `S(t) ∘ S(s) = S(s + t)` as an identity of operators. -/
theorem schrodingerPropagator_compL_schrodingerPropagator (s t : ℝ) :
    schrodingerPropagator E F t ∘L schrodingerPropagator E F s =
      schrodingerPropagator E F (s + t) := by
  ext1 u
  exact schrodingerPropagator_schrodingerPropagator_apply s t u

/-! ### Commutation with Fourier multipliers -/

/-- **`S(t)` commutes with every Fourier multiplier** whose symbol has temperate growth. -/
theorem schrodingerPropagator_fourierMultiplierCLM_comm {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (t : ℝ) (u : 𝓢'(E, F)) :
    schrodingerPropagator E F t (fourierMultiplierCLM F g u) =
      fourierMultiplierCLM F g (schrodingerPropagator E F t u) := by
  have hσ := TauCeti.hasTemperateGrowth_phaseSymbol_laplacianSymbol (E := E) t
  rw [schrodingerPropagator, fourierMultiplierCLM_fourierMultiplierCLM_apply hg hσ,
    fourierMultiplierCLM_fourierMultiplierCLM_apply hσ hg, mul_comm]

/-- `S(t)` commutes with the directional derivatives: `∂_m (S(t) u) = S(t) (∂_m u)`. -/
theorem lineDerivOp_schrodingerPropagator (m : E) (t : ℝ) (u : 𝓢'(E, F)) :
    ∂_{m} (schrodingerPropagator E F t u) = schrodingerPropagator E F t (∂_{m} u) := by
  rw [lineDeriv_eq_fourierMultiplierCLM, lineDeriv_eq_fourierMultiplierCLM,
    ContinuousLinearMap.map_smul_of_tower,
    schrodingerPropagator_fourierMultiplierCLM_comm (by fun_prop)]

/-- `S(t)` commutes with the Laplacian: `Δ (S(t) u) = S(t) (Δ u)`. -/
theorem laplacian_schrodingerPropagator (t : ℝ) (u : 𝓢'(E, F)) :
    Δ (schrodingerPropagator E F t u) = schrodingerPropagator E F t (Δ u) := by
  rw [laplacian_eq_fourierMultiplierCLM, laplacian_eq_fourierMultiplierCLM,
    ContinuousLinearMap.map_smul_of_tower,
    schrodingerPropagator_fourierMultiplierCLM_comm (by fun_prop)]

/-- `S(t)` commutes with the Bessel potentials: `J^s (S(t) u) = S(t) (J^s u)`. -/
theorem besselPotential_schrodingerPropagator (s t : ℝ) (u : 𝓢'(E, F)) :
    besselPotential E F s (schrodingerPropagator E F t u) =
      schrodingerPropagator E F t (besselPotential E F s u) := by
  rw [besselPotential, schrodingerPropagator_fourierMultiplierCLM_comm (by fun_prop)]

/-- `S(t)` commutes with the Littlewood–Paley blocks: `Δⱼ (S(t) u) = S(t) (Δⱼ u)`. -/
theorem littlewoodPaleyBlock_schrodingerPropagator (φ : ContDiffBump (0 : E)) (j : ℕ) (t : ℝ)
    (u : 𝓢'(E, F)) :
    littlewoodPaleyBlock F φ j (schrodingerPropagator E F t u) =
      schrodingerPropagator E F t (littlewoodPaleyBlock F φ j u) :=
  littlewoodPaleyBlock_fourierMultiplierCLM_comm φ
    (TauCeti.hasTemperateGrowth_phaseSymbol_laplacianSymbol t) j u

end NormedSpace

/-! ### Agreement with the propagator on `L²` and the Sobolev scale -/

section L2

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **On `L²`, `S(t)` is the unitary propagator** `TauCeti.schrodingerPropagator`: for every
`f ∈ L²(E, F)`, the tempered distribution `S(t) f` is the `L²` function
`TauCeti.schrodingerPropagator F t f`. -/
theorem schrodingerPropagator_toTemperedDistribution (t : ℝ) (f : Lp F 2 (volume : Measure E)) :
    schrodingerPropagator E F t (f : 𝓢'(E, F)) =
      (TauCeti.schrodingerPropagator F t f : 𝓢'(E, F)) := by
  rw [TauCeti.schrodingerPropagator_def, TauCeti.phasePropagator_def]
  exact Lp.fourierMultiplierCLM_toTemperedDistribution_eq f
    (TauCeti.hasTemperateGrowth_phaseSymbol_laplacianSymbol t)
    (TauCeti.memLp_phaseSymbol TauCeti.laplacianSymbol t)

/-- **`S(t)` preserves the Bessel-potential space `H^{s,2}`.** -/
theorem MemSobolev.schrodingerPropagator {s : ℝ} {u : 𝓢'(E, F)} (hu : MemSobolev s 2 u)
    (t : ℝ) : MemSobolev s 2 (TemperedDistribution.schrodingerPropagator E F t u) :=
  hu.fourierMultiplierCLM_of_bounded (TauCeti.hasTemperateGrowth_phaseSymbol_laplacianSymbol t)
    ⟨1, fun ξ ↦ (TauCeti.norm_phaseSymbol _ t ξ).le⟩

end L2

end TemperedDistribution
