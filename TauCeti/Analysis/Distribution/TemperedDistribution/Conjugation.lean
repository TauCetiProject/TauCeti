/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
public import TauCeti.Analysis.Distribution.SchwartzSpace.Conjugation
public import TauCeti.Analysis.Distribution.TemperedDistribution.TestFunction
public import TauCeti.Analysis.LocallyConvex.PointwiseConvergence
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Conjugation of tempered distributions

A continuous conjugate-linear map `L : F →L⋆[ℂ] G` acts on `F`-valued tempered distributions by

`(L u) φ = L (u (conj φ))`

(`TemperedDistribution.conjPostcompCLM`). The conjugation of the test function makes `L u` again
complex-linear in `φ`, and it is what makes this action extend `f ↦ L ∘ f` from functions: for a
Schwartz function or an `Lᵖ` function `f`, `L (∫ conj φ • f) = ∫ φ • L ∘ f`
(`TemperedDistribution.conjPostcompCLM_toTemperedDistributionCLM_eq`,
`TemperedDistribution.conjPostcompCLM_toTemperedDistribution_eq`). For `L = conj` on `ℂ` this is
the complex conjugate `conj (u (conj φ))` of a scalar distribution.

As on Schwartz functions, `L` exchanges the Fourier transform and its inverse, and it conjugates and
reflects the symbol of a Fourier multiplier,
`T_g (L u) = L (T_{g'} u)` with `g'(ξ) = conj (g (-ξ))`
(`TemperedDistribution.fourierMultiplierCLM_conjPostcompCLM`). The symbol `⟨ξ⟩ ^ s` of the Bessel
potential is real and even, so the Bessel potential of every real order commutes with `L`
(`TemperedDistribution.besselPotential_conjPostcompCLM`). This is the identity that makes `L` act on
the Bessel-potential spaces `H^{s,p}` for every real `s`, including negative orders.

## Main declarations

* `TemperedDistribution.conjPostcompCLM`: the action `u ↦ (φ ↦ L (u (conj φ)))` of a continuous
  conjugate-linear map on tempered distributions.
* `TemperedDistribution.conjPostcompCLM_toTemperedDistributionCLM_eq`,
  `TemperedDistribution.conjPostcompCLM_toTemperedDistribution_eq`: it extends `f ↦ L ∘ f` from
  Schwartz functions and from `Lᵖ` functions.
* `TemperedDistribution.mapCLM_re_toDistribution`: on real test functions, the real part of a
  scalar tempered distribution `u` is `(u + conj u) / 2`.
* `TemperedDistribution.fourier_conjPostcompCLM`, `TemperedDistribution.fourierInv_conjPostcompCLM`:
  `𝓕 (L u) = L (𝓕⁻ u)` and `𝓕⁻ (L u) = L (𝓕 u)`.
* `TemperedDistribution.fourierMultiplierCLM_conjPostcompCLM`: conjugation of Fourier multipliers.
* `TemperedDistribution.besselPotential_conjPostcompCLM`: the Bessel potential commutes with `L`.
-/

public section

noncomputable section

open scoped FourierTransform SchwartzMap ComplexConjugate
open FourierTransform MeasureTheory

namespace TemperedDistribution

variable {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

section NormedSpace

variable [NormedSpace ℝ E]

/-- A continuous conjugate-linear map `L : F →L⋆[ℂ] G` acting on tempered distributions,
`(L u) φ = L (u (conj φ))`. On functions it is `f ↦ L ∘ f`. -/
def conjPostcompCLM (L : F →L⋆[ℂ] G) : 𝓢'(E, F) →L⋆[ℂ] 𝓢'(E, G) :=
  (PointwiseConvergenceCLM.postcomp _ L).comp
    (PointwiseConvergenceCLM.precomp F (SchwartzMap.conjCLM (E := E)))

@[simp]
theorem conjPostcompCLM_apply_apply (L : F →L⋆[ℂ] G) (u : 𝓢'(E, F)) (φ : 𝓢(E, ℂ)) :
    conjPostcompCLM L u φ = L (u (SchwartzMap.conjCLM φ)) :=
  (rfl)

/-- Two conjugate-linear maps act on tempered distributions as their complex-linear composite. -/
@[simp]
theorem conjPostcompCLM_conjPostcompCLM {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (L' : G →L⋆[ℂ] H) (L : F →L⋆[ℂ] G) (u : 𝓢'(E, F)) :
    conjPostcompCLM L' (conjPostcompCLM L u) =
      PointwiseConvergenceCLM.postcomp _ (L'.comp L) u := by
  ext φ
  simp

/-- **The real part of a tempered distribution.** On the real test functions of an open set `Ω`,
the real part of a scalar tempered distribution `u` is the restriction of `(u + conj u) / 2`, where
`conj u` is `φ ↦ conj (u (conj φ))`. -/
theorem mapCLM_re_toDistribution (Ω : TopologicalSpace.Opens E) (u : 𝓢'(E, ℂ)) :
    Distribution.mapCLM (Complex.ofRealCLM ∘L Complex.reCLM) (toDistribution Ω u) =
      toDistribution Ω ((2⁻¹ : ℂ) •
        (u + conjPostcompCLM (starL ℂ : ℂ ≃L⋆[ℂ] ℂ).toContinuousLinearMap u)) := by
  ext φ
  -- A real test function is fixed by the conjugation of Schwartz functions.
  have hφ : SchwartzMap.conjCLM
      (SchwartzMap.postcompCLM Complex.ofRealCLM (TestFunction.toSchwartzMapCLM ℝ φ)) =
      SchwartzMap.postcompCLM Complex.ofRealCLM (TestFunction.toSchwartzMapCLM ℝ φ) := by
    ext x
    simp [SchwartzMap.conjCLM_apply]
  simp [hφ, Complex.re_eq_add_conj]
  ring

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] [CompleteSpace G]

/-- On a Schwartz function `f`, the action of a conjugate-linear map `L` is `f ↦ L ∘ f`. -/
theorem conjPostcompCLM_toTemperedDistributionCLM_eq [SecondCountableTopology E] {μ : Measure E}
    [μ.HasTemperateGrowth] (L : F →L⋆[ℂ] G) (f : 𝓢(E, F)) :
    conjPostcompCLM L (SchwartzMap.toTemperedDistributionCLM E F μ f) =
      SchwartzMap.toTemperedDistributionCLM E G μ (SchwartzMap.conjPostcompCLM L f) := by
  ext φ
  have hφf : Integrable (fun x ↦ SchwartzMap.conjCLM φ x • f x) μ :=
    (SchwartzMap.conjCLM φ).integrable.smul_of_top_left (f.memLp_top μ)
  rw [conjPostcompCLM_apply_apply, SchwartzMap.toTemperedDistributionCLM_apply_apply μ,
    SchwartzMap.toTemperedDistributionCLM_apply_apply μ,
    ← L.integral_comp_commSL (fun r z ↦ by simp) hφf]
  congr 1 with x
  simp

/-- On an `Lᵖ` function `f`, the action of a conjugate-linear map `L` is `f ↦ L ∘ f`. -/
theorem conjPostcompCLM_toTemperedDistribution_eq {μ : Measure E} [μ.HasTemperateGrowth]
    {p : ENNReal} [hp : Fact (1 ≤ p)] (L : F →L⋆[ℂ] G) (f : Lp F p μ) :
    conjPostcompCLM L (f : 𝓢'(E, F)) = ((L.compLp f : Lp G p μ) : 𝓢'(E, G)) := by
  ext φ
  have : (1 - p⁻¹)⁻¹.HolderConjugate p :=
    (ENNReal.HolderConjugate.inv_one_sub_inv' hp.out).symm
  have hφf : Integrable (fun x ↦ SchwartzMap.conjCLM φ x • f x) μ :=
    memLp_one_iff_integrable.1
      (((SchwartzMap.conjCLM φ).memLp (1 - p⁻¹)⁻¹ (μ := μ)).smul (Lp.memLp f))
  rw [conjPostcompCLM_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply, ← L.integral_comp_commSL (fun r z ↦ by simp) hφf]
  refine integral_congr_ae ((L.coeFn_compLp f).mono fun x hx ↦ ?_)
  simp [hx]

end NormedSpace

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section Fourier

/-- A conjugate-linear map exchanges the Fourier transform and its inverse on tempered
distributions: `𝓕 (L u) = L (𝓕⁻ u)`. -/
@[simp]
theorem fourier_conjPostcompCLM (L : F →L⋆[ℂ] G) (u : 𝓢'(E, F)) :
    𝓕 (conjPostcompCLM L u) = conjPostcompCLM L (𝓕⁻ u) := by
  ext φ
  simp [fourier_apply, fourierInv_apply, SchwartzMap.conjCLM_fourier]

/-- A conjugate-linear map exchanges the inverse Fourier transform and the Fourier transform on
tempered distributions: `𝓕⁻ (L u) = L (𝓕 u)`. -/
@[simp]
theorem fourierInv_conjPostcompCLM (L : F →L⋆[ℂ] G) (u : 𝓢'(E, F)) :
    𝓕⁻ (conjPostcompCLM L u) = conjPostcompCLM L (𝓕 u) := by
  ext φ
  simp [fourier_apply, fourierInv_apply, SchwartzMap.conjCLM_fourierInv]

/-- **Conjugation of Fourier multipliers.** A conjugate-linear map `L` conjugates and reflects the
symbol of a Fourier multiplier on tempered distributions: `T_g (L u) = L (T_{g'} u)` with
`g'(ξ) = conj (g (-ξ))`. -/
theorem fourierMultiplierCLM_conjPostcompCLM (L : F →L⋆[ℂ] G) {g : E → ℂ}
    (hg : g.HasTemperateGrowth) (u : 𝓢'(E, F)) :
    fourierMultiplierCLM G g (conjPostcompCLM L u) =
      conjPostcompCLM L (fourierMultiplierCLM F (fun ξ ↦ conj (g (-ξ))) u) := by
  have hg' : (fun ξ ↦ conj (g ξ)).HasTemperateGrowth :=
    (Complex.conjCLE.toContinuousLinearMap.hasTemperateGrowth).comp hg
  have hg'' : (fun ξ ↦ conj (g (-ξ))).HasTemperateGrowth :=
    (Complex.conjCLE.toContinuousLinearMap.hasTemperateGrowth).comp (by fun_prop)
  -- The multipliers act on the test function through `𝓕 (g • 𝓕⁻ φ) = T_{g (-·)} φ`, and
  -- conjugating the test function turns `T_{g (-·)}` into `T_{conj ∘ g}`.
  ext φ
  rw [fourierMultiplierCLM_apply_apply, conjPostcompCLM_apply_apply, conjPostcompCLM_apply_apply,
    fourierMultiplierCLM_apply_apply, SchwartzMap.fourier_smulLeftCLM_fourierInv_eq hg,
    SchwartzMap.fourier_smulLeftCLM_fourierInv_eq hg'']
  have h : SchwartzMap.conjCLM (SchwartzMap.fourierMultiplierCLM ℂ (fun ξ ↦ g (-ξ)) φ) =
      SchwartzMap.fourierMultiplierCLM ℂ (fun ξ ↦ conj (g (-(-ξ)))) (SchwartzMap.conjCLM φ) := by
    simpa using (SchwartzMap.fourierMultiplierCLM_conjCLM hg' φ).symm
  rw [h]

/-- **The Bessel potential commutes with conjugate-linear maps.** Its symbol `⟨ξ⟩ ^ s` is real and
even, so `J^s (L u) = L (J^s u)` for every real order `s`. -/
@[simp]
theorem besselPotential_conjPostcompCLM (L : F →L⋆[ℂ] G) (s : ℝ) (u : 𝓢'(E, F)) :
    besselPotential E G s (conjPostcompCLM L u) = conjPostcompCLM L (besselPotential E F s u) := by
  simp only [besselPotential]
  rw [fourierMultiplierCLM_conjPostcompCLM L (by fun_prop)]
  simp [norm_neg]

end Fourier

end TemperedDistribution
