/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Localized.Basic
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Localized Hamiltonian variations detect annihilating covector fields

Let `u` be a map from an open set `Ω` of a finite-dimensional parameter space to a symplectic
vector space, continuous on `Ω`, and let `η` be a locally integrable covector field on `Ω`. If
`∫ η(z)(X_{δK z}(u z)) = 0` for every smooth compactly supported Hamiltonian variation `δK`
supported in an open neighbourhood `U` of the graph of `u` over `Ω`, then `η = 0` almost
everywhere on `Ω`, and everywhere on `Ω` when `η` is continuous there.

There is no nonconstancy, injectivity or somewhere-injectivity hypothesis on `u`: the variations
are localized in the product of the parameter space and the target, so constant maps are covered.
Only continuity of `u` on `Ω` is used.

The variations are explicit. For a test function `ρ` on the parameter space and a vector `v`, the
variation `δK(z, x) = ρ(z) χ(z, x) ω(v, x)`, with `χ` a smooth cutoff equal to `1` near the graph
of `u` over the support of `ρ`, satisfies `X_{δK z}(u z) = ρ(z) v` for every `z`
(`TauCeti.SymplecticForm.exists_contDiff_hamiltonianVectorField_comp_eq_smul`). The vanishing
of `η` then follows from the fundamental lemma of the calculus of variations,
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  localized Hamiltonian perturbations in the universal Cauchy–Riemann equation.
-/

public section

open MeasureTheory Set Function

namespace TauCeti.SymplecticForm

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Hamiltonian variations detect cokernel elements.** Let `u` be continuous on an open set `Ω`
and let `η` be a locally integrable field of covectors on `Ω`. If `η` annihilates the Hamiltonian
vector fields `z ↦ X_{δK z}(u z)` of all smooth Hamiltonian variations `δK` with compact support
in an open neighbourhood `U` of the graph of `u` over `Ω`, then `η` vanishes almost everywhere on
`Ω`. No hypothesis on `u` beyond continuity is needed, so this applies to constant maps. -/
theorem ae_eq_zero_of_integral_apply_hamiltonianVectorField_eq_zero [MeasurableSpace E]
    [BorelSpace E] {μ : Measure E} (ω : SymplecticForm V) {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → V} (hu : ContinuousOn u Ω) {U : Set (E × V)} (hU : IsOpen U)
    (hΩU : ∀ z ∈ Ω, (z, u z) ∈ U) {η : E → V →L[ℝ] ℝ} (hη : LocallyIntegrableOn η Ω μ)
    (h : ∀ δK : E → V → ℝ, ContDiff ℝ (⊤ : ℕ∞) (uncurry δK) → HasCompactSupport (uncurry δK) →
      tsupport (uncurry δK) ⊆ U → ∫ z, η z (ω.hamiltonianVectorField (δK z) (u z)) ∂μ = 0) :
    ∀ᵐ z ∂μ, z ∈ Ω → η z = 0 := by
  refine hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hη fun ρ hρ hρc hρΩ ↦ ?_
  ext v
  obtain ⟨δK, hδK, hδKc, hδKU, hX⟩ :=
    ω.exists_contDiff_hamiltonianVectorField_comp_eq_smul hu hU hΩU hρ hρc hρΩ v
  have hv : ∫ z, η z (ρ z • v) ∂μ = 0 := by simpa only [hX] using h δK hδK hδKc hδKU
  by_cases hi : Integrable (fun z ↦ ρ z • η z) μ
  · rw [ContinuousLinearMap.integral_apply hi]
    simpa using hv
  · simp [integral_undef hi]

/-- **Hamiltonian variations detect continuous cokernel elements pointwise.** If, in the setting of
`TauCeti.SymplecticForm.ae_eq_zero_of_integral_apply_hamiltonianVectorField_eq_zero`, the covector
field `η` is continuous on `Ω` and the measure charges every nonempty open set, then `η` vanishes at
every point of `Ω`. -/
theorem eqOn_zero_of_integral_apply_hamiltonianVectorField_eq_zero [MeasurableSpace E]
    [BorelSpace E] {μ : Measure E} [μ.IsOpenPosMeasure] [IsLocallyFiniteMeasure μ]
    (ω : SymplecticForm V) {Ω : Set E} (hΩ : IsOpen Ω)
    {u : E → V} (hu : ContinuousOn u Ω) {U : Set (E × V)} (hU : IsOpen U)
    (hΩU : ∀ z ∈ Ω, (z, u z) ∈ U) {η : E → V →L[ℝ] ℝ} (hη : ContinuousOn η Ω)
    (h : ∀ δK : E → V → ℝ, ContDiff ℝ (⊤ : ℕ∞) (uncurry δK) → HasCompactSupport (uncurry δK) →
      tsupport (uncurry δK) ⊆ U → ∫ z, η z (ω.hamiltonianVectorField (δK z) (u z)) ∂μ = 0) :
    EqOn η 0 Ω := by
  have hae := ω.ae_eq_zero_of_integral_apply_hamiltonianVectorField_eq_zero hΩ hu hU hΩU
    (hη.locallyIntegrableOn hΩ.measurableSet) h
  exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' hΩ.measurableSet).mpr hae) hΩ hη
    continuousOn_const

end TauCeti.SymplecticForm
