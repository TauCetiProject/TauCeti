/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Perturbation
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Hamiltonian variations detect cokernel elements on the core

In the transversality argument for inhomogeneous Floer equations, the universal linearized
operator at a solution `u` is `(ξ, δK) ↦ D_u ξ - X_{δK}(u)`, where `δK` ranges over
compactly supported variations of the Hamiltonian perturbation localized in the compact core of
the domain. Its surjectivity is proved by showing that a functional `η` on its target which
annihilates the whole range vanishes. This file proves the part coming from the Hamiltonian
variations alone: if `∫ η(z)(X_{δK z}(u z)) = 0` for every smooth compactly supported `δK`
supported in a neighbourhood `U` of the graph of `u` over an open set `Ω`, then `η = 0` almost
everywhere on `Ω`, and everywhere on `Ω` when `η` is continuous there. The same holds for the
parameter derivatives of the Floer operator `TauCeti.SymplecticForm.floerOperator` in the
directions of variations of its `ds` component.

There is no nonconstancy, injectivity or somewhere-injectivity hypothesis on `u`: the variations
are localized in the product of the domain and the target, so they detect cokernel elements along
constant solutions as well as nonconstant ones. Only continuity of `u` on `Ω` is used. This is
where Hamiltonian variations differ from variations of the almost complex structure, which only
act through the perturbed derivative `du - X_K` and need an injectivity argument.

The variations are explicit. For a test function `ρ` on the domain and a vector `v`, the variation
`δK(z, x) = ρ(z) χ(z, x) ω(v, x)`, with `χ` a smooth cutoff equal to `1` near the graph of `u`
over the support of `ρ`, satisfies `X_{δK z}(u z) = ρ(z) v` for every `z`
(`TauCeti.SymplecticForm.exists_contDiff_hamiltonianVectorField_comp_eq_smul`). The vanishing
of `η` then follows from the fundamental lemma of the calculus of variations,
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`.

These are statements about the Hamiltonian component of the universal operator in local
coordinates. They do not assert unique continuation for the formal adjoint of `D_u`, closedness
of the range of a Sobolev operator, or regularity of a moduli space.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Chapter 8, on
  transversality for the universal moduli space of solutions with Hamiltonian perturbations.
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

/-- **Variations of the `ds` component detect cokernel elements of the Floer operator.** Let `u`
be continuous on an open set `Ω` of the domain, with the `ds` Hamiltonian differentiable along
`u` there. If a locally integrable covector field `η` annihilates the parameter derivatives
`d/dr F(Ks + r δK)` at `r = 0` of the Floer operator at `u`, for every smooth variation `δK` of
the `ds` component with compact support in an open neighbourhood `U` of the graph of `u` over
`Ω`, then `η` vanishes almost everywhere on `Ω`. There is no hypothesis on `J`, `Kt`, or on
nonconstancy of `u`. -/
theorem ae_eq_zero_of_integral_apply_deriv_floerOperator_eq_zero {μ : Measure (ℝ × ℝ)}
    (ω : SymplecticForm V) (J : ℝ × ℝ → V → V →L[ℝ] V) (Ks Kt : ℝ × ℝ → V → ℝ)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {u : ℝ × ℝ → V} (hu : ContinuousOn u Ω)
    (hKs : ∀ z ∈ Ω, DifferentiableAt ℝ (Ks z) (u z)) {U : Set ((ℝ × ℝ) × V)} (hU : IsOpen U)
    (hΩU : ∀ z ∈ Ω, (z, u z) ∈ U) {η : ℝ × ℝ → V →L[ℝ] ℝ} (hη : LocallyIntegrableOn η Ω μ)
    (h : ∀ δK : ℝ × ℝ → V → ℝ, ContDiff ℝ (⊤ : ℕ∞) (uncurry δK) → HasCompactSupport (uncurry δK) →
      tsupport (uncurry δK) ⊆ U →
        ∫ z, η z (deriv (fun r : ℝ ↦
          ω.floerOperator J (fun w y ↦ Ks w y + r * δK w y) Kt u z) 0) ∂μ = 0) :
    ∀ᵐ z ∂μ, z ∈ Ω → η z = 0 := by
  -- Restrict the variations to lie over `Ω`. There the Floer operator is affine in the variation
  -- with derivative `-X_{δK z}(u z)`; elsewhere the variation vanishes identically.
  refine ω.ae_eq_zero_of_integral_apply_hamiltonianVectorField_eq_zero hΩ hu
    (hU.inter (hΩ.prod isOpen_univ)) (fun z hz ↦ ⟨hΩU z hz, hz, mem_univ _⟩) hη
    fun δK hδK hδKc hδKU ↦ ?_
  have hd : ∀ z, deriv (fun r : ℝ ↦
      ω.floerOperator J (fun w y ↦ Ks w y + r * δK w y) Kt u z) 0 =
        -ω.hamiltonianVectorField (δK z) (u z) := by
    intro z
    by_cases hz : z ∈ Ω
    · have hδ : DifferentiableAt ℝ (δK z) (u z) :=
        (hδK.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) (u z)
      simp_rw [ω.floerOperator_add_const_mul_left J Ks Kt δK u z (hKs z hz) hδ]
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const
        (ω.hamiltonianVectorField (δK z) (u z))).const_sub (ω.floerOperator J Ks Kt u z) |>.deriv
    · have hδz : δK z = fun _ ↦ 0 := funext fun x ↦
        image_eq_zero_of_notMem_tsupport (f := uncurry δK) (x := (z, x))
          fun h ↦ hz (hδKU h).2.1
      have hconst : (fun r : ℝ ↦ ω.floerOperator J (fun w y ↦ Ks w y + r * δK w y) Kt u z) =
          fun _ ↦ ω.floerOperator J Ks Kt u z := by
        funext r
        simp [floerOperator_def, hδz]
      rw [hconst, deriv_const, hδz, hamiltonianVectorField_const, Pi.zero_apply, neg_zero]
  simpa [hd, integral_neg] using h δK hδK hδKc (hδKU.trans inter_subset_left)

end TauCeti.SymplecticForm
