/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Perturbation
public import TauCeti.Geometry.Symplectic.Hamiltonian.Localized.Annihilator

/-!
# Hamiltonian variations detect cokernel elements on the core

In the transversality argument for inhomogeneous Floer equations, the universal linearized
operator at a solution `u` is `(ξ, δK) ↦ D_u ξ - X_{δK}(u)`, where `δK` ranges over
compactly supported variations of the Hamiltonian perturbation localized in the compact core of
the domain. Its surjectivity is proved by showing that a functional `η` on its target which
annihilates the whole range vanishes. This file proves the part coming from the Hamiltonian
variations alone, for the parameter derivatives of the Floer operator
`TauCeti.SymplecticForm.floerOperator` in the directions of variations of its `ds` component: if
`η` annihilates them for every smooth compactly supported `δK` supported in a neighbourhood `U` of
the graph of `u` over an open set `Ω`, then `η = 0` almost everywhere on `Ω`. It reduces to the
corresponding statement for the Hamiltonian vector fields `X_{δK z}(u z)`
(`TauCeti.SymplecticForm.ae_eq_zero_of_integral_apply_hamiltonianVectorField_eq_zero`), since the
Floer operator is affine in the variation with derivative `-X_{δK z}(u z)`.

There is no nonconstancy, injectivity or somewhere-injectivity hypothesis on `u`: the variations
are localized in the product of the domain and the target, so they detect cokernel elements along
constant solutions as well as nonconstant ones. Only continuity of `u` on `Ω` is used. This is
where Hamiltonian variations differ from variations of the almost complex structure, which only
act through the perturbed derivative `du - X_K` and need an injectivity argument.

This is a statement about the Hamiltonian component of the universal operator in local
coordinates. It does not assert unique continuation for the formal adjoint of `D_u`, closedness
of the range of a Sobolev operator, or regularity of a moduli space.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Chapter 8, on
  transversality for the universal moduli space of solutions with Hamiltonian perturbations.
-/

public section

open MeasureTheory Set Function

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

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
