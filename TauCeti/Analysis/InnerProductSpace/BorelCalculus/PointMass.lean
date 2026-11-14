/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Basic

/-!
# Spectral projections of points

Let `a` be a normal operator on a complex Hilbert space with spectral measure `P`. On the range
of the spectral projection `P({μ})` of a point `μ`, the operator `a` acts as multiplication by `μ`.
Consequently, if `μ` is not an eigenvalue of `a`, then `P({μ}) = 0`, and every diagonal measure of
`P` assigns mass zero to `{μ}`.

## Main results

* `ContinuousLinearMap.comp_spectralPVM_proj_preimage_singleton`,
  `ContinuousLinearMap.mul_spectralPVM_proj_preimage_singleton`,
  `ContinuousLinearMap.apply_spectralPVM_proj_preimage_singleton`: `a P({μ}) = μ P({μ})`.
* `ContinuousLinearMap.spectralPVM_proj_preimage_singleton_eq_zero`: the spectral projection of a
  non-eigenvalue vanishes.
* `ContinuousLinearMap.diagMeasure_preimage_singleton_eq_zero`: the diagonal measures do not
  charge a non-eigenvalue.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), §IX.2.
-/

public section

noncomputable section

open MeasureTheory TauCeti

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (a : H →L[ℂ] H) [IsStarNormal a]

/-- On the spectral projection of a point `μ`, a normal operator acts as multiplication by `μ`:
`a P({μ}) = μ P({μ})`. -/
@[simp]
theorem comp_spectralPVM_proj_preimage_singleton (μ : ℂ) :
    a ∘L a.spectralPVM.proj (Subtype.val ⁻¹' {μ}) (measurable_subtype_coe
      (measurableSet_singleton μ)) =
      μ • a.spectralPVM.proj (Subtype.val ⁻¹' {μ})
        (measurable_subtype_coe (measurableSet_singleton μ)) := by
  -- The coordinate times the indicator of `{μ}` is `μ` times that indicator.
  have hmul : BoundedBorelFunction.ofContinuousMap ((ContinuousMap.id ℂ).restrict (spectrum ℂ a)) *
      BoundedBorelFunction.indicator (Subtype.val ⁻¹' {μ})
        (measurable_subtype_coe (measurableSet_singleton μ)) 1 =
      μ • BoundedBorelFunction.indicator (Subtype.val ⁻¹' {μ})
        (measurable_subtype_coe (measurableSet_singleton μ)) 1 := by
    ext z
    by_cases hz : (z : ℂ) = μ
    · simp [Set.indicator, hz]
    · simp [Set.indicator, hz]
  have h := congrArg a.borelCalculus hmul
  rwa [map_mul, map_smul, borelCalculus_restrict_id, borelCalculus_indicator] at h

/-- `a P({μ}) = μ P({μ})`, stated with the multiplication of `H →L[ℂ] H`. -/
@[simp]
theorem mul_spectralPVM_proj_preimage_singleton (μ : ℂ) :
    a * a.spectralPVM.proj (Subtype.val ⁻¹' {μ}) (measurable_subtype_coe
      (measurableSet_singleton μ)) =
      μ • a.spectralPVM.proj (Subtype.val ⁻¹' {μ})
        (measurable_subtype_coe (measurableSet_singleton μ)) :=
  a.comp_spectralPVM_proj_preimage_singleton μ

/-- A normal operator `a` maps each vector `P({μ}) x` to `μ P({μ}) x`. -/
@[simp]
theorem apply_spectralPVM_proj_preimage_singleton (μ : ℂ) (x : H) :
    a (a.spectralPVM.proj (Subtype.val ⁻¹' {μ}) (measurable_subtype_coe
      (measurableSet_singleton μ)) x) =
      μ • a.spectralPVM.proj (Subtype.val ⁻¹' {μ})
        (measurable_subtype_coe (measurableSet_singleton μ)) x :=
  congrArg (fun T : H →L[ℂ] H => T x) (a.comp_spectralPVM_proj_preimage_singleton μ)

/-- **Spectral projections of non-eigenvalues vanish.** If `μ` is not an eigenvalue of a normal
operator `a`, its spectral projection `P({μ})` is zero. -/
theorem spectralPVM_proj_preimage_singleton_eq_zero {μ : ℂ}
    (hμ : ¬ Module.End.HasEigenvalue (a : H →ₗ[ℂ] H) μ) :
    a.spectralPVM.proj (Subtype.val ⁻¹' {μ}) (measurable_subtype_coe
      (measurableSet_singleton μ)) = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [zero_apply]
  by_contra hx
  exact hμ (Module.End.hasEigenvalue_of_hasEigenvector (Module.End.hasEigenvector_iff.2
    ⟨Module.End.mem_eigenspace_iff.2 (a.apply_spectralPVM_proj_preimage_singleton μ x), hx⟩))

/-- If `μ` is not an eigenvalue of a normal operator `a`, every diagonal measure of its spectral
measure assigns mass zero to `{μ}`. -/
theorem diagMeasure_preimage_singleton_eq_zero {μ : ℂ}
    (hμ : ¬ Module.End.HasEigenvalue (a : H →ₗ[ℂ] H) μ) (ξ : H) :
    a.diagMeasure ξ (Subtype.val ⁻¹' {μ}) = 0 :=
  a.spectralPVM_diag ξ ▸ (a.spectralPVM.proj_eq_zero_iff_forall_diag_apply_eq_zero _ _).1
    (a.spectralPVM_proj_preimage_singleton_eq_zero hμ) ξ

end ContinuousLinearMap
