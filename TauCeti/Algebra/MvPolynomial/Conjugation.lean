/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import TauCeti.LinearAlgebra.Complex.Conjugation

/-!
# Complex conjugation of multivariate polynomials

Complex polynomials are the complexification of real polynomials:
`MvPolynomial.algebraTensorAlgEquiv ℝ ℂ : ℂ ⊗[ℝ] ℝ[X_σ] ≃ₐ[ℂ] ℂ[X_σ]`. Under this identification
the conjugation `TauCeti.tmulConj` of the complexification is the coefficientwise conjugation
`MvPolynomial.map (starRingEnd ℂ)` (`MvPolynomial.algebraTensorAlgEquiv_tmulConj`). Consequently
a complex polynomial is fixed by coefficientwise conjugation exactly when it has real
coefficients (`MvPolynomial.map_starRingEnd_eq_self_iff`).
-/

public section

open scoped TensorProduct

namespace MvPolynomial

variable {σ : Type*}

/-- Under `ℂ ⊗[ℝ] ℝ[X_σ] ≃ ℂ[X_σ]`, the conjugation of the complexification is coefficientwise
complex conjugation. -/
theorem algebraTensorAlgEquiv_tmulConj (u : ℂ ⊗[ℝ] MvPolynomial σ ℝ) :
    algebraTensorAlgEquiv ℝ ℂ (TauCeti.tmulConj _ u) =
      map (starRingEnd ℂ) (algebraTensorAlgEquiv ℝ ℂ u) := by
  have hconj : (starRingEnd ℂ).comp (algebraMap ℝ ℂ) = algebraMap ℝ ℂ :=
    RingHom.ext Complex.conj_ofReal
  induction u with
  | tmul c q => simp [smul_eq_C_mul, map_map, hconj]
  | add u v hu hv => simp [hu, hv]

/-- A complex polynomial is fixed by coefficientwise conjugation exactly when it has real
coefficients. -/
theorem map_starRingEnd_eq_self_iff (p : MvPolynomial σ ℂ) :
    map (starRingEnd ℂ) p = p ↔ ∃ q : MvPolynomial σ ℝ, map (algebraMap ℝ ℂ) q = p := by
  obtain ⟨u, rfl⟩ := (algebraTensorAlgEquiv (σ := σ) ℝ ℂ).surjective p
  rw [← algebraTensorAlgEquiv_tmulConj, (algebraTensorAlgEquiv ℝ ℂ).injective.eq_iff,
    TauCeti.tmulConj_eq_self_iff]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q, by simp⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, (algebraTensorAlgEquiv ℝ ℂ).injective (by simp [hq])⟩

end MvPolynomial
