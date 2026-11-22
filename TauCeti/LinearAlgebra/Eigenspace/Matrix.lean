/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import TauCeti.LinearAlgebra.Eigenspace.Transport

/-!
# Eigenvectors of matrices, the spectrum and conjugation

Mathlib identifies the spectrum of a square matrix with that of the endomorphism `Matrix.toLin'`
it defines (`Matrix.spectrum_toLin'`), and the spectrum of an endomorphism of a finite-dimensional
vector space with its eigenvalues (`Module.End.hasEigenvalue_iff_mem_spectrum`). This file records
the composite in matrix language: a scalar lies in the spectrum of a matrix over a field exactly
when the matrix has a nonzero eigenvector for it. It also records that conjugate matrices have
eigenspaces of the same dimension, and so do an endomorphism and its matrix in a basis.

## Main results

* `Matrix.mem_spectrum_iff_exists_mulVec_eq_smul`: `μ ∈ spectrum K A` if and only if
  `A *ᵥ v = μ • v` for some nonzero vector `v`.
* `Matrix.finrank_eigenspace_toLin'_conj`: the eigenspaces of `P X P⁻¹` and of `X` have the same
  dimension.
* `LinearMap.finrank_eigenspace_toLin'_toMatrix`: the eigenspaces of an endomorphism and of its
  matrix in a basis have the same dimension.
-/

public section

open scoped Matrix

namespace Matrix

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

/-- A scalar `μ` lies in the spectrum of a square matrix `A` over a field exactly when `A` has a
nonzero eigenvector for `μ`. -/
theorem mem_spectrum_iff_exists_mulVec_eq_smul {A : Matrix n n K} {μ : K} :
    μ ∈ spectrum K A ↔ ∃ v : n → K, v ≠ 0 ∧ A *ᵥ v = μ • v := by
  rw [← spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
  refine ⟨fun h => ?_, fun ⟨v, hv, hAv⟩ => ?_⟩
  · obtain ⟨v, hv⟩ := h.exists_hasEigenvector
    exact ⟨v, hv.2, by simpa using Module.End.mem_eigenspace_iff.1 hv.1⟩
  · exact Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.2 (by simpa using hAv), hv⟩

section Conj

variable {R : Type*} [CommRing R]

/-- **Conjugate matrices have eigenspaces of the same dimension**: `P` maps the eigenspace of `X`
at `μ` onto that of `P X P⁻¹`. -/
theorem finrank_eigenspace_toLin'_conj (P : GL n R) (X : Matrix n n R) (μ : R) :
    Module.finrank R
        (Module.End.eigenspace (toLin' ((P : Matrix n n R) * X * ((P⁻¹ : GL n R) : Matrix n n R)))
          μ) =
      Module.finrank R (Module.End.eigenspace (toLin' X) μ) := by
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (GeneralLinearGroup.toLin P)
  have h := TauCeti.eigenspace_eq_comap_of_intertwine (e := e)
    (f := toLin' X) (g := toLin' ((P : Matrix n n R) * X * ((P⁻¹ : GL n R) : Matrix n n R)))
    (fun x ↦ by simp [e, mulVec_mulVec, Matrix.mul_assoc]) μ
  rw [h, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

end Conj

end Matrix

namespace LinearMap

variable {n R M : Type*} [Fintype n] [DecidableEq n] [CommRing R] [AddCommGroup M] [Module R M]

/-- An endomorphism and its matrix in a basis have eigenspaces of the same dimension: the
coordinates of the basis intertwine the two. -/
theorem finrank_eigenspace_toLin'_toMatrix (b : Module.Basis n R M) (f : Module.End R M) (μ : R) :
    Module.finrank R (Module.End.eigenspace (Matrix.toLin' (LinearMap.toMatrix b b f)) μ) =
      Module.finrank R (Module.End.eigenspace f μ) := by
  rw [TauCeti.eigenspace_eq_comap_of_intertwine (e := b.equivFun)
    (g := Matrix.toLin' (LinearMap.toMatrix b b f)) (fun x ↦ by
      rw [Matrix.toLin'_apply, Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
        LinearMap.toMatrix_mulVec_repr]) μ,
    Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]

end LinearMap
