/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-!
# Eigenvectors of matrices and the spectrum

Mathlib identifies the spectrum of a square matrix with that of the endomorphism `Matrix.toLin'`
it defines (`Matrix.spectrum_toLin'`), and the spectrum of an endomorphism of a finite-dimensional
vector space with its eigenvalues (`Module.End.hasEigenvalue_iff_mem_spectrum`). This file records
the composite in matrix language: a scalar lies in the spectrum of a matrix over a field exactly
when the matrix has a nonzero eigenvector for it.

## Main results

* `Matrix.mem_spectrum_iff_exists_mulVec_eq_smul`: `μ ∈ spectrum K A` if and only if
  `A *ᵥ v = μ • v` for some nonzero vector `v`.
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

end Matrix
