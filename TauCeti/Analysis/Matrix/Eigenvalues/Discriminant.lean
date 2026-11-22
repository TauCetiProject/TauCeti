/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# The characteristic discriminant of a Hermitian matrix

The discriminant of the characteristic polynomial of a Hermitian matrix is the product of
the squared gaps of its real eigenvalues. It is therefore nonzero exactly when the eigenvalues
are distinct.

The discriminant argument is the one used in Anderson, Guionnet and Zeitouni,
*An Introduction to Random Matrices* (2010), proof of Theorem 2.5.2.
-/

public section

open Finset Polynomial

namespace Matrix

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-- The characteristic discriminant of a Hermitian matrix is the real product of
the squared eigenvalue gaps. -/
theorem IsHermitian.charpoly_discr_eq {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    A.charpoly.discr =
      ((∏ i, ∏ j ∈ Ioi i, (hA.eigenvalues i - hA.eigenvalues j) ^ 2 : ℝ) : 𝕜) := by
  rw [hA.charpoly_eq, discr_prod_X_sub_C]
  push_cast
  rfl

/-- A Hermitian matrix has nonzero characteristic discriminant exactly when its
eigenvalues are distinct. -/
theorem IsHermitian.charpoly_discr_ne_zero_iff {A : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) :
    A.charpoly.discr ≠ 0 ↔ Function.Injective hA.eigenvalues := by
  rw [hA.charpoly_discr_eq, ne_eq, RCLike.ofReal_eq_zero]
  simp only [prod_ne_zero_iff, mem_univ, true_implies, mem_Ioi, ne_eq,
    pow_eq_zero_iff two_ne_zero, sub_eq_zero]
  exact ⟨fun h i j hij ↦ by
    rcases lt_trichotomy i j with hlt | h | hgt
    · exact (h i j hlt hij).elim
    · exact h
    · exact (h j i hgt hij.symm).elim,
    fun h i j hij ↦ h.ne hij.ne⟩

end Matrix
