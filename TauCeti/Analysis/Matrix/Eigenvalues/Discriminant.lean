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
the squared gaps of its ordered real eigenvalues. It is therefore nonzero exactly when the
eigenvalues are distinct. Along linear coordinates on the self-adjoint matrices, the zero locus
of the real polynomial that `Matrix.exists_eval_eq_linearMap_charpoly_discr` gives for the real
part is thus the set of matrices with a repeated eigenvalue.

The discriminant argument is the one used in Anderson, Guionnet and Zeitouni,
*An Introduction to Random Matrices* (2010), proof of Theorem 2.5.2.
-/

public section

open Finset Polynomial

namespace Matrix

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- The characteristic discriminant of a Hermitian matrix is the real product of
the squared gaps of its ordered eigenvalues. -/
theorem IsHermitian.charpoly_discr_eq {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) :
    A.charpoly.discr =
      ((∏ i, ∏ j ∈ Ioi i, (hA.eigenvalues₀ i - hA.eigenvalues₀ j) ^ 2 : ℝ) : 𝕜) := by
  have h : A.charpoly = ∏ i, (X - C (hA.eigenvalues₀ i : 𝕜)) := by
    rw [hA.charpoly_eq]
    exact Equiv.prod_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      fun i ↦ X - C (hA.eigenvalues₀ i : 𝕜)
  rw [h, discr_prod_X_sub_C]
  push_cast
  rfl

/-- A Hermitian matrix has nonzero characteristic discriminant exactly when its
eigenvalues are distinct. -/
theorem IsHermitian.charpoly_discr_ne_zero_iff {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) :
    A.charpoly.discr ≠ 0 ↔ Function.Injective hA.eigenvalues := by
  rw [A.charpoly_monic.discr_ne_zero_iff, hA.charpoly_eq, separable_prod_X_sub_C_iff]
  exact RCLike.ofReal_injective.of_comp_iff _

end Matrix
