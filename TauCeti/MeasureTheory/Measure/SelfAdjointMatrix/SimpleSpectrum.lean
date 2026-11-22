/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.MeasureTheory.Measure.SelfAdjointMatrix.Basic
import TauCeti.Analysis.Matrix.Eigenvalues.Discriminant
import TauCeti.MeasureTheory.Measure.Matrix.CharpolyDiscriminant

/-!
# Almost every self-adjoint matrix has simple spectrum

The characteristic discriminant of a self-adjoint matrix is real. It is nonzero at a diagonal with
distinct entries and vanishes exactly at the matrices with a repeated eigenvalue
(`Matrix.IsHermitian.charpoly_discr_ne_zero_iff`). Applying
`MeasureTheory.Measure.ae_charpoly_discr_ne_zero_of_re_ne_zero` to the inclusion of the
self-adjoint subspace, a self-adjoint matrix sampled from a law absolutely continuous with respect
to Frobenius volume has distinct eigenvalues almost surely.

The discriminant argument is the one used in Anderson, Guionnet and Zeitouni,
*An Introduction to Random Matrices* (2010), proof of Theorem 2.5.2.
-/

public section

noncomputable section

open MeasureTheory Polynomial
open scoped TauCeti.SelfAdjointMatrix

namespace MeasureTheory.Measure

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

private theorem exists_re_charpoly_discr_ne_zero :
    ∃ A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜),
      RCLike.re A.val.charpoly.discr ≠ 0 := by
  let D := Matrix.diagonal fun i : Fin n ↦ ((i : ℕ) : 𝕜)
  have hD : D.IsHermitian := Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)
  have hsep : D.charpoly.discr ≠ 0 := by
    rw [D.charpoly_monic.discr_ne_zero_iff, Matrix.charpoly_diagonal, separable_prod_X_sub_C_iff]
    exact fun i j h ↦ Fin.ext (Nat.cast_injective (R := 𝕜) h)
  rw [hD.charpoly_discr_eq, ne_eq, RCLike.ofReal_eq_zero] at hsep
  refine ⟨⟨D, hD⟩, ?_⟩
  rwa [hD.charpoly_discr_eq, RCLike.ofReal_re]

/-- Frobenius-absolutely-continuous self-adjoint matrix laws have simple eigenvalues
almost surely, including in empty and one-dimensional matrix spaces. -/
theorem ae_injective_eigenvalues_selfAdjoint [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜))) (hμ : μ ≪ volume) :
    ∀ᵐ A ∂μ, Function.Injective (selfAdjoint.isHermitian_coe A).eigenvalues := by
  obtain ⟨A, hA⟩ := exists_re_charpoly_discr_ne_zero (n := n) (𝕜 := 𝕜)
  filter_upwards [ae_charpoly_discr_ne_zero_of_re_ne_zero μ hμ
    (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜)).subtype hA] with A' hA'
  exact (selfAdjoint.isHermitian_coe A').charpoly_discr_ne_zero_iff.mp hA'

end MeasureTheory.Measure
