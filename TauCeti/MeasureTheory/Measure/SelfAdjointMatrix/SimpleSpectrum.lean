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

The characteristic discriminant is nonzero at a diagonal with distinct entries
(`Matrix.charpoly_discr_diagonal_ne_zero_iff`), and on self-adjoint matrices it vanishes exactly
at the matrices with a repeated eigenvalue (`Matrix.IsHermitian.charpoly_discr_ne_zero_iff`).
Applying `MeasureTheory.Measure.ae_charpoly_discr_ne_zero` to the inclusion of the self-adjoint
subspace, a self-adjoint matrix sampled from a law absolutely continuous with respect to
Frobenius volume has distinct eigenvalues almost surely.

The discriminant argument is the one used in Anderson, Guionnet and Zeitouni,
*An Introduction to Random Matrices* (2010), proof of Theorem 2.5.2.
-/

public section

noncomputable section

open MeasureTheory
open scoped TauCeti.SelfAdjointMatrix

namespace MeasureTheory.Measure

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

/-- Frobenius-absolutely-continuous self-adjoint matrix laws have simple eigenvalues
almost surely, including in empty and one-dimensional matrix spaces. -/
theorem ae_injective_eigenvalues_selfAdjoint [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜))) (hμ : μ ≪ volume) :
    ∀ᵐ A ∂μ, Function.Injective (selfAdjoint.isHermitian_coe A).eigenvalues := by
  let D := TauCeti.selfAdjointDiagonal (𝕜 := 𝕜) fun i : Fin n ↦ ((i : ℕ) : ℝ)
  have hD : (D : Matrix (Fin n) (Fin n) 𝕜).charpoly.discr ≠ 0 := by
    rw [TauCeti.coe_selfAdjointDiagonal, Matrix.charpoly_discr_diagonal_ne_zero_iff]
    exact RCLike.ofReal_injective.comp (Nat.cast_injective.comp Fin.val_injective)
  filter_upwards [ae_charpoly_discr_ne_zero μ hμ
    (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜)).subtype.toAffineMap hD] with A hA
  exact (selfAdjoint.isHermitian_coe A).charpoly_discr_ne_zero_iff.mp hA

end MeasureTheory.Measure
