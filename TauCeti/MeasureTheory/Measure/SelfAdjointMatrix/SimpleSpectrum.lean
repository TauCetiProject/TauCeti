/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.MeasureTheory.Measure.SelfAdjointMatrix.Basic
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import TauCeti.Analysis.Matrix.Eigenvalues.Discriminant
import TauCeti.MeasureTheory.Measure.MvPolynomialZeroLocus

/-!
# Almost every self-adjoint matrix has simple spectrum

As a function of real linear coordinates on the self-adjoint subspace, the real part of the
characteristic discriminant is a real polynomial (`Matrix.exists_eval_eq_re_charpoly_discr`). It is
nonzero at a diagonal with distinct entries and vanishes exactly at the matrices with a repeated
eigenvalue (`Matrix.IsHermitian.charpoly_discr_ne_zero_iff`). Thus a self-adjoint matrix sampled
from a law absolutely continuous with respect to Frobenius volume has distinct eigenvalues almost
surely.

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
  let E := selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜)
  let b := Module.finBasis ℝ E
  obtain ⟨q, hq⟩ :=
    Matrix.exists_eval_eq_re_charpoly_discr (E.subtype ∘ₗ b.equivFun.symm.toLinearMap)
  obtain ⟨A, hA⟩ := exists_re_charpoly_discr_ne_zero (n := n) (𝕜 := 𝕜)
  have hq₀ : q ≠ 0 := by
    intro h
    have he := hq (b.equivFun A)
    rw [h, map_zero, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      E.subtype_apply] at he
    exact hA he.symm
  have hnonzero : ∀ᵐ x : _ ∂volume, MvPolynomial.eval x q ≠ 0 :=
    compl_mem_ae_iff.mpr (q.volume_setOfPred_eval_eq_zero hq₀)
  have hp := (ae_comp_linearMap_mem_iff (μ := (volume : Measure E)) (ν := volume)
    (L := b.equivFun.toLinearMap) b.equivFun.surjective
    (s := {x | MvPolynomial.eval x q = 0}ᶜ)
    q.measurableSet_setOfPred_eval_eq_zero.compl).mpr hnonzero
  filter_upwards [hμ.ae_le hp] with A' hA'
  refine (selfAdjoint.isHermitian_coe A').charpoly_discr_ne_zero_iff.mp fun h ↦ hA' ?_
  simp only [Set.mem_ofPred_eq, LinearEquiv.coe_toLinearMap]
  rw [hq, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, E.subtype_apply,
    h, map_zero]

end MeasureTheory.Measure
