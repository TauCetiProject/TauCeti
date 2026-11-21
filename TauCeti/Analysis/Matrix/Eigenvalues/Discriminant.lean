/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.MeasureTheory.Measure.SelfAdjointMatrix
public import TauCeti.RingTheory.Polynomial.Resultant.Discriminant
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import TauCeti.Algebra.MvPolynomial.Eval
import TauCeti.MeasureTheory.Measure.MvPolynomialZeroLocus

/-!
# The null locus of repeated Hermitian eigenvalues

The discriminant of a self-adjoint matrix is the product of squared gaps of its real
eigenvalues. As a function of real linear coordinates on the self-adjoint subspace, it is
a nonzero real polynomial. Thus a self-adjoint matrix sampled from a law absolutely
continuous with respect to Frobenius volume has distinct eigenvalues almost surely.

The discriminant argument is the one used in Anderson, Guionnet and Zeitouni,
*An Introduction to Random Matrices* (2010), proof of Theorem 2.5.2.
-/

public section

noncomputable section

open Finset MeasureTheory Polynomial
open scoped TauCeti.SelfAdjointMatrix

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

namespace MeasureTheory.Measure

variable {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]

private theorem exists_eval_charpoly_discr {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℝ (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜))) :
    ∃ q : MvPolynomial ι ℝ, ∀ x : ι → ℝ, MvPolynomial.eval x q =
      RCLike.re (b.equivFun.symm x : Matrix (Fin n) (Fin n) 𝕜).charpoly.discr := by
  let _ := Fintype.ofFinite ι
  let M : Matrix (Fin n) (Fin n) (MvPolynomial ι 𝕜) := Matrix.of fun i j ↦
    ∑ k, MvPolynomial.C ((b k : Matrix (Fin n) (Fin n) 𝕜) i j) * MvPolynomial.X k
  obtain ⟨q, hq⟩ := (M.charpoly.discr).exists_eval_eq_linearMap (RCLike.reLm (K := 𝕜))
  refine ⟨q, fun x ↦ ?_⟩
  let φ := MvPolynomial.eval (algebraMap ℝ 𝕜 ∘ x)
  have hM : M.map φ = (b.equivFun.symm x : Matrix (Fin n) (Fin n) 𝕜) := by
    rw [Module.Basis.equivFun_symm_apply]
    ext i j
    simp [M, φ, Algebra.smul_def, Matrix.algebraMap_eq_diagonal, mul_comm]
  rw [← hM, Matrix.charpoly_map, M.charpoly_monic.discr_map]
  exact hq x

private theorem exists_re_charpoly_discr_ne_zero :
    ∃ A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜),
      RCLike.re A.val.charpoly.discr ≠ 0 := by
  let d (i : Fin n) := (i.val : ℝ)
  let A : selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜) :=
    ⟨Matrix.diagonal fun i ↦ (d i : 𝕜),
      Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)⟩
  refine ⟨A, ?_⟩
  have hA : A.val.charpoly.discr = ((∏ i, ∏ j ∈ Ioi i, (d i - d j) ^ 2 : ℝ) : 𝕜) := by
    rw [show A.val = Matrix.diagonal (fun i ↦ (d i : 𝕜)) from rfl, Matrix.charpoly_diagonal,
      discr_prod_X_sub_C]
    push_cast
    rfl
  rw [hA, RCLike.ofReal_re]
  exact prod_ne_zero_iff.mpr fun i _ ↦ prod_ne_zero_iff.mpr fun j hj ↦
    pow_ne_zero _ (sub_ne_zero.mpr fun h ↦ (mem_Ioi.mp hj).ne (Fin.ext (by
      have h' : (i.val : ℝ) = (j.val : ℝ) := h
      exact_mod_cast h')))

/-- Frobenius-absolutely-continuous self-adjoint matrix laws have simple eigenvalues
almost surely, including in empty and one-dimensional matrix spaces. -/
theorem ae_injective_eigenvalues_selfAdjoint [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure (selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜))) (hμ : μ ≪ volume) :
    ∀ᵐ A ∂μ, Function.Injective (selfAdjoint.isHermitian_coe A).eigenvalues := by
  let E := selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) 𝕜)
  let b := Module.finBasis ℝ E
  obtain ⟨q, hq⟩ := exists_eval_charpoly_discr b
  obtain ⟨A, hA⟩ := exists_re_charpoly_discr_ne_zero (n := n) (𝕜 := 𝕜)
  have hq₀ : q ≠ 0 := by
    intro h
    have he := hq (b.equivFun A)
    rw [h, map_zero, LinearEquiv.symm_apply_apply] at he
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
  rw [hq, LinearEquiv.symm_apply_apply, h, map_zero]

end MeasureTheory.Measure
