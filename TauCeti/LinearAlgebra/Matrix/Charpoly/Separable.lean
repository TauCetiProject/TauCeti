/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Matrix.Basis
import TauCeti.LinearAlgebra.Matrix.Charpoly.Diagonal

/-!
# Matrices with separable characteristic polynomial

A square matrix over a field whose characteristic polynomial splits with distinct roots is
diagonalizable: its eigenvectors for the distinct roots form a basis
(`Matrix.exists_mul_eq_mul_diagonal_of_separable`). When the matrix is invertible, the diagonal
entries of any such diagonalization are units (`Matrix.isUnit_of_mul_eq_mul_diagonal`). Conversely,
the diagonal entries of any diagonalization of a matrix with separable characteristic polynomial
are distinct (`Matrix.injective_of_mul_eq_mul_diagonal`).

## Main results

* `Matrix.exists_mul_eq_mul_diagonal_of_separable`: a matrix with split separable characteristic
  polynomial is conjugate to a diagonal matrix.
* `Matrix.isUnit_of_mul_eq_mul_diagonal`: an invertible matrix conjugate to a diagonal matrix has
  unit diagonal entries.
* `Matrix.injective_of_mul_eq_mul_diagonal`: a diagonalization of a matrix with separable
  characteristic polynomial has distinct diagonal entries.
-/

public section

open Polynomial

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A matrix with split separable characteristic polynomial is diagonalizable**: there are an
invertible `P` and a diagonal matrix `diagonal d` with `M * P = P * diagonal d`. -/
theorem exists_mul_eq_mul_diagonal_of_separable {F : Type*} [Field F] (M : Matrix ι ι F)
    (hs : M.charpoly.Splits) (hM : M.charpoly.Separable) :
    ∃ (P : GL ι F) (d : ι → F), M * P = P * diagonal d := by
  classical
  cases isEmpty_or_nonempty ι
  · exact ⟨1, 0, Subsingleton.elim _ _⟩
  set f := Matrix.toLin' M
  set s := M.charpoly.roots.toFinset
  have hev (μ : s) : Module.End.HasEigenvalue f μ := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
    have := μ.property
    rw [Multiset.mem_toFinset, mem_roots hM.ne_zero] at this
    exact this
  choose v hv using fun μ : s ↦ (hev μ).exists_hasEigenvector
  have hli : LinearIndependent F v :=
    Module.End.eigenvectors_linearIndependent' f (fun μ : s ↦ (μ : F)) Subtype.coe_injective v hv
  have hcard : Fintype.card s = Fintype.card ι := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup (nodup_roots hM),
      ← hs.natDegree_eq_card_roots, charpoly_natDegree_eq_dim]
  let e : ι ≃ s := Fintype.equivOfCardEq hcard.symm
  let b := basisOfLinearIndependentOfCardEqFinrank (hli.comp e e.injective) (by simp)
  let _ := (Pi.basisFun F ι).invertibleToMatrix b
  refine ⟨unitOfInvertible ((Pi.basisFun F ι).toMatrix b), fun i ↦ (e i : F), ?_⟩
  ext r c
  have h := congrFun (hv (e c)).apply_eq_smul r
  simp only [f, Matrix.toLin'_apply, mulVec, dotProduct] at h
  simp [Matrix.mul_apply, Module.Basis.toMatrix_apply, b, h, diagonal_apply, mul_comm]

/-- If an invertible matrix `M` satisfies `M * P = P * diagonal d` for an invertible `P`, then every
diagonal entry `d i` is a unit. -/
theorem isUnit_of_mul_eq_mul_diagonal {R : Type*} [CommRing R] {M : Matrix ι ι R} (hM : IsUnit M)
    {P : GL ι R} {d : ι → R} (h : M * P = P * diagonal d) (i : ι) : IsUnit (d i) := by
  have hdet := congrArg det h
  rw [det_mul, det_mul, det_diagonal, mul_comm] at hdet
  have hprod : IsUnit (∏ j, d j) := isUnit_of_mul_isUnit_right (hdet ▸
    ((isUnit_iff_isUnit_det _).1 (Units.isUnit P)).mul ((isUnit_iff_isUnit_det _).1 hM))
  exact isUnit_of_dvd_unit (Finset.dvd_prod_of_mem d (Finset.mem_univ i)) hprod

/-- The diagonal entries of a diagonalization of a matrix with separable characteristic polynomial
are distinct. -/
theorem injective_of_mul_eq_mul_diagonal {R : Type*} [CommRing R] [Nontrivial R]
    {M : Matrix ι ι R} (hsep : M.charpoly.Separable) {P : GL ι R} {d : ι → R}
    (hP : M * P = P * diagonal d) : Function.Injective d := by
  rw [charpoly_eq_prod_of_mul_eq_mul_diagonal hP] at hsep
  exact fun i j hij ↦ hsep.inj_of_prod_X_sub_C (Finset.mem_univ i) (Finset.mem_univ j) hij

end Matrix
