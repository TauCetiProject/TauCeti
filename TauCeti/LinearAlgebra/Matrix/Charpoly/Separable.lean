/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Disc
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Matrix.Basis
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Matrices with separable characteristic polynomial

A square matrix over a field whose characteristic polynomial splits with distinct roots is
diagonalizable: its eigenvectors for the distinct roots form a basis
(`Matrix.exists_mul_eq_mul_diagonal_of_separable`). The discriminant of a matrix, the
discriminant of its characteristic polynomial, commutes with ring maps (`Matrix.discr_map`), so
a matrix over a domain whose discriminant is nonzero specializes, at every point where the
discriminant does not vanish, to a matrix with separable characteristic polynomial.

## Main results

* `Matrix.exists_mul_eq_mul_diagonal_of_separable`: a matrix with split separable characteristic
  polynomial is conjugate to a diagonal matrix.
* `Matrix.discr_map`: the discriminant of a matrix commutes with ring maps.
-/

public section

open Polynomial

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The discriminant commutes with ring maps.** The characteristic polynomial is monic, so
mapping it preserves its degree. -/
theorem discr_map {R S : Type*} [CommRing R] [CommRing S] (M : Matrix ι ι R) (φ : R →+* S) :
    (M.map φ).discr = φ M.discr := by
  rw [discr, discr, charpoly_map, M.charpoly_monic.discr_map]

/-- **A matrix with split separable characteristic polynomial is diagonalizable.** Eigenvectors
for the distinct roots of the characteristic polynomial form a basis, and the matrix `P` whose
columns are these eigenvectors satisfies `M * P = P * diagonal d`. -/
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

end Matrix
