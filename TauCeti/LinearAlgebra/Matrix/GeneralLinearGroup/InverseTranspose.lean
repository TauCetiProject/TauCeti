/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Unitary
import Mathlib.Algebra.Group.Units.Opposite
import Mathlib.Algebra.Group.Equiv.Opposite

/-!
# Inverse transpose on the general linear group

Over a commutative semiring, inverse transpose is an involutive automorphism of the general
linear group. It inverts diagonal entries and fixes permutation matrices. Over a commutative
ring it exchanges the indices of an elementary transvection and negates its parameter.

These formulas describe the contragredient action on matrices and provide the inverse-transpose
part of the pinned type-`A` graph automorphism.

## Main definitions

* `Matrix.GeneralLinearGroup.inverseTranspose`: the automorphism `g ↦ (g⁻¹)ᵀ`.

## Main results

* `Matrix.GeneralLinearGroup.inverseTranspose_inverseTranspose` and
  `Matrix.GeneralLinearGroup.inverseTranspose_symm`: inverse transpose is involutive.
* `Matrix.GeneralLinearGroup.unop_transposeMulEquiv_eq_inverseTranspose_inv`: transpose is
  inverse transpose of the inverse.
* `Matrix.GeneralLinearGroup.map_inverseTranspose`: naturality under ring homomorphisms.
* `TauCeti.inverseTranspose_diagGL`: action on diagonal matrices.
* `TauCeti.inverseTranspose_permutationGL`: permutation matrices are fixed.
* `TauCeti.inverseTranspose_transvectionUnit`: action on elementary transvections.
* `TauCeti.mem_unitarySubgroup_GL_iff_inverseTranspose_eq`: over a commutative star ring, an
  invertible matrix is unitary exactly when its inverse transpose is its entrywise star.

## Formalization source

The transpose-and-units composition is Mathlib's
`Matrix.GeneralLinearGroup.transposeMulEquiv`. Here it is composed with inversion and generalized
from Mathlib's commutative-ring coefficients to commutative semirings.
-/

public section

open Matrix

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Type*} [CommSemiring A]

/-- **Inverse transpose on the general linear group.** This is the group automorphism
`g ↦ (g⁻¹)ᵀ`, induced by `Matrix.transposeRingEquiv` and inversion into the opposite group. -/
def inverseTranspose : GL n A ≃* GL n A :=
  ((Units.mapEquiv (Matrix.transposeRingEquiv n A).toMulEquiv).trans Units.opEquiv).trans
    (MulEquiv.inv' (GL n A)).symm

/-- The matrix underlying inverse transpose is `(g⁻¹)ᵀ`. -/
@[simp]
theorem coe_inverseTranspose (g : GL n A) :
    (inverseTranspose g : Matrix n n A) = ((g⁻¹ : GL n A) : Matrix n n A).transpose := by
  simp [inverseTranspose, MulEquiv.inv', Units.mapEquiv, Units.opEquiv,
    Matrix.transposeRingEquiv]

/-- Inverse transpose is an involution. -/
@[simp]
theorem inverseTranspose_inverseTranspose (g : GL n A) :
    inverseTranspose (inverseTranspose g) = g := by
  apply Units.ext
  simp only [← map_inv, coe_inverseTranspose, inv_inv, Matrix.transpose_transpose]

/-- Inverse transpose is its own inverse automorphism. -/
@[simp]
theorem inverseTranspose_symm :
    (inverseTranspose : GL n A ≃* GL n A).symm = inverseTranspose :=
  MulEquiv.ext fun g ↦ by rw [MulEquiv.symm_apply_eq, inverseTranspose_inverseTranspose]

/-- Over a commutative ring, the transpose of an invertible matrix is the inverse transpose of its
inverse. -/
theorem unop_transposeMulEquiv_eq_inverseTranspose_inv {R : Type*} [CommRing R] (g : GL n R) :
    (transposeMulEquiv n g).unop = inverseTranspose g⁻¹ :=
  Units.ext <| by rw [coe_unop_transposeMulEquiv, coe_inverseTranspose, inv_inv]

variable {B : Type*} [CommSemiring B]

/-- Inverse transpose commutes with entrywise application of a semiring homomorphism. -/
@[simp]
theorem map_inverseTranspose (f : A →+* B) (g : GL n A) :
    Units.map (MonoidHom.ofClass (f.mapMatrix (m := n))) (inverseTranspose g) =
      inverseTranspose (Units.map (MonoidHom.ofClass (f.mapMatrix (m := n))) g) := by
  apply Units.ext
  simp [coe_inverseTranspose, ← map_inv, Matrix.transpose_map]

end Matrix.GeneralLinearGroup

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Type*}

/-- Inverse transpose inverts the entries of an invertible diagonal matrix. -/
@[simp]
theorem inverseTranspose_diagGL [CommSemiring A] (d : n → Aˣ) :
    Matrix.GeneralLinearGroup.inverseTranspose (diagGL d) = diagGL (fun i => (d i)⁻¹) := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.coe_inverseTranspose, ← map_inv, diagGL_coe]

/-- Inverse transpose fixes every permutation matrix. -/
@[simp]
theorem inverseTranspose_permutationGL [CommSemiring A] (σ : Equiv.Perm n) :
    Matrix.GeneralLinearGroup.inverseTranspose (permutationGL (k := A) σ) =
      permutationGL (k := A) σ := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.coe_inverseTranspose, ← map_inv, permutationGL_coe,
    Matrix.transpose_permMatrix]

/-- Inverse transpose swaps the indices of a transvection and negates its parameter. -/
@[simp]
theorem inverseTranspose_transvectionUnit [CommRing A] {i j : n} (hij : i ≠ j) (c : A) :
    Matrix.GeneralLinearGroup.inverseTranspose (transvectionUnit hij c) =
      transvectionUnit hij.symm (-c) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, transvectionUnit_inv,
    coe_transvectionUnit, coe_transvectionUnit]
  simp [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_single]

/-- Over a commutative star ring, an invertible matrix is unitary exactly when its inverse
transpose is its entrywise star. -/
theorem mem_unitarySubgroup_GL_iff_inverseTranspose_eq [CommRing A] [StarRing A] (g : GL n A) :
    g ∈ unitarySubgroup (GL n A) ↔
      Matrix.GeneralLinearGroup.inverseTranspose g =
        Matrix.GeneralLinearGroup.map (starRingEnd A) g := by
  have hstar : (Matrix.GeneralLinearGroup.map (starRingEnd A) g : Matrix n n A)ᵀ =
      star (g : Matrix n n A) := by
    ext i j
    simp [Matrix.star_apply, starRingEnd_apply]
  rw [mem_unitarySubgroup_GL_iff_mem_unitaryGroup, Matrix.mem_unitaryGroup_iff, Units.ext_iff,
    Matrix.GeneralLinearGroup.coe_inverseTranspose, ← Matrix.transpose_inj (A := _ᵀ),
    Matrix.transpose_transpose, hstar]
  exact ⟨Units.inv_eq_of_mul_eq_one_right, fun h ↦ h ▸ Units.mul_inv g⟩

end TauCeti
