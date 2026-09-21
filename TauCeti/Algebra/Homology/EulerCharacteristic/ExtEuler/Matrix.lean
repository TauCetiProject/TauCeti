/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Numerical
public import TauCeti.LinearAlgebra.BilinearMap.GramCongruence
public import TauCeti.LinearAlgebra.SesquilinearForm.NumericalQuotient.Basic

/-!
# Matrices of the Ext-Euler pairing

This file records the matrix of the Ext-Euler pairing in independently chosen bases of two exact
Grothendieck groups. No symmetry is assumed, so the source and target properties and their bases
may be different.

## Main definitions

* `TauCeti.extEulerMatrix`: the matrix of the Ext-Euler pairing in two bases.

## Main results

* `TauCeti.extEulerMatrix_apply`: a matrix entry is the pairing of the corresponding basis
  vectors.
* `TauCeti.extEulerMatrix_of_of`: when two basis vectors are object classes, their entry is the
  object-level Ext-Euler characteristic.
* `TauCeti.extEulerMatrix_basis_change`: changing the two bases transforms the matrix by the
  transposed first and the untransposed second change-of-basis matrix.
-/

public section

namespace TauCeti

open CategoryTheory
open scoped Matrix

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type t} [Field k] [Linear k C]
  [HasExt.{w} C]
variable (P Q : ObjectProperty C) [LocallySmall.{w} C]
  [ObjectProperty.EssentiallySmall.{w} P] [ObjectProperty.EssentiallySmall.{w} Q]
  [P.ContainsZero] [P.IsClosedUnderBinaryProducts]
  [Q.ContainsZero] [Q.IsClosedUnderBinaryProducts]

/-- **The matrix of the Ext-Euler pairing** in independently chosen bases of two exact
Grothendieck groups. Neither symmetry nor equal source and target groups is required. -/
noncomputable def extEulerMatrix
    (hP : (ExactStructure.abelian C).IsExtensionClosed P)
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsEulerAdmissibleOn.{w} k P Q) {I J : Type*}
    (bP : Module.Basis I ℤ (ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP)))
    (bQ : Module.Basis J ℤ (ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ))) :
    Matrix I J ℤ :=
  LinearMap.toMatrix₂Aux ℤ bP bQ (extEulerBilinear hP hQ h)

/-- An entry of the Ext-Euler matrix is the pairing of the corresponding basis vectors. -/
@[simp]
theorem extEulerMatrix_apply
    (hP : (ExactStructure.abelian C).IsExtensionClosed P)
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsEulerAdmissibleOn.{w} k P Q) {I J : Type*}
    (bP : Module.Basis I ℤ (ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP)))
    (bQ : Module.Basis J ℤ (ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ)))
    (i : I) (j : J) :
    extEulerMatrix P Q hP hQ h bP bQ i j = extEulerPairing hP hQ h (bP i) (bQ j) := by
  rw [extEulerMatrix, LinearMap.toMatrix₂Aux_apply, extEulerBilinear_apply]

/-- If two basis vectors are classes of objects, their Ext-Euler matrix entry is the object-level
Ext-Euler characteristic. -/
theorem extEulerMatrix_of_of
    (hP : (ExactStructure.abelian C).IsExtensionClosed P)
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsEulerAdmissibleOn.{w} k P Q) {I J : Type*}
    (bP : Module.Basis I ℤ (ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP)))
    (bQ : Module.Basis J ℤ (ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ)))
    (i : I) (j : J) (X : P.FullSubcategory) (Y : Q.FullSubcategory)
    (hi : bP i = ExactK0.of X) (hj : bQ j = ExactK0.of Y) :
    extEulerMatrix P Q hP hQ h bP bQ i j =
      extEuler.{w} k (h.isEulerAdmissible X.property Y.property) := by
  rw [extEulerMatrix_apply, hi, hj, extEulerPairing_of_of]

/-- **Change of basis for the Ext-Euler matrix.** The first change-of-basis matrix acts
transposed on the left and the second acts on the right, since the pairing is bilinear but not
symmetric. -/
theorem extEulerMatrix_basis_change
    (hP : (ExactStructure.abelian C).IsExtensionClosed P)
    (hQ : (ExactStructure.abelian C).IsExtensionClosed Q)
    (h : IsEulerAdmissibleOn.{w} k P Q) {I J I' J' : Type*} [Fintype I] [Fintype J]
    (bP : Module.Basis I ℤ (ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP)))
    (bQ : Module.Basis J ℤ (ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ)))
    (cP : Module.Basis I' ℤ (ExactK0 ((ExactStructure.abelian C).fullSubcategory P hP)))
    (cQ : Module.Basis J' ℤ (ExactK0 ((ExactStructure.abelian C).fullSubcategory Q hQ))) :
    (bP.toMatrix cP)ᵀ * extEulerMatrix P Q hP hQ h bP bQ * bQ.toMatrix cQ =
      extEulerMatrix P Q hP hQ h cP cQ := by
  simpa [extEulerMatrix] using LinearMap.toMatrix₂Aux_mul_map_basis_toMatrix
    (extEulerBilinear hP hQ h) bP bQ cP cQ

end TauCeti
