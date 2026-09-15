/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Sesquilinear
public import TauCeti.LinearAlgebra.BilinearMap.GramCongruence

/-!
# Matrices of the graded Ext--Euler pairing

The graded Ext--Euler pairing is Laurent-sesquilinear: the involution
`LaurentPolynomial.invert` acts on its first argument and the second argument is linear. This file
records its matrix in independently chosen bases and proves the corresponding change-of-basis
formula. The first coordinate matrix is transposed after applying `q ↦ q⁻¹` entrywise, while the
second coordinate matrix is unchanged.

No symmetry is assumed. In particular, the source and target properties and their bases may be
different. This distinction is essential for the projective/simple matrices of nonsymmetric Euler
forms.

## Main definitions

* `TauCeti.gradedExtEulerMatrix`: the matrix of the graded Ext--Euler pairing in two bases.

## Main results

* `TauCeti.gradedExtEulerMatrix_apply`: a matrix entry is the pairing of the corresponding basis
  vectors.
* `TauCeti.gradedExtEulerMatrix_of_of`: when two basis vectors are object classes, their entry is
  the object-level graded Ext--Euler characteristic.
* `TauCeti.gradedExtEulerMatrix_basis_change`: changing the two bases transforms the matrix by an
  involution-transpose on the left and an ordinary coordinate matrix on the right.

The convention follows Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices",
*Journal of Combinatorial Theory, Series A* **185** (2022), Sections 1.2 and 3.1--3.2: a
q-antilinear first argument forces conjugate transpose on the left change-of-basis matrix.
-/

public section

namespace TauCeti

open CategoryTheory LaurentPolynomial

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type t} [Field k] [Linear k C]
  [HasExt.{w} C] (e : C ≌ C) [e.functor.Additive] [e.functor.Linear k]
variable (P Q : ObjectProperty C) [LocallySmall.{w} C]
  [ObjectProperty.EssentiallySmall.{w} P] [ObjectProperty.EssentiallySmall.{w} Q]
  [P.ContainsZero] [P.IsClosedUnderBinaryProducts]
  [Q.ContainsZero] [Q.IsClosedUnderBinaryProducts]

local instance : P.IsClosedUnderIsomorphisms :=
  ObjectProperty.isClosedUnderIsomorphisms_of_containsZero P

local instance : Q.IsClosedUnderIsomorphisms :=
  ObjectProperty.isClosedUnderIsomorphisms_of_containsZero Q

/-- **The matrix of the graded Ext--Euler pairing** in independently chosen bases of the Laurent
Grothendieck groups selected by `P` and `Q`. Neither symmetry nor equal source and target modules
is required. -/
noncomputable def gradedExtEulerMatrix
    (hP : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed P)
    (hQ : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed Q)
    (hPshift : P.inverseImage (GradedExactStructure.abelian C e).shift.functor = P)
    (hQshift : Q.inverseImage (GradedExactStructure.abelian C e).shift.functor = Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q)
    {I J : Type*}
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory P hP hPshift)))
    (bQ : Module.Basis J (LaurentPolynomial ℤ)
      (LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory Q hQ hQshift))) :
    Matrix I J (LaurentPolynomial ℤ) :=
  LinearMap.toMatrix₂Aux (LaurentPolynomial ℤ) bP bQ
    (gradedExtEulerSesquilinear hP hQ hPshift hQshift h)

/-- An entry of the graded Ext--Euler matrix is the pairing of the corresponding basis vectors. -/
@[simp]
theorem gradedExtEulerMatrix_apply
    (hP : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed P)
    (hQ : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed Q)
    (hPshift : P.inverseImage (GradedExactStructure.abelian C e).shift.functor = P)
    (hQshift : Q.inverseImage (GradedExactStructure.abelian C e).shift.functor = Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q)
    {I J : Type*}
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory P hP hPshift)))
    (bQ : Module.Basis J (LaurentPolynomial ℤ)
      (LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory Q hQ hQshift)))
    (i : I) (j : J) :
    gradedExtEulerMatrix e P Q hP hQ hPshift hQshift h bP bQ i j =
      gradedExtEulerSesquilinear hP hQ hPshift hQshift h (bP i) (bQ j) := by
  rw [gradedExtEulerMatrix, LinearMap.toMatrix₂Aux_apply]

/-- If two basis vectors are classes of objects, their graded Ext--Euler matrix entry is the
object-level graded Ext--Euler characteristic. -/
theorem gradedExtEulerMatrix_of_of
    (hP : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed P)
    (hQ : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed Q)
    (hPshift : P.inverseImage (GradedExactStructure.abelian C e).shift.functor = P)
    (hQshift : Q.inverseImage (GradedExactStructure.abelian C e).shift.functor = Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q)
    {I J : Type*}
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory P hP hPshift)))
    (bQ : Module.Basis J (LaurentPolynomial ℤ)
      (LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory Q hQ hQshift)))
    (i : I) (j : J) (X : P.FullSubcategory) (Y : Q.FullSubcategory)
    (hi : bP i = LaurentK0.of _ X) (hj : bQ j = LaurentK0.of _ Y) :
    gradedExtEulerMatrix e P Q hP hQ hPshift hQshift h bP bQ i j =
      gradedExtEuler k e (h.isGradedEulerAdmissible X.property Y.property) := by
  rw [gradedExtEulerMatrix_apply, hi, hj,
    gradedExtEulerSesquilinear_of_of hP hQ hPshift hQshift h]

/-- **Involution-transpose change of basis for the graded Ext--Euler matrix.** The first basis
matrix is transformed entrywise by `LaurentPolynomial.invert` and transposed, while the second
basis matrix acts without the involution. This is the matrix law forced by q-antilinearity in the
first argument and q-linearity in the second. -/
theorem gradedExtEulerMatrix_basis_change
    (hP : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed P)
    (hQ : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed Q)
    (hPshift : P.inverseImage (GradedExactStructure.abelian C e).shift.functor = P)
    (hQshift : Q.inverseImage (GradedExactStructure.abelian C e).shift.functor = Q)
    (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q)
    {I J I' J' : Type*} [Fintype I] [Fintype J]
    (bP : Module.Basis I (LaurentPolynomial ℤ)
      (LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory P hP hPshift)))
    (bQ : Module.Basis J (LaurentPolynomial ℤ)
      (LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory Q hQ hQshift)))
    (cP : Module.Basis I' (LaurentPolynomial ℤ)
      (LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory P hP hPshift)))
    (cQ : Module.Basis J' (LaurentPolynomial ℤ)
      (LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory Q hQ hQshift))) :
    Matrix.transpose ((bP.toMatrix cP).map (LaurentPolynomial.invert (R := ℤ))) *
        gradedExtEulerMatrix e P Q hP hQ hPshift hQshift h bP bQ * bQ.toMatrix cQ =
      gradedExtEulerMatrix e P Q hP hQ hPshift hQshift h cP cQ := by
  exact LinearMap.toMatrix₂Aux_mul_map_basis_toMatrixₛₗ
    (gradedExtEulerSesquilinear hP hQ hPshift hQshift h) bP bQ cP cQ

end TauCeti
