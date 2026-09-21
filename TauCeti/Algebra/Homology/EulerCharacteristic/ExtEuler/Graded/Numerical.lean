/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.ExtEuler.Graded.Sesquilinear
public import TauCeti.LinearAlgebra.SesquilinearForm.NumericalQuotient.Basic

/-!
# Numerical quotients of the graded Ext-Euler pairing

The graded Ext-Euler characteristic gives a Laurent-polynomial-valued sesquilinear pairing on
the Laurent-module Grothendieck groups of two extension-closed, shift-stable subcategories. This
file quotients the first group by the left radical and the second group by the right radical, and
descends the q-Euler form to the resulting numerical Grothendieck groups.

The two quotients are kept separate because the q-Euler form need not be symmetric or Hermitian.
The left radical is a Laurent submodule even though scalar multiplication in the first variable
is twisted by `LaurentPolynomial.invert`; this closure is built into the kernel of the semilinear
map. The generic numerical-quotient construction supplies the quotient modules and descended
pairings, while the results here expose their values in terms of graded Ext.

## Main definitions

* `TauCeti.GradedExtEulerLeftNumericalQuotient` and
  `TauCeti.GradedExtEulerRightNumericalQuotient`: the left and right numerical graded
  Grothendieck groups.
* `TauCeti.gradedExtEulerNumericalPairing`: the nondegenerate q-Euler pairing between both
  numerical quotients.

## Main results

* `TauCeti.mem_gradedExtEulerLeftRadical_iff` and
  `TauCeti.mem_gradedExtEulerRightRadical_iff` characterize the two radicals.
* `TauCeti.gradedExtEulerNumericalPairing_of_of` evaluates the quotient pairing on object
  classes.
* `TauCeti.gradedExtEulerNumericalPairing_nondegenerate` proves two-sided nondegeneracy after
  taking both quotients.

## References

The separate left and right numerical quotients for nonsymmetric q-pairings follow Zsuzsanna
Dancso and Anthony Licata, *Koszul algebras and flow lattices*, Section 3.1.
-/

public section

namespace TauCeti

open CategoryTheory LaurentPolynomial

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] {k : Type t} [Field k] [Linear k C]
  [HasExt.{w} C] {e : C ≌ C} [e.functor.Additive] [e.functor.Linear k]

variable {P Q : ObjectProperty C} [LocallySmall.{w} C]
  [ObjectProperty.EssentiallySmall.{w} P] [ObjectProperty.EssentiallySmall.{w} Q]
  [P.ContainsZero] [P.IsClosedUnderBinaryProducts]
  [Q.ContainsZero] [Q.IsClosedUnderBinaryProducts]

variable (hP : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed P)
  (hQ : (GradedExactStructure.abelian C e).toExactStructure.IsExtensionClosed Q)
  (hPshift : P.inverseImage (GradedExactStructure.abelian C e).shift.functor = P)
  (hQshift : Q.inverseImage (GradedExactStructure.abelian C e).shift.functor = Q)
  (h : IsGradedEulerAdmissibleOn.{w} (k := k) (e := e) P Q)

/-- The left numerical quotient of the first Laurent-module Grothendieck group for the graded
Ext-Euler pairing. -/
abbrev GradedExtEulerLeftNumericalQuotient :=
  LeftNumericalQuotient (gradedExtEulerSesquilinear hP hQ hPshift hQshift h)

/-- The right numerical quotient of the second Laurent-module Grothendieck group for the graded
Ext-Euler pairing. -/
abbrev GradedExtEulerRightNumericalQuotient :=
  RightNumericalQuotient (gradedExtEulerSesquilinear hP hQ hPshift hQshift h)

/-- The quotient map from the first Laurent-module Grothendieck group to its left graded
Ext-Euler numerical quotient. -/
noncomputable def gradedExtEulerLeftNumericalQuotientMk :
    LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory P hP hPshift) →ₗ[
      LaurentPolynomial ℤ] GradedExtEulerLeftNumericalQuotient hP hQ hPshift hQshift h :=
  leftNumericalQuotientMk (gradedExtEulerSesquilinear hP hQ hPshift hQshift h)

/-- The quotient map from the second Laurent-module Grothendieck group to its right graded
Ext-Euler numerical quotient. -/
noncomputable def gradedExtEulerRightNumericalQuotientMk :
    LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory Q hQ hQshift) →ₗ[
      LaurentPolynomial ℤ] GradedExtEulerRightNumericalQuotient hP hQ hPshift hQshift h :=
  rightNumericalQuotientMk (gradedExtEulerSesquilinear hP hQ hPshift hQshift h)

/-- The left radical of the graded Ext-Euler pairing consists exactly of the classes pairing to
zero with every class on the right. -/
theorem mem_gradedExtEulerLeftRadical_iff
    (x : LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory P hP hPshift)) :
    x ∈ leftRadical (gradedExtEulerSesquilinear hP hQ hPshift hQshift h) ↔
      ∀ y, gradedExtEulerSesquilinear hP hQ hPshift hQshift h x y = 0 :=
  mem_leftRadical_iff (gradedExtEulerSesquilinear hP hQ hPshift hQshift h) x

/-- The right radical of the graded Ext-Euler pairing consists exactly of the classes pairing to
zero with every class on the left. -/
theorem mem_gradedExtEulerRightRadical_iff
    (y : LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory Q hQ hQshift)) :
    y ∈ rightRadical (gradedExtEulerSesquilinear hP hQ hPshift hQshift h) ↔
      ∀ x, gradedExtEulerSesquilinear hP hQ hPshift hQshift h x y = 0 :=
  mem_rightRadical_iff (gradedExtEulerSesquilinear hP hQ hPshift hQshift h) y

/-- The one-sided q-Euler pairing after quotienting the left Laurent-module Grothendieck group. -/
noncomputable def gradedExtEulerLeftNumericalPairing :
    GradedExtEulerLeftNumericalQuotient hP hQ hPshift hQshift h →ₛₗ[
      (LaurentPolynomial.invert (R := ℤ)).toRingEquiv.toRingHom]
      LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory Q hQ hQshift) →ₗ[
        LaurentPolynomial ℤ] LaurentPolynomial ℤ :=
  leftNumericalPairing (gradedExtEulerSesquilinear hP hQ hPshift hQshift h)

/-- The one-sided q-Euler pairing after quotienting the right Laurent-module Grothendieck group. -/
noncomputable def gradedExtEulerRightNumericalPairing :
    LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory P hP hPshift) →ₛₗ[
      (LaurentPolynomial.invert (R := ℤ)).toRingEquiv.toRingHom]
      GradedExtEulerRightNumericalQuotient hP hQ hPshift hQshift h →ₗ[
        LaurentPolynomial ℤ] LaurentPolynomial ℤ :=
  rightNumericalPairing (gradedExtEulerSesquilinear hP hQ hPshift hQshift h)

/-- The graded Ext-Euler pairing between the left and right numerical Grothendieck groups. -/
noncomputable def gradedExtEulerNumericalPairing :
    GradedExtEulerLeftNumericalQuotient hP hQ hPshift hQshift h →ₛₗ[
      (LaurentPolynomial.invert (R := ℤ)).toRingEquiv.toRingHom]
      GradedExtEulerRightNumericalQuotient hP hQ hPshift hQshift h →ₗ[
        LaurentPolynomial ℤ] LaurentPolynomial ℤ :=
  numericalPairing (gradedExtEulerSesquilinear hP hQ hPshift hQshift h)

/-- The left numerical q-Euler pairing evaluates on a quotient representative as the original
graded Ext-Euler pairing. -/
@[simp]
theorem gradedExtEulerLeftNumericalPairing_mk
    (x : LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory P hP hPshift))
    (y : LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory Q hQ hQshift)) :
    gradedExtEulerLeftNumericalPairing hP hQ hPshift hQshift h
        (gradedExtEulerLeftNumericalQuotientMk hP hQ hPshift hQshift h x) y =
      gradedExtEulerSesquilinear hP hQ hPshift hQshift h x y := by
  rw [gradedExtEulerLeftNumericalPairing, gradedExtEulerLeftNumericalQuotientMk,
    leftNumericalPairing_mk]

/-- The right numerical q-Euler pairing evaluates on a quotient representative as the original
graded Ext-Euler pairing. -/
@[simp]
theorem gradedExtEulerRightNumericalPairing_mk
    (x : LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory P hP hPshift))
    (y : LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory Q hQ hQshift)) :
    gradedExtEulerRightNumericalPairing hP hQ hPshift hQshift h x
        (gradedExtEulerRightNumericalQuotientMk hP hQ hPshift hQshift h y) =
      gradedExtEulerSesquilinear hP hQ hPshift hQshift h x y := by
  rw [gradedExtEulerRightNumericalPairing, gradedExtEulerRightNumericalQuotientMk,
    rightNumericalPairing_mk]

/-- The numerical q-Euler pairing evaluates on quotient representatives as the original graded
Ext-Euler pairing. -/
@[simp]
theorem gradedExtEulerNumericalPairing_mk
    (x : LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory P hP hPshift))
    (y : LaurentK0 ((GradedExactStructure.abelian C e).fullSubcategory Q hQ hQshift)) :
    gradedExtEulerNumericalPairing hP hQ hPshift hQshift h
        (gradedExtEulerLeftNumericalQuotientMk hP hQ hPshift hQshift h x)
        (gradedExtEulerRightNumericalQuotientMk hP hQ hPshift hQshift h y) =
      gradedExtEulerSesquilinear hP hQ hPshift hQshift h x y := by
  rw [gradedExtEulerNumericalPairing, gradedExtEulerLeftNumericalQuotientMk,
    gradedExtEulerRightNumericalQuotientMk, numericalPairing_mk]

/-- The numerical q-Euler pairing evaluates on object classes as their graded Ext-Euler
characteristic. -/
theorem gradedExtEulerNumericalPairing_of_of (X : P.FullSubcategory) (Y : Q.FullSubcategory) :
    gradedExtEulerNumericalPairing hP hQ hPshift hQshift h
        (gradedExtEulerLeftNumericalQuotientMk hP hQ hPshift hQshift h (LaurentK0.of _ X))
        (gradedExtEulerRightNumericalQuotientMk hP hQ hPshift hQshift h (LaurentK0.of _ Y)) =
      gradedExtEuler k e (h.isGradedEulerAdmissible X.property Y.property) := by
  rw [gradedExtEulerNumericalPairing_mk, gradedExtEulerSesquilinear_of_of]

/-- The left numerical graded Ext-Euler pairing separates its left argument. -/
theorem gradedExtEulerLeftNumericalPairing_separatingLeft :
    (gradedExtEulerLeftNumericalPairing hP hQ hPshift hQshift h).SeparatingLeft :=
  leftNumericalPairing_separatingLeft
    (gradedExtEulerSesquilinear hP hQ hPshift hQshift h)

/-- The right numerical graded Ext-Euler pairing separates its right argument. -/
theorem gradedExtEulerRightNumericalPairing_separatingRight :
    (gradedExtEulerRightNumericalPairing hP hQ hPshift hQshift h).SeparatingRight :=
  rightNumericalPairing_separatingRight
    (gradedExtEulerSesquilinear hP hQ hPshift hQshift h)

/-- Quotienting by both graded Ext-Euler radicals makes the q-Euler pairing nondegenerate. -/
theorem gradedExtEulerNumericalPairing_nondegenerate :
    (gradedExtEulerNumericalPairing hP hQ hPshift hQshift h).Nondegenerate :=
  numericalPairing_nondegenerate (gradedExtEulerSesquilinear hP hQ hPshift hQshift h)

/-- The numerical q-Euler pairing is the unique sesquilinear pairing whose representative values
are the original graded Ext-Euler values. -/
theorem gradedExtEulerNumericalPairing_unique
    (b :
      GradedExtEulerLeftNumericalQuotient hP hQ hPshift hQshift h
        →ₛₗ[(LaurentPolynomial.invert (R := ℤ)).toRingEquiv.toRingHom]
          GradedExtEulerRightNumericalQuotient hP hQ hPshift hQshift h
            →ₗ[LaurentPolynomial ℤ] LaurentPolynomial ℤ)
    (hb : ∀ x y, b (gradedExtEulerLeftNumericalQuotientMk hP hQ hPshift hQshift h x)
        (gradedExtEulerRightNumericalQuotientMk hP hQ hPshift hQshift h y) =
          gradedExtEulerSesquilinear hP hQ hPshift hQshift h x y) :
    b = gradedExtEulerNumericalPairing hP hQ hPshift hQshift h := by
  apply numericalPairing_unique
    (gradedExtEulerSesquilinear hP hQ hPshift hQshift h) b
  intro x y
  simpa only [gradedExtEulerLeftNumericalQuotientMk,
    gradedExtEulerRightNumericalQuotientMk] using hb x y

end TauCeti
