/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `WeierstrassCurve.Affine.pointEquivDegreeOnePlace` is the point--place dictionary the count of
-- points runs on, and `TauCeti.Place.degree_eq_one_of_isAlgClosed_of_isFunctionField` is what makes
-- every place rational.
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.PointPlace
-- `WeierstrassCurve.Affine.pointEquivDegreeZeroDivisorClass` occurs in the statement about classes.
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Divisor.Class
-- `WeierstrassCurve.Affine.translationHom` is the injection of the points into the automorphism
-- group.
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Basic
-- Non-public: `TauCeti.Place.infinite`, that a function field has infinitely many places, is the
-- engine of all three statements, in the proofs only.
import TauCeti.FieldTheory.FunctionField.Place.Existence

/-!
# An elliptic curve over an algebraically closed field: points, classes and automorphisms

Over an algebraically closed field of constants every place of an algebraic function field is
rational (`TauCeti.Place.degree_eq_one_of_isAlgClosed_of_isFunctionField`), and a function field
always has infinitely many places (`TauCeti.Place.infinite`). For an elliptic curve the point--place
dictionary identifies the rational points with the rational places
(`WeierstrassCurve.Affine.pointEquivDegreeOnePlace`), so the curve has **infinitely many rational
points**.

Two consequences follow by transport along merged identifications. The degree-zero divisor classes
of the function field are the points (`pointEquivDegreeZeroDivisorClass`), so `Cl⁰` is infinite.
The translations are automorphisms of the function field over the constants, one for each point and
distinct for distinct points (`translationHom_injective`), so the **automorphism group is
infinite**.

The last statement is why finiteness of the automorphism group of a function field, and the Hurwitz
bound `|G| ≤ 84 (g - 1)` on its finite subgroups, need genus at least two: in genus one over an
algebraically closed field the whole group is already infinite. Over a field that is not
algebraically closed the group can be finite — over a finite field it is, since the degree-zero
class group is then finite.

## Main results

* `WeierstrassCurve.Affine.infinite_point`: an elliptic curve over an algebraically closed field has
  infinitely many rational points.
* `WeierstrassCurve.Affine.infinite_degreeZeroDivisorClass`: hence infinitely many degree-zero
  divisor classes.
* `WeierstrassCurve.Affine.infinite_algEquiv`: hence an infinite automorphism group, witnessed by
  the translations.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Remark 1.1.17 and Exercise 6.14.
-/

public section

namespace WeierstrassCurve.Affine

open TauCeti

variable {F : Type*} [Field F] [IsAlgClosed F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

local instance : IsDedekindDomain W.CoordinateRing :=
  have := isIntegrallyClosed_coordinateRing W
  W.isDedekindDomain_coordinateRing_of_isIntegrallyClosed

/-- **An elliptic curve over an algebraically closed field has infinitely many rational points.**
Every place of the function field is rational and there are infinitely many places, so the
point--place dictionary has an infinite codomain. -/
theorem infinite_point : Infinite W.Point := by
  have _ : Infinite (Place F W.FunctionField) := Place.infinite W.isFunctionField
  have hsub : Infinite { P : Place F W.FunctionField // P.degree = 1 } :=
    Infinite.of_injective
      (fun P : Place F W.FunctionField ↦
        (⟨P, P.degree_eq_one_of_isAlgClosed_of_isFunctionField W.isFunctionField⟩ :
          { P : Place F W.FunctionField // P.degree = 1 }))
      fun _ _ h ↦ by simpa using h
  exact Infinite.of_injective W.pointEquivDegreeOnePlace.symm
    W.pointEquivDegreeOnePlace.symm.injective

/-- **The degree-zero divisor classes of an elliptic function field over an algebraically closed
field are infinite**: they are the rational points. -/
theorem infinite_degreeZeroDivisorClass :
    Infinite (Divisor.degreeClass W.isFunctionField).ker := by
  classical
  have _ : Infinite W.Point := W.infinite_point
  exact Infinite.of_injective W.pointEquivDegreeZeroDivisorClass
    W.pointEquivDegreeZeroDivisorClass.injective

/-- **The automorphism group of an elliptic function field over an algebraically closed field is
infinite**, witnessed by the translations.  This is why the finiteness of the automorphism group of
a function field, and the Hurwitz bound on its finite subgroups, assume genus at least two. -/
theorem infinite_algEquiv : Infinite (W.FunctionField ≃ₐ[F] W.FunctionField) := by
  classical
  -- The base change of `W` along the identity of `F` is `W` itself, so its points are the same.
  have _ : Infinite (W⁄F).toAffine.Point := W.infinite_point
  have _ : Infinite (Multiplicative (W⁄F).toAffine.Point) :=
    Infinite.of_injective Multiplicative.ofAdd Multiplicative.ofAdd.injective
  exact Infinite.of_injective (translationHom W) (translationHom_injective W)

end WeierstrassCurve.Affine
