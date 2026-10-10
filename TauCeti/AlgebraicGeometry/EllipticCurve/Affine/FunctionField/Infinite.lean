/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `WeierstrassCurve.Affine.pointEquivDegreeZeroDivisorClass` occurs in the statement about classes.
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Divisor.Class
-- `WeierstrassCurve.Affine.translationHom` is the injection of the points into the automorphism
-- group.
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Translation.Basic

/-!
# Classes and automorphisms of an elliptic function field with infinitely many points

An elliptic curve with infinitely many rational points has a function field with two infinitudes of
its own, each by transport along an identification already in the tree.

The degree-zero divisor classes of the function field are the rational points
(`pointEquivDegreeZeroDivisorClass`), so `Cl⁰` is infinite. The translations are automorphisms of
the function field over the constants, one for each point and distinct for distinct points
(`translationHom_injective`), so the **automorphism group is infinite**.

The hypothesis holds over a separably closed field, where `WeierstrassCurve.Affine.infinite_point`
supplies it from the `ℓ`-torsion counts, and that is the case the theory of function fields cares
about: it is why finiteness of the automorphism group, and the Hurwitz bound `|G| ≤ 84 (g - 1)` on
its finite subgroups, need genus at least two, since in genus one over `k̄` the whole group is
already infinite. Over a field that is not separably closed the group can be finite — over a finite
field it is, the degree-zero class group being finite there.

## Main results

* `WeierstrassCurve.Affine.infinite_degreeZeroDivisorClass`: the degree-zero divisor classes of the
  function field are infinite.
* `WeierstrassCurve.Affine.infinite_algEquiv`: the automorphism group of the function field over the
  constants is infinite, witnessed by the translations.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Exercise 6.14.
-/

public section

namespace WeierstrassCurve.Affine

open TauCeti

variable {F : Type*} [Field F] (W : WeierstrassCurve.Affine F) [W.IsElliptic] [Infinite W.Point]

local instance : IsDedekindDomain W.CoordinateRing :=
  have := isIntegrallyClosed_coordinateRing W
  W.isDedekindDomain_coordinateRing_of_isIntegrallyClosed

/-- **The degree-zero divisor classes are infinite** when the curve has infinitely many rational
points: the two are identified. -/
theorem infinite_degreeZeroDivisorClass :
    Infinite (Divisor.degreeClass W.isFunctionField).ker := by
  classical
  exact Infinite.of_injective W.pointEquivDegreeZeroDivisorClass
    W.pointEquivDegreeZeroDivisorClass.injective

/-- **The automorphism group of the function field is infinite** when the curve has infinitely many
rational points, witnessed by the translations.  Over a separably closed field the hypothesis is
automatic, which is why the finiteness of the automorphism group of a function field, and the
Hurwitz bound on its finite subgroups, assume genus at least two. -/
theorem infinite_algEquiv : Infinite (W.FunctionField ≃ₐ[F] W.FunctionField) := by
  classical
  -- The base change of `W` along the identity of `F` is `W` itself, so its points are the same.
  have _ : Infinite (W⁄F).toAffine.Point := ‹Infinite W.Point›
  have _ : Infinite (Multiplicative (W⁄F).toAffine.Point) :=
    Infinite.of_injective Multiplicative.ofAdd Multiplicative.ofAdd.injective
  exact Infinite.of_injective (translationHom W) (translationHom_injective W)

end WeierstrassCurve.Affine
