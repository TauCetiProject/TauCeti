/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.PointPlace
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.DegreeOneReduction

/-!
# The reduction of the generic point

Let `W` be an elliptic curve over a field `F`. The generic point `(genericX, genericY)` is a
point of `W` over its own function field `F(W)`, and every point `P` of `W` has a place of
`F(W)`, of degree one (`WeierstrassCurve.Affine.pointEquivDegreeOnePlace`). At that place the
generic point **reduces to `P`**.

In the language of `Affine/Point/DegreeOneReduction.lean`, this is the statement that
`reductionOfDegreeEqOne` of the generic point at the place of `P` is `P`
(`WeierstrassCurve.Affine.reductionOfDegreeEqOne_genericPoint`). Any `F`-algebra map `τ` out of
`F(W)` carries the generic point to the tautological point of `τ`, and this identity is what the
reduction of such points is computed from: an isogeny's action on points in particular.

## Main results

* `WeierstrassCurve.Affine.valuation_pointPlace_genericX_sub_lt_one` and
  `WeierstrassCurve.Affine.valuation_pointPlace_genericY_sub_lt_one`: `x - a` and `y - b` vanish
  at the place of `(a, b)`.
* `WeierstrassCurve.Affine.reductionOfDegreeEqOne_genericPoint`: the generic point reduces to `P`
  at the place of `P`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.1, VII.2.1.
-/

public section

open Polynomial TauCeti

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : Affine F) [W.IsElliptic]

/-- The coordinate ring of an elliptic curve is a Dedekind domain. -/
-- Named: an anonymous `local instance` here gets the same generated name as the one in
-- `Affine/FunctionField/Genus.lean`, and the two modules are siblings under `PointPlace.lean`.
local instance isDedekindDomain_coordinateRing_of_isElliptic : IsDedekindDomain W.CoordinateRing :=
  have := isIntegrallyClosed_coordinateRing W
  W.isDedekindDomain_coordinateRing_of_isIntegrallyClosed

/-- **`x - a` vanishes at the place of `(a, b)`**: the class of `X - a` lies in the point ideal. -/
theorem valuation_pointPlace_genericX_sub_lt_one {x y : F} (h : W.Equation x y) :
    (Place.ofPrime F W.FunctionField (CoordinateRing.pointPlace h)).valuation
      (genericX W - algebraMap F W.FunctionField x) < 1 := by
  rw [← algebraMap_XClass, Place.valuation_ofPrime_algebraMap_lt_one_iff,
    CoordinateRing.pointPlace_asIdeal]
  exact Ideal.subset_span (Set.mem_insert _ _)

/-- **`y - b` vanishes at the place of `(a, b)`**: the class of `Y - b` lies in the point ideal. -/
theorem valuation_pointPlace_genericY_sub_lt_one {x y : F} (h : W.Equation x y) :
    (Place.ofPrime F W.FunctionField (CoordinateRing.pointPlace h)).valuation
      (genericY W - algebraMap F W.FunctionField y) < 1 := by
  rw [← algebraMap_YClass, Place.valuation_ofPrime_algebraMap_lt_one_iff,
    CoordinateRing.pointPlace_asIdeal]
  exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

variable [DecidableEq F]

/-- **The generic point reduces to `P` at the place of `P`.** -/
@[simp]
theorem reductionOfDegreeEqOne_genericPoint (P : W.Point) :
    reductionOfDegreeEqOne W (W.pointEquivDegreeOnePlace P).2 (genericPoint W) =
      Point.equivBaseChangeSelf W P := by
  rw [reductionOfDegreeEqOne_eq_iff]
  rcases P with _ | ⟨x, y, h⟩
  · rw [coe_pointEquivDegreeOnePlace_zero, ← Point.zero_def, map_zero, map_zero, sub_zero,
      mem_polePoints_iff, xCoord_genericPoint, Place.valuation_infinity, genericX_eq_algebraMap]
    exact Or.inr (one_lt_infinityPlace_X W)
  · rw [Point.equivBaseChangeSelf_some W h, genericPoint_eq_some,
      some_sub_baseChange_mem_polePoints_iff, coe_pointEquivDegreeOnePlace_some]
    exact ⟨valuation_pointPlace_genericX_sub_lt_one W h.1,
      valuation_pointPlace_genericY_sub_lt_one W h.1⟩

end WeierstrassCurve.Affine

end
