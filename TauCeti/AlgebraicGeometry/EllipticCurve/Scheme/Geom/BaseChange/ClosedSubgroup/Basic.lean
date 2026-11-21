/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.GroupLaw
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.GroupLaw

/-!
# Base change of closed subgroup schemes of an elliptic curve

Let `g : E' ⟶ E` be a morphism of elliptic curves lying over `f : S' ⟶ S`, such that the square
formed by `g`, `f` and the two structure morphisms is a pullback square, and carrying the zero
section of `E'` to that of `E`. The inverse image along `g` of a closed subgroup scheme of `E` is a
closed subgroup scheme of `E'` (`EllipticCurveGeom.exists_grpObj_isMonHom_comap`). This is what
makes level structures defined through subgroup schemes, such as cyclic subgroups, pull back along
base change.

This is the elliptic-curve case of the corresponding statement for group schemes,
`TauCeti.GroupScheme.exists_grpObj_isMonHom_comap`, since `g` is compatible with the group laws
(`EllipticCurveGeom.addition_comp_of_isPullback`). The converse, along flat surjective base
changes, is in
`TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.ClosedSubgroup.Descent`.

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_grpObj_isMonHom_comap`: the inverse image of
  a closed subgroup scheme of `E` along `g` is a closed subgroup scheme of `E'`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §1.3.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace EllipticCurveGeom

variable {S S' : Scheme.{u}} {E : EllipticCurveGeom S} {E' : EllipticCurveGeom S'}
  {g : E'.carrier ⟶ E.carrier} {f : S' ⟶ S} (hg : IsPullback g E'.structureMap E.structureMap f)
  (h0 : E'.zero ≫ g = f ≫ E.zero)

include hg h0 in
/-- **Closed subgroup schemes are stable under base change.** Let `g : E' ⟶ E` be a morphism of
elliptic curves lying over `f : S' ⟶ S`, forming a pullback square with the structure morphisms and
carrying the zero section of `E'` to that of `E`. If the closed subscheme of `E` cut out by an
ideal sheaf `D` is a subgroup scheme, then so is the closed subscheme of `E'` cut out by the
inverse image of `D` along `g`. -/
theorem exists_grpObj_isMonHom_comap (D : E.carrier.IdealSheafData)
    (hD : ∃ _ : GrpObj (Over.mk (D.subschemeι ≫ E.structureMap)),
      IsMonHom (Over.homMk D.subschemeι :
        Over.mk (D.subschemeι ≫ E.structureMap) ⟶ Over.mk E.structureMap)) :
    ∃ _ : GrpObj (Over.mk ((D.comap g).subschemeι ≫ E'.structureMap)),
      IsMonHom (Over.homMk (D.comap g).subschemeι :
        Over.mk ((D.comap g).subschemeι ≫ E'.structureMap) ⟶ Over.mk E'.structureMap) :=
  GroupScheme.exists_grpObj_isMonHom_comap (G := Over.mk E.structureMap)
    (G' := Over.mk E'.structureMap) hg.w
    (by simpa only [mul_left, Over.mk_hom] using addition_comp_of_isPullback hg h0) D hD

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
