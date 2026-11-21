/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.GroupLaw
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.FlatDescent
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.GroupLaw

/-!
# Base change of closed subgroup schemes of an elliptic curve

Let `g : E' ⟶ E` be a morphism of elliptic curves lying over `f : S' ⟶ S`, such that the square
formed by `g`, `f` and the two structure morphisms is a pullback square, and carrying the zero
section of `E'` to that of `E`. The inverse image along `g` of a closed subgroup scheme of `E` is a
closed subgroup scheme of `E'` (`EllipticCurveGeom.exists_grpObj_isMonHom_comap`). This is what
makes level structures defined through subgroup schemes, such as cyclic subgroups, pull back along
base change.

Conversely, when `f` is flat and surjective, a closed subscheme of `E` is a subgroup scheme as soon
as its inverse image in `E'` is
(`EllipticCurveGeom.exists_grpObj_isMonHom_comap_iff_of_flat_of_surjective`), with no finiteness
or flatness hypothesis on the subscheme.

Both are the elliptic-curve cases of the corresponding statements for group schemes,
`TauCeti.GroupScheme.exists_grpObj_isMonHom_comap` and
`TauCeti.GroupScheme.exists_grpObj_isMonHom_comap_iff_of_flat_of_surjective`, since `g` is
compatible with the group laws (`EllipticCurveGeom.addition_comp_of_isPullback`).

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_grpObj_isMonHom_comap`: the inverse image of
  a closed subgroup scheme of `E` along `g` is a closed subgroup scheme of `E'`.
* `EllipticCurveGeom.exists_grpObj_isMonHom_comap_iff_of_flat_of_surjective`: over a flat
  surjective `f`, a closed subscheme of `E` is a subgroup scheme exactly when its inverse image in
  `E'` is.

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
    (G' := Over.mk E'.structureMap) hg.w D
    (by rw [mul_left, mul_left]; exact addition_comp_of_isPullback hg h0) hD

include hg h0 in
/-- **Subgroup schemes descend along flat surjective morphisms.** Let `g : E' ⟶ E` be a morphism
of elliptic curves lying over a flat surjective `f : S' ⟶ S`, forming a pullback square with the
structure morphisms and carrying the zero section of `E'` to that of `E`, and let `V(D) ⊆ E` be a
closed subscheme, with no finiteness or flatness hypothesis. Then `V(D)` is a subgroup scheme of
`E` exactly when its inverse image in `E'` is a subgroup scheme of `E'`. The base-change direction
(`.mpr`) is `EllipticCurveGeom.exists_grpObj_isMonHom_comap`, which needs no hypothesis on `f`. -/
theorem exists_grpObj_isMonHom_comap_iff_of_flat_of_surjective (D : E.carrier.IdealSheafData)
    [Flat f] [Surjective f] :
    (∃ _ : GrpObj (Over.mk ((D.comap g).subschemeι ≫ E'.structureMap)),
      IsMonHom (Over.homMk (D.comap g).subschemeι :
        Over.mk ((D.comap g).subschemeι ≫ E'.structureMap) ⟶ Over.mk E'.structureMap)) ↔
      ∃ _ : GrpObj (Over.mk (D.subschemeι ≫ E.structureMap)),
        IsMonHom (Over.homMk D.subschemeι :
          Over.mk (D.subschemeι ≫ E.structureMap) ⟶ Over.mk E.structureMap) :=
  GroupScheme.exists_grpObj_isMonHom_comap_iff_of_flat_of_surjective
    (G := Over.mk E.structureMap) (G' := Over.mk E'.structureMap) hg
    (by rw [mul_left, mul_left]; exact addition_comp_of_isPullback hg h0) D

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
