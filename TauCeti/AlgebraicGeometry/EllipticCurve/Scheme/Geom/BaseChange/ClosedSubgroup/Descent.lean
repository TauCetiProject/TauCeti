/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.GroupLaw
public import TauCeti.AlgebraicGeometry.GroupScheme.ClosedSubgroup.FlatDescent
public import TauCeti.AlgebraicGeometry.Morphisms.Flat.SchemeTheoreticallyDominant
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.GroupLaw

/-!
# Flat descent of closed subgroup schemes of an elliptic curve

Let `g : E' ⟶ E` be a morphism of elliptic curves lying over `f : S' ⟶ S`, such that the square
formed by `g`, `f` and the two structure morphisms is a pullback square, and carrying the zero
section of `E'` to that of `E`. If every base change of `f` is scheme-theoretically dominant, for
instance if `f` is flat and surjective, then a closed subscheme of `E` is a subgroup scheme as
soon as its inverse image in `E'` is. No finiteness or flatness hypothesis is placed on the
subscheme. The converse holds for any `f`
(`TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_grpObj_isMonHom_comap`).

This is the elliptic-curve case of `TauCeti.GroupScheme.exists_grpObj_isMonHom_comap_iff`, since
`g` is compatible with the group laws (`EllipticCurveGeom.addition_comp_of_isPullback`), and flat
surjective morphisms are universally scheme-theoretically dominant
(`AlgebraicGeometry.IsSchemeTheoreticallyDominant.universally_of_flat_of_surjective`).

## Main results

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.exists_grpObj_isMonHom_comap_iff`: along a
  universally scheme-theoretically dominant `f`, a closed subscheme of `E` is a subgroup scheme
  exactly when its inverse image in `E'` is.
* `EllipticCurveGeom.exists_grpObj_isMonHom_comap_iff_of_flat_of_surjective`: the same along a
  flat surjective `f`.

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
/-- **Subgroup schemes descend along universally scheme-theoretically dominant morphisms.** Let
`g : E' ⟶ E` be a morphism of elliptic curves lying over `f : S' ⟶ S`, all of whose base changes
are scheme-theoretically dominant, forming a pullback square with the structure morphisms and
carrying the zero section of `E'` to that of `E`, and let `V(D) ⊆ E` be a closed subscheme. Then
`V(D)` is a subgroup scheme of `E` exactly when its inverse image in `E'` is a subgroup scheme of
`E'`. -/
theorem exists_grpObj_isMonHom_comap_iff
    (hf : MorphismProperty.universally @IsSchemeTheoreticallyDominant f)
    (D : E.carrier.IdealSheafData) :
    (∃ _ : GrpObj (Over.mk ((D.comap g).subschemeι ≫ E'.structureMap)),
      IsMonHom (Over.homMk (D.comap g).subschemeι :
        Over.mk ((D.comap g).subschemeι ≫ E'.structureMap) ⟶ Over.mk E'.structureMap)) ↔
      ∃ _ : GrpObj (Over.mk (D.subschemeι ≫ E.structureMap)),
        IsMonHom (Over.homMk D.subschemeι :
          Over.mk (D.subschemeι ≫ E.structureMap) ⟶ Over.mk E.structureMap) :=
  GroupScheme.exists_grpObj_isMonHom_comap_iff (G := Over.mk E.structureMap)
    (G' := Over.mk E'.structureMap) hf hg
    (by simpa only [mul_left, Over.mk_hom] using addition_comp_of_isPullback hg h0) D

include hg h0 in
/-- **Subgroup schemes descend along flat surjective morphisms.** Let `g : E' ⟶ E` be a morphism
of elliptic curves lying over a flat surjective `f : S' ⟶ S`, forming a pullback square with the
structure morphisms and carrying the zero section of `E'` to that of `E`, and let `V(D) ⊆ E` be a
closed subscheme, with no finiteness or flatness hypothesis. Then `V(D)` is a subgroup scheme of
`E` exactly when its inverse image in `E'` is a subgroup scheme of `E'`. -/
theorem exists_grpObj_isMonHom_comap_iff_of_flat_of_surjective (D : E.carrier.IdealSheafData)
    [Flat f] [Surjective f] :
    (∃ _ : GrpObj (Over.mk ((D.comap g).subschemeι ≫ E'.structureMap)),
      IsMonHom (Over.homMk (D.comap g).subschemeι :
        Over.mk ((D.comap g).subschemeι ≫ E'.structureMap) ⟶ Over.mk E'.structureMap)) ↔
      ∃ _ : GrpObj (Over.mk (D.subschemeι ≫ E.structureMap)),
        IsMonHom (Over.homMk D.subschemeι :
          Over.mk (D.subschemeι ≫ E.structureMap) ⟶ Over.mk E.structureMap) :=
  exists_grpObj_isMonHom_comap_iff hg h0
    (IsSchemeTheoreticallyDominant.universally_of_flat_of_surjective f) D

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
