/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.BaseChange.Points
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Torsion

/-!
# Points of the `n`-torsion of a base change

Let `T` be a scheme over `S` and `g : E' ⟶ E` a morphism of elliptic curves lying over `T ⟶ S`,
forming a pullback square with the structure morphisms and carrying the zero section of `E'` to that
of `E`; for instance `E'` is the base change `E_T` of `E`. The `T`-points of `E'` are the points of
`E` with values in `T` (`EllipticCurveGeom.pointsMulEquivOfIsPullback`). This file shows that the
same holds for the `n`-torsion: the `T`-points of `E'[n]` are the morphisms `T ⟶ E[n]` over `S`
(`EllipticCurveGeom.torsionPointsEquivOfIsPullback`). This is how `E[n]` and its subschemes
represent functors of torsion points on base changes of `E`.

## Main definitions

* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.torsionPointsEquivOfIsPullback`: the `T`-points of
  `E'[n]` are the points of `E[n]` with values in `T`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.3.1.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry.EllipticCurveGeom

variable {S : Scheme.{u}} {E : EllipticCurveGeom S} {T : Over S} {E' : EllipticCurveGeom T.left}
  {g : E'.carrier ⟶ E.carrier} (n : ℤ) (hg : IsPullback g E'.structureMap E.structureMap T.hom)
  (h0 : E'.zero ≫ g = T.hom ≫ E.zero)

/-- **The points of the `n`-torsion of a base change.** Let `T` be a scheme over `S` and
`g : E' ⟶ E` a morphism of elliptic curves lying over `T ⟶ S`, forming a pullback square with the
structure morphisms and carrying the zero section of `E'` to that of `E`. Then the `T`-points of
`E'[n]` are the points of `E[n]` with values in `T`: a `T`-point `P` of `E'[n]` corresponds to the
point of `E[n]` whose image in `E` is the image of `P` under `g`
(`torsionPointsEquivOfIsPullback_apply_torsionι`). -/
noncomputable def torsionPointsEquivOfIsPullback :
    (𝟙_ (Over T.left) ⟶ (E'.torsion n).X) ≃ (T ⟶ (E.torsion n).X) :=
  (E'.torsionPointsEquiv n _).symm.trans <|
    ((pointsMulEquivOfIsPullback hg h0).toEquiv.subtypeEquiv fun x ↦ by
      rw [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_zpow,
        MulEquiv.map_eq_one_iff]).trans (E.torsionPointsEquiv n _)

/-- The image in `E` of the point of `E[n]` corresponding to a `T`-point `P` of `E'[n]` is the
point of `E` corresponding to the image of `P` in `E'`. -/
@[simp]
theorem torsionPointsEquivOfIsPullback_apply_torsionι (P : 𝟙_ (Over T.left) ⟶ (E'.torsion n).X) :
    torsionPointsEquivOfIsPullback n hg h0 P ≫ E.torsionι n =
      pointsMulEquivOfIsPullback hg h0 (P ≫ E'.torsionι n) := by
  simp [torsionPointsEquivOfIsPullback]

end TauCeti.AlgebraicGeometry.EllipticCurveGeom
