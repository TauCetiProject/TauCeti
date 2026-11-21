/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.PointsSheaf
public import TauCeti.Algebra.AlgebraicGroup.Fppf.Quotient.Homogeneous.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Scheme.Basic

/-!
# Represented fppf homogeneous quotients

Let `H` be a commutative Hopf algebra over a commutative ring `R`, and let `I` be a Hopf ideal
of `H`. Whenever a scheme `Q` over `Spec R` represents the fppf homogeneous quotient `G / N` cut
out by `I` — that is, via an isomorphism of fppf sheaves
`e : fppfHomogeneousQuotient H I ≅ CommAlgCat.pointsSheaf Q` — the quotient projection
`G ⟶ G / N` descends by full faithfulness of `CommAlgCat.pointsSheafFunctor` to a scheme morphism
`quotientMapOfRep H I e : Spec H ⟶ Q` over `Spec R` that is fppf locally surjective on affine
points sheaves.

We also record the compatibility of `hopfPointMulEquiv` with the subgroup inclusion
`Spec (H ⧸ I) ⟶ Spec H` on `A`-valued points for an arbitrary Hopf ideal `I`.

## Main declarations

* `TauCeti.CommHopfAlgCat.hopfPointMulEquiv_quotientPointsHom`: `hopfPointMulEquiv` intertwines
  the inclusion of `H ⧸ I`-points into `H`-points with postcomposition by `quotientSpecι H I`.
* `CommHopfAlgCat.quotientMapOfRep`: the quotient morphism `Spec H ⟶ Q` induced by an fppf
  sheaf isomorphism identifying `G / N` with `CommAlgCat.pointsSheaf Q`.
* `CommHopfAlgCat.hopfPointsToPointsSheaf_quotientMapOfRep`: on convolution points,
  `quotientMapOfRep` agrees with the fppf quotient projection composed with the representing
  isomorphism.
* `CommHopfAlgCat.isLocallySurjective_quotientMapOfRep`: `quotientMapOfRep` is fppf locally
  surjective on affine points sheaves.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5.c, homogeneous spaces and quotient sheaves.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite

namespace TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{u} R)

/-- `hopfPointMulEquiv` intertwines the inclusion `quotientPointsHom` of `H ⧸ I`-points into
`H`-points with postcomposition by the closed-subgroup immersion `quotientSpecι H I`. -/
theorem hopfPointMulEquiv_quotientPointsHom
    (I : HopfIdeal R H) (A : CommAlgCat.{u} R)
    (q : HopfAlgebra.points (R := R) (H := _root_.CommHopfAlgCat.quotient H I) A) :
    hopfPointMulEquiv H A (quotientPointsHom H I A q) =
      hopfPointMulEquiv (_root_.CommHopfAlgCat.quotient H I) A q ≫
        (quotientSpecι H I).hom.hom := by
  rw [quotientPointsHom, quotientSpecι_def]
  exact hopfPointMulEquiv_mapPointsFunctor A (_root_.CommHopfAlgCat.mkQuotient H I) q

end TauCeti.CommHopfAlgCat

namespace CommHopfAlgCat

open TauCeti TauCeti.CommHopfAlgCat

universe u

variable {R : Type u} [CommRing R] (H : _root_.CommHopfAlgCat.{u} R)

/-- The quotient morphism `Spec H ⟶ Q` induced by an fppf sheaf isomorphism identifying `G / N`
with the points sheaf of a representing scheme `Q`. -/
noncomputable def quotientMapOfRep (I : HopfIdeal R H) {Q : Over (Spec (CommRingCat.of R))}
    (e : fppfHomogeneousQuotient H I ≅ TauCeti.CommAlgCat.pointsSheaf Q) :
    ((hopfSpec (CommRingCat.of R)).obj (op H)).X ⟶ Q :=
  pointsSheafHomOfHopfPoints H (fppfHomogeneousQuotientProjection H I ≫ e.hom.hom)

/-- On convolution points, `quotientMapOfRep` agrees with the fppf quotient projection composed
with the representing isomorphism. -/
@[simp]
theorem hopfPointsToPointsSheaf_quotientMapOfRep (I : HopfIdeal R H)
    {Q : Over (Spec (CommRingCat.of R))}
    (e : fppfHomogeneousQuotient H I ≅ TauCeti.CommAlgCat.pointsSheaf Q) :
    hopfPointsToPointsSheaf H (quotientMapOfRep H I e) =
      fppfHomogeneousQuotientProjection H I ≫ e.hom.hom :=
  hopfPointsToPointsSheaf_pointsSheafHomOfHopfPoints H _

/-- The scheme quotient morphism induced by any representing model of `G / N` is fppf locally
surjective on affine points sheaves. -/
instance isLocallySurjective_quotientMapOfRep (I : HopfIdeal R H)
    {Q : Over (Spec (CommRingCat.of R))}
    (e : fppfHomogeneousQuotient H I ≅ TauCeti.CommAlgCat.pointsSheaf Q) :
    Presheaf.IsLocallySurjective (TauCeti.CommAlgCat.fppfTopology R)
      (TauCeti.CommAlgCat.pointsSheafMap (quotientMapOfRep H I e)).hom := by
  have : IsIso e.hom.hom :=
    ((sheafToPresheaf (TauCeti.CommAlgCat.fppfTopology R) (Type (u + 1))).mapIso e).isIso_hom
  have : Presheaf.IsLocallySurjective (TauCeti.CommAlgCat.fppfTopology R)
      (fppfHomogeneousQuotientProjection H I ≫ e.hom.hom) :=
    Presheaf.isLocallySurjective_comp (TauCeti.CommAlgCat.fppfTopology R) _ _
  unfold quotientMapOfRep
  infer_instance

end CommHopfAlgCat
