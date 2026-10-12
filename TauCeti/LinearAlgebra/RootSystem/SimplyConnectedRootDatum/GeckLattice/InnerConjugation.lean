/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.InnerConjugation
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.PointsFunctor

/-!
# Inner conjugation of the Geck carrier

This file realizes inner conjugation by any integral point of the Geck carrier as a group-scheme
automorphism and identifies its action on scheme-valued points.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv
open scoped CategoryTheory.MonObj

namespace TauCeti.DynkinType

noncomputable section

variable (t : DynkinType) (ht : t.Valid)

/-- **Inner conjugation by an integral Geck point**, as an automorphism of the Geck group scheme.
On points over a commutative ring it sends `x` to `g x g⁻¹`. -/
def geckInnerConjugation (g : t.geckPoints ht ℤ) : Aut (t.geckGroupScheme ht) :=
  (eqToIso (t.geckGroupScheme_eq_hopfSpec ht)).trans
    ((hopfSpec (CommRingCat.of ℤ)).mapIso
      (CommHopfAlgCat.innerConjugationIso (t.geckCoordinateHopfAlgebra ht)
        (t.geckCoordinatePoint ht g)).op) |>.trans
    (eqToIso (t.geckGroupScheme_eq_hopfSpec ht)).symm

/-- Inner conjugation by `g` is transported from the coordinate Hopf-algebra automorphism. -/
theorem geckInnerConjugation_def (g : t.geckPoints ht ℤ) :
    t.geckInnerConjugation ht g =
      ((eqToIso (t.geckGroupScheme_eq_hopfSpec ht)).trans
        ((hopfSpec (CommRingCat.of ℤ)).mapIso
          (CommHopfAlgCat.innerConjugationIso (t.geckCoordinateHopfAlgebra ht)
            (t.geckCoordinatePoint ht g)).op)).trans
          (eqToIso (t.geckGroupScheme_eq_hopfSpec ht)).symm :=
  (rfl)

/-- On presented scheme-valued points, `geckInnerConjugation` is induced by the coordinate inner
automorphism. -/
theorem geckGroupSchemePointMulEquiv_comp_geckInnerConjugation
    (g : t.geckPoints ht ℤ) (A : Type) [CommRing A]
    (q : HopfAlgebra.points (R := ℤ) (H := t.geckCoordinateHopfAlgebra ht)
      (CommAlgCat.of ℤ A)) :
    t.geckGroupSchemePointMulEquiv ht A q ≫
        (t.geckInnerConjugation ht g).hom.hom.hom =
      t.geckGroupSchemePointMulEquiv ht A
        ((CommHopfAlgCat.mapPointsFunctor
          (CommHopfAlgCat.innerConjugationIso (t.geckCoordinateHopfAlgebra ht)
            (t.geckCoordinatePoint ht g)).hom).app (CommAlgCat.of ℤ A) q) := by
  rw [geckInnerConjugation_def]
  exact CommHopfAlgCat.pointMulEquivOfPresentation_mapDomain (R := ℤ) A
    (t.geckGroupScheme_eq_hopfSpec ht) (t.geckGroupScheme_eq_hopfSpec ht)
    (t.geckGroupSchemePointMulEquiv ht A) (t.geckGroupSchemePointMulEquiv ht A)
    (t.geckGroupSchemePointMulEquiv_apply_left ht A)
    (t.geckGroupSchemePointMulEquiv_apply_left ht A)
    (CommHopfAlgCat.innerConjugationIso (t.geckCoordinateHopfAlgebra ht)
      (t.geckCoordinatePoint ht g)).hom q

/-- **On scheme-valued points, inner conjugation by an integral point is conjugation by its
image in the value ring.** -/
@[simp]
theorem geckSchemePointsMulEquiv_comp_geckInnerConjugation
    (g : t.geckPoints ht ℤ) (A : Type) [CommRing A]
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (t.geckGroupScheme ht).X) :
    t.geckSchemePointsMulEquiv ht A
        (p ≫ (t.geckInnerConjugation ht g).hom.hom.hom) =
      (t.geckPointsPresentation ht ℤ).map (t.geckPointsPresentation ht A)
          (Int.castRingHom A) g *
        t.geckSchemePointsMulEquiv ht A p *
        ((t.geckPointsPresentation ht ℤ).map (t.geckPointsPresentation ht A)
          (Int.castRingHom A) g)⁻¹ := by
  obtain ⟨q, rfl⟩ := (t.geckGroupSchemePointMulEquiv ht A).surjective p
  rw [t.geckGroupSchemePointMulEquiv_comp_geckInnerConjugation ht g A]
  rw [CommHopfAlgCat.mapPointsFunctor_innerConjugationIso_hom,
    HopfAlgebra.innerConjugationPointNatIso_hom_app_apply]
  rw [geckSchemePointsMulEquiv_groupSchemePointMulEquiv,
    geckSchemePointsMulEquiv_groupSchemePointMulEquiv]
  rw [map_mul, map_mul, map_inv,
    t.geckCoordinatePointMulEquiv_extendPoint_geckCoordinatePoint ht g A]

/-- Inner conjugation by the identity point is the identity group-scheme automorphism. -/
@[simp]
theorem geckInnerConjugation_one :
    t.geckInnerConjugation ht 1 = Iso.refl _ := by
  rw [geckInnerConjugation_def]
  have hpoint : t.geckCoordinatePoint ht 1 = 1 := by
    apply (t.geckCoordinatePointMulEquiv ht ℤ).injective
    rw [geckCoordinatePointMulEquiv_geckCoordinatePoint, map_one]
  rw [hpoint, CommHopfAlgCat.innerConjugationIso_one]
  apply Iso.ext
  simp

end

end TauCeti.DynkinType
