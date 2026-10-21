/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Equivalence

/-!
# Scheme points and coordinate Hopf-algebra points

For an arbitrary affine group scheme, the counit
`TauCeti.AffineGroupSchemeCat.hopfSpecCoordinateHopfAlgebraIso` transports
`CommHopfAlgCat.pointsFunctorIsoAlgebraPointsFunctor` to its coordinate Hopf algebra.
The resulting natural isomorphism of group-valued functors on commutative algebras retains
multiplication as well as naturality. Both component formulas are explicit: pass to the Hopf
spectrum through that counit, then use the spectrum-points equivalence. No finite-type
or smoothness hypothesis is needed.

The naturality calculation is `TauCeti.CommHopfAlgCat.mapMulEquiv_mapValue`.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

universe u

namespace TauCeti.AffineGroupSchemeCat

/-- Scheme points of an affine group scheme are naturally the convolution points of the
coordinate Hopf algebra supplied by the affine anti-equivalence. -/
noncomputable def algebraPointsFunctorIsoCoordinatePointsFunctor (R : Type u) [CommRing R]
    (G : AffineGroupSchemeCat (CommRingCat.of R)) :
    GroupScheme.algebraPointsFunctor R G.obj ≅
      HopfAlgebra.pointsFunctor (R := R)
        (H := ((commHopfAlgCatOpEquivAffineGroupSchemeCat
          (CommRingCat.of R)).inverse.obj G).unop) :=
  (Functor.isoWhiskerLeft _
    (yonedaGrp.mapIso (hopfSpecCoordinateHopfAlgebraIso R G))).symm ≪≫
    (_root_.CommHopfAlgCat.pointsFunctorIsoAlgebraPointsFunctor _).symm

/-- To read a scheme point as a coordinate point, first pass to the Hopf spectrum using the
inverse counit of the affine anti-equivalence. -/
theorem algebraPointsFunctorIsoCoordinatePointsFunctor_hom_app_apply
    (R : Type u) [CommRing R] (G : AffineGroupSchemeCat (CommRingCat.of R))
    (A : CommAlgCat.{u} R)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶ G.obj.X) :
    (algebraPointsFunctorIsoCoordinatePointsFunctor R G).hom.app A p =
      Spec.mapMulEquiv.symm (p ≫ (hopfSpecCoordinateHopfAlgebraIso R G).inv.hom.hom) := by
  rw [algebraPointsFunctorIsoCoordinatePointsFunctor, Iso.trans_hom, NatTrans.comp_app]
  -- Whiskering evaluates `yonedaGrp.mapIso` at `Spec A`; its inverse component is
  -- postcomposition by the inverse counit. Evaluation of the `GrpCat` composite reduces
  -- definitionally to applying the spectrum-points comparison to that composite.
  exact _root_.CommHopfAlgCat.pointsFunctorIsoAlgebraPointsFunctor_inv_app_apply _ A _

/-- A coordinate point defines a scheme point through the counit of the affine
anti-equivalence. -/
theorem algebraPointsFunctorIsoCoordinatePointsFunctor_inv_app_apply
    (R : Type u) [CommRing R] (G : AffineGroupSchemeCat (CommRingCat.of R))
    (A : CommAlgCat.{u} R)
    (p : WithConv (((commHopfAlgCatOpEquivAffineGroupSchemeCat
      (CommRingCat.of R)).inverse.obj G).unop →ₐ[R] A)) :
    (algebraPointsFunctorIsoCoordinatePointsFunctor R G).inv.app A p =
      Spec.mapMulEquiv p ≫ (hopfSpecCoordinateHopfAlgebraIso R G).hom.hom.hom := by
  rw [algebraPointsFunctorIsoCoordinatePointsFunctor, Iso.trans_inv, NatTrans.comp_app]
  -- The whiskered `yonedaGrp.mapIso` component is postcomposition by the counit;
  -- evaluation of the `GrpCat` composite reduces definitionally to that operation.
  exact congrArg (fun q ↦ q ≫ (hopfSpecCoordinateHopfAlgebraIso R G).hom.hom.hom)
    (_root_.CommHopfAlgCat.pointsFunctorIsoAlgebraPointsFunctor_hom_app_apply _ A p)

end TauCeti.AffineGroupSchemeCat
