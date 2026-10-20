/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.Points
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.SchemePoints
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Equivalence

/-!
# Scheme points and coordinate Hopf-algebra points

Mathlib's `Spec.mapMulEquiv` identifies convolution points of a Hopf algebra with
scheme-valued points of its spectrum. This file assembles the comparison as a natural
isomorphism of group-valued functors on commutative algebras. The group-valued statement
retains multiplication as well as naturality, unlike the underlying type-valued presheaf.

For an arbitrary affine group scheme, the counit
`TauCeti.AffineGroupSchemeCat.hopfSpecCoordinateHopfAlgebraIso` transports the comparison
to its coordinate Hopf algebra. Both component formulas are explicit: pass to the Hopf
spectrum through that counit, then use the spectrum-points equivalence. No finite-type
or smoothness hypothesis is needed.

The naturality calculation is `TauCeti.CommHopfAlgCat.mapMulEquiv_mapValue`.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

universe u

namespace CommHopfAlgCat

open TauCeti

variable {R : Type u} [CommRing R]

/-- Convolution points and relative scheme points of a Hopf spectrum agree naturally as groups.
This retains multiplicativity, in addition to the underlying type-valued comparison. -/
noncomputable def pointsFunctorIsoSchemePointsFunctor (H : _root_.CommHopfAlgCat.{u} R) :
    HopfAlgebra.pointsFunctor (R := R) (H := H) ≅
      GroupScheme.algebraPointsFunctor R ((hopfSpec (CommRingCat.of R)).obj (op H)) :=
  NatIso.ofComponents (fun _ ↦ Spec.mapMulEquiv.toGrpIso) (by
    intro A B f
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro p
    exact TauCeti.CommHopfAlgCat.mapMulEquiv_mapValue H f p)

/-- The forward comparison is Mathlib's spectrum-points equivalence. -/
theorem pointsFunctorIsoSchemePointsFunctor_hom_app_apply
    (H : _root_.CommHopfAlgCat.{u} R) (A : CommAlgCat.{u} R)
    (p : WithConv (H →ₐ[R] A)) :
    (pointsFunctorIsoSchemePointsFunctor H).hom.app A p = Spec.mapMulEquiv p :=
  (rfl)

/-- The inverse comparison recovers the convolution point of a relative spectrum morphism. -/
theorem pointsFunctorIsoSchemePointsFunctor_inv_app_apply
    (H : _root_.CommHopfAlgCat.{u} R) (A : CommAlgCat.{u} R)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶
      ((hopfSpec (CommRingCat.of R)).obj (op H)).X) :
    (pointsFunctorIsoSchemePointsFunctor H).inv.app A p = Spec.mapMulEquiv.symm p :=
  (rfl)

end CommHopfAlgCat

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
    (_root_.CommHopfAlgCat.pointsFunctorIsoSchemePointsFunctor _).symm

/-- To read a scheme point as a coordinate point, first pass to the Hopf spectrum using the
inverse counit of the affine anti-equivalence. -/
theorem algebraPointsFunctorIsoCoordinatePointsFunctor_hom_app_apply
    (R : Type u) [CommRing R] (G : AffineGroupSchemeCat (CommRingCat.of R))
    (A : CommAlgCat.{u} R)
    (p : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of R)) ⟶ G.obj.X) :
    (algebraPointsFunctorIsoCoordinatePointsFunctor R G).hom.app A p =
      Spec.mapMulEquiv.symm (p ≫ (hopfSpecCoordinateHopfAlgebraIso R G).inv.hom.hom) :=
  (rfl)

/-- A coordinate point defines a scheme point through the counit of the affine
anti-equivalence. -/
theorem algebraPointsFunctorIsoCoordinatePointsFunctor_inv_app_apply
    (R : Type u) [CommRing R] (G : AffineGroupSchemeCat (CommRingCat.of R))
    (A : CommAlgCat.{u} R)
    (p : WithConv (((commHopfAlgCatOpEquivAffineGroupSchemeCat
      (CommRingCat.of R)).inverse.obj G).unop →ₐ[R] A)) :
    (algebraPointsFunctorIsoCoordinatePointsFunctor R G).inv.app A p =
      Spec.mapMulEquiv p ≫ (hopfSpecCoordinateHopfAlgebraIso R G).hom.hom.hom :=
  (rfl)

end TauCeti.AffineGroupSchemeCat
