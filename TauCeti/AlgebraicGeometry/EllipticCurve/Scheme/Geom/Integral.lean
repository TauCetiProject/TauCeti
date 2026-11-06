/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Geometrically.Integral
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Integral

/-!
# Geometric integrality of elliptic curves over a scheme

Let `E` be an elliptic curve over a scheme `S` (`TauCeti.AlgebraicGeometry.EllipticCurveGeom S`).
This file shows that its structure morphism `E.structureMap : E.carrier ⟶ S` is geometrically
integral (`TauCeti.AlgebraicGeometry.EllipticCurveGeom.geometricallyIntegral_structureMap`).

Over an affine open neighbourhood `U` of any point of `S`, `E` is isomorphic over `U ≅ Spec Γ(S, U)`
to the projective Weierstrass model `W.projModel` of an elliptic Weierstrass curve `W` over
`Γ(S, U)`, whose structure morphism is geometrically integral by
`WeierstrassCurve.geometricallyIntegral_projModelOver`. Since `GeometricallyIntegral` is
Zariski-local on the target, geometric integrality passes to `E.structureMap` globally. Over a
field `K`, it follows that `E.carrier` is an integral scheme.

## Main results

* `TauCeti.AlgebraicGeometry.PointedWeierstrassChart.geometricallyIntegral_toBase`: the structure
  morphism of a pointed Weierstrass chart is geometrically integral.
* `TauCeti.AlgebraicGeometry.IsLocallyWeierstrass.geometricallyIntegral`: any morphism satisfying
  the local Weierstrass model condition is geometrically integral.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.geometricallyIntegral_structureMap`: the structure
  morphism of an elliptic curve over a scheme is geometrically integral.
* `TauCeti.AlgebraicGeometry.EllipticCurveGeom.isIntegral_carrier`: an elliptic curve over `Spec K`
  for a field `K` has an integral underlying scheme.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.1.
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, II.1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

namespace PointedWeierstrassChart

variable {S X : Scheme.{u}} {π : X ⟶ S} {zero : S ⟶ X}

/-- On a pointed Weierstrass chart `c`, the structure morphism
`c.toBase : c.pullbackCarrier ⟶ c.base` is geometrically integral. -/
instance geometricallyIntegral_toBase (c : PointedWeierstrassChart π zero) :
    GeometricallyIntegral c.toBase := by
  have h : c.toBase = c.modelIso.hom ≫ c.equation.projModelOver ≫ c.baseIso.inv := by
    rw [← Category.assoc, c.modelIso_over, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h, MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral,
    MorphismProperty.cancel_right_of_respectsIso @GeometricallyIntegral]
  infer_instance

end PointedWeierstrassChart

/-- **Morphisms locally modelled on Weierstrass curves are geometrically integral.** -/
theorem IsLocallyWeierstrass.geometricallyIntegral {X S : Scheme.{u}} {π : X ⟶ S} {zero : S ⟶ X}
    {hzero : zero ≫ π = 𝟙 S} (h : IsLocallyWeierstrass π zero hzero) :
    GeometricallyIntegral π := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun s ↦ ?_
  obtain ⟨U, hsU, W, -, e, hover, -⟩ := (isLocallyWeierstrass_iff hzero).mp h s
  refine ⟨U.1, hsU, ?_⟩
  have hres : π ∣_ U.1 =
      ((isPullback_morphismRestrict π U.1).flip.isoPullback.hom ≫ e.hom) ≫
        W.projModelOver ≫ U.2.isoSpec.inv := by
    rw [Category.assoc, ← Category.assoc e.hom, hover, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, IsPullback.isoPullback_hom_snd]
  rw [hres, MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral,
    MorphismProperty.cancel_right_of_respectsIso @GeometricallyIntegral]
  infer_instance

namespace EllipticCurveGeom

variable {S : Scheme.{u}} (E : EllipticCurveGeom S)

/-- **The structure morphism of an elliptic curve over a scheme is geometrically integral.** -/
instance geometricallyIntegral_structureMap : GeometricallyIntegral E.structureMap :=
  E.isLocallyWeierstrass.geometricallyIntegral

/-- **An elliptic curve over a field is an integral scheme.** -/
instance isIntegral_carrier {K : Type u} [Field K] (E : EllipticCurveGeom (Spec (.of K))) :
    AlgebraicGeometry.IsIntegral E.carrier :=
  GeometricallyIntegral.isIntegral_of_subsingleton E.structureMap

end EllipticCurveGeom

end TauCeti.AlgebraicGeometry
