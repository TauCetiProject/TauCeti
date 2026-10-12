/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ProjModel
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Prime
import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.BaseChange
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Integral

/-!
# Integrality of the projective Weierstrass model

For a Weierstrass curve `W` over an integral domain `R`, the projective Weierstrass model
`W.projModel` is an integral scheme. No ellipticity hypothesis is needed; in particular the
projective model of an elliptic curve over a field is integral.

Over an arbitrary commutative ring `R`, the structure morphism `W.projModelOver` is therefore
geometrically integral: its base change along `Spec K ⟶ Spec R`, for a field `K`, is the
projective model of `W` over `K`.

## Main results

* `WeierstrassCurve.isIntegral_projModel`: over an integral domain, the projective Weierstrass
  model is an integral scheme.
* `WeierstrassCurve.geometricallyIntegral_projModelOver`: over any commutative ring, the structure
  morphism of the projective Weierstrass model is geometrically integral.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1.

## Provenance

Both results draw on AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`; the files named below lie in
`projects/ModularCurves/ModularCurves/EllipticCurve/`.

AINTLIB states integrality of the projective model only over a field
(`ModularCurves.isIntegral_projModel` in `PointsDictionary.lean` and
`ModularCurves.isIntegral_projModel_u` in `GroupLawAxioms.lean`). Over an integral domain,
`isIntegral_projModel` is assembled from the two inputs adapted from AINTLIB,
`WeierstrassCurve.Projective.instIsDomainCoordinateRing` and
`AlgebraicGeometry.Proj.isIntegral_of_isDomain`.

`geometricallyIntegral_projModelOver` is adapted from
`ModularCurves.geometricallyIntegral_universalCurveπ` in `PointsDictionary.lean` and its
universe-polymorphic counterpart `ModularCurves.geometricallyIntegral_universalCurveπU` in
`GroupLawAxioms.lean`, which treat only the universal Weierstrass curve over
`ℤ[a₁, a₂, a₃, a₄, a₆][Δ⁻¹]`. Here the same fibrewise argument applies to every Weierstrass curve
over every commutative ring.
-/

public section

open AlgebraicGeometry

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] (W' : Projective R)

private theorem irrelevant_ne_bot [Nontrivial R] : HomogeneousIdeal.irrelevant W'.grading ≠ ⊥ :=
  -- the irrelevant ideal contains `Y`, which is nonzero since it is `1` at the point `[0 : 1 : 0]`
  mt (HomogeneousIdeal.eq_bot_iff _).mp <| (Submodule.ne_bot_iff _).mpr
    ⟨W'.coord 1, HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos (W'.coord_mem_grading 1),
      ne_zero_of_map (f := W'.evalZero) (by simp)⟩

end WeierstrassCurve.Projective

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Over an integral domain, the projective Weierstrass model is an integral scheme; in particular
the projective model of any Weierstrass curve over a field, elliptic or not, is integral. Here
`IsIntegral` is the scheme property `AlgebraicGeometry.IsIntegral`, not
`WeierstrassCurve.IsIntegral` (integrality of the coefficients over a subring). -/
instance isIntegral_projModel [IsDomain R] : AlgebraicGeometry.IsIntegral W.projModel :=
  Proj.isIntegral_of_isDomain _ W.toProjective.irrelevant_ne_bot

/-- The structure morphism of the projective Weierstrass model over any commutative ring is
geometrically integral: its base change along `Spec K ⟶ Spec R`, for a field `K`, is the projective
Weierstrass model of `W` over `K`, which is an integral scheme. No ellipticity hypothesis is
needed. -/
instance geometricallyIntegral_projModelOver : GeometricallyIntegral W.projModelOver :=
  ⟨geometrically_iff_of_commRing.mpr fun K _ _ _ _ _ h ↦
    .of_isIso ((W.isPullback_projModelBaseChange (algebraMap R K)).isoIsPullback _ _ h).hom⟩

end WeierstrassCurve
