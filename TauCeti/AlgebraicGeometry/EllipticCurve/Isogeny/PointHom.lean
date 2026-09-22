/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.ToClass
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PushClass

/-!
# A class-group map on points associated to an isogeny

An isogeny `φ : W₁ → W₂` is a map of function fields, backwards, and carries no map of points with
it. The ideal class groups nevertheless define a map on points: `Isogeny.pushClass` extends an
ideal of `W₁.CoordinateRing` into the intermediate ring and norms it down to
`W₂.CoordinateRing`, and `Point.toClassEquiv` identifies the points of a Weierstrass curve with
the classes of its coordinate ring. Conjugating the first by the second gives

`Isogeny.toPointHom : W₁.Point →+ W₂.Point`,

a homomorphism **by construction**, since the class-group map and the point–class dictionary are
additive.

The normality hypothesis `IsIntegrallyClosed W₂.CoordinateRing` is the one `pushClass` already
asks of the target; for an elliptic curve it is supplied by
`WeierstrassCurve.Affine.isIntegrallyClosed_coordinateRing`. Nothing here needs `W₁` or `W₂` to be
elliptic.

What is *not* proved here is the geometric reading: that the image of a point is the point lying
under it, in the sense that its place restricts along `φ` to the place of the image. That
comparison, and functoriality in `φ` beyond the identity, are separate statements.

## Main definitions

* `TauCeti.Isogeny.toPointHom`: the class-group-defined additive map on points.

## Main results

* `TauCeti.Isogeny.toClass_toPointHom`: the defining computation — the class of the image point is
  the pushed-forward class.
* `TauCeti.Isogeny.toPointHom_eq_iff`: a point is the image of `P` exactly when its class is the
  pushed-forward class of `P`, the point–class dictionary being injective.
* `TauCeti.Isogeny.toPointHom_id`: the map on points induced by the identity isogeny is the
  identity.

## Provenance

⚠ *mathlib-track*, as for `Isogeny.pushClass` below it: the construction — conjugate the
class-group map induced by extension and relative norm by the point--class dictionary — is
adapted from D. Angdinata's shared isogeny development, `Isogeny.lean`, by David Kurniadi
Angdinata, declaration `toPointHom`, restated in the coordinate-ring form this repository gives
`pushClass`. The identity law is proved here, from `Isogeny.pushClass_id`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.3 (the pushforward of
  divisors along a map of curves, dual to the pullback and computed by the norm) and III.3.4-3.5
  (the identification of the points of an elliptic curve with a divisor class group).
-/

public section

namespace TauCeti

namespace Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve.Affine F}
  (φ : Isogeny W₁ W₂) [IsIntegrallyClosed W₂.CoordinateRing]

/-- **The class-group-defined map on points associated to an isogeny**: the map
`Isogeny.pushClass`, read
through the identification `WeierstrassCurve.Affine.Point.toClassEquiv` of the points of a
Weierstrass curve with the ideal classes of its coordinate ring. -/
noncomputable def toPointHom : W₁.Point →+ W₂.Point :=
  ((Point.toClassEquiv (W := W₂)).symm.toAddMonoidHom.comp φ.pushClass).comp
    (Point.toClassEquiv (W := W₁)).toAddMonoidHom

/-- The class-group-defined map sends `P` to the point corresponding to its pushed-forward class.

**Deliberately not `@[simp]`**: it would put `toPointHom` into a `Point.toClassEquiv.symm` normal
form that no further lemma consumes, and block the characteristic rule `toClass_toPointHom`
below. -/
theorem toPointHom_apply (P : W₁.Point) :
    φ.toPointHom P = Point.toClassEquiv.symm (φ.pushClass P.toClass) := by
  -- `toClassEquiv` is not exposed, so its application is rewritten rather than unfolded; what is
  -- left is this file's own definition, applied
  rw [← Point.toClassEquiv_apply]
  rfl

/-- **The class of the image point is the pushed-forward class.** This characterises `toPointHom`,
since `WeierstrassCurve.Affine.Point.toClass` is injective.

This is deliberately not a simp lemma: `Point.toClass_apply` simplifies its left-hand side to a
match on the image point, which is a worse public-facing normal form than this characteristic
equation. -/
theorem toClass_toPointHom (P : W₁.Point) :
    (φ.toPointHom P).toClass = φ.pushClass P.toClass := by
  rw [toPointHom_apply, ← Point.toClassEquiv_apply, AddEquiv.apply_symm_apply]

/-- **A point is the image of `P` exactly when its class is the pushed-forward class of `P`.** -/
theorem toPointHom_eq_iff {P : W₁.Point} {Q : W₂.Point} :
    φ.toPointHom P = Q ↔ φ.pushClass P.toClass = Q.toClass := by
  rw [← toClass_toPointHom]
  exact Point.toClass_injective.eq_iff.symm

/-- **The map on points induced by the identity isogeny is the identity.** -/
@[simp]
theorem toPointHom_id (W : WeierstrassCurve.Affine F) [IsIntegrallyClosed W.CoordinateRing] :
    (Isogeny.id W).toPointHom = AddMonoidHom.id W.Point := by
  refine AddMonoidHom.ext fun P ↦ ?_
  rw [toPointHom_apply, pushClass_id, AddMonoidHom.id_apply, ← Point.toClassEquiv_apply,
    AddEquiv.symm_apply_apply, AddMonoidHom.id_apply]

end Isogeny

end TauCeti

end
