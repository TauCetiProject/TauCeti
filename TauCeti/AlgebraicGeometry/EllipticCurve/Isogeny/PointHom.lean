/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.ToClass
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PushClass

/-!
# The map on points induced by an isogeny

An isogeny `φ : W₁ → W₂` is a map of function fields, backwards, and carries no map of points with
it. It does induce one, through the ideal class groups: `Isogeny.pushClass` extends an ideal of
`W₁.CoordinateRing` into the intermediate ring and norms it down to `W₂.CoordinateRing`, and
`Point.toClassEquiv` identifies the points of a Weierstrass curve with the classes of its
coordinate ring. Conjugating the first by the second gives

`Isogeny.toPointHom : W₁.Point →+ W₂.Point`,

the map `φ` induces on rational points. It is a homomorphism **by construction** — the class-group
map is one and the point–class dictionary is additive — so the classical statement that a pointed
morphism of elliptic curves respects the group law needs no separate rigidity argument here.

The normality hypothesis `IsIntegrallyClosed W₂.CoordinateRing` is the one `pushClass` already
asks of the target; for an elliptic curve it is supplied by
`WeierstrassCurve.Affine.isIntegrallyClosed_coordinateRing`. Nothing here needs `W₁` or `W₂` to be
elliptic.

What is *not* proved here is the geometric reading: that the image of a point is the point lying
under it, in the sense that its place restricts along `φ` to the place of the image. That
comparison, and functoriality in `φ` beyond the identity, are separate statements.

## Main definitions

* `TauCeti.Isogeny.toPointHom`: the induced additive map on points.

## Main results

* `TauCeti.Isogeny.toClass_toPointHom`: the defining computation — the class of the image point is
  the pushed-forward class.
* `TauCeti.Isogeny.toPointHom_eq_iff`: a point is the image of `P` exactly when its class is the
  pushed-forward class of `P`, the point–class dictionary being injective.
* `TauCeti.Isogeny.toPointHom_eq_zero_iff`: the kernel of the induced map, in class-group terms.
* `TauCeti.Isogeny.toPointHom_id`: the identity isogeny induces the identity on points.

## Provenance

⚠ *mathlib-track*, as for `Isogeny.pushClass` below it: the construction — conjugate the
class-group map induced by extension and relative norm by the point--class dictionary — is
D. Angdinata's shared isogeny development's `toPointHom`, built here until its PRs land. The
identity law is proved here, from `Isogeny.pushClass_id`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2 and III.4.8.
-/

public section

namespace TauCeti

namespace Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve.Affine F}
  (φ : Isogeny W₁ W₂) [IsIntegrallyClosed W₂.CoordinateRing]

/-- **The map on points induced by an isogeny**: the class-group map `Isogeny.pushClass`, read
through the identification `WeierstrassCurve.Affine.Point.toClassEquiv` of the points of a
Weierstrass curve with the ideal classes of its coordinate ring.

Additive by construction, so Silverman III.4.8 — a morphism of elliptic curves taking `O` to `O`
is a homomorphism — is built in rather than proved separately. -/
noncomputable def toPointHom : W₁.Point →+ W₂.Point :=
  ((Point.toClassEquiv (W := W₂)).symm.toAddMonoidHom.comp φ.pushClass).comp
    (Point.toClassEquiv (W := W₁)).toAddMonoidHom

/-- The induced map, unfolded: push the class of `P` forward and read the result as a point. The
definition's body is not exposed across the module boundary, so this is how a downstream module
computes with it; `toClass_toPointHom` is the form that avoids the inverse equivalence. -/
theorem toPointHom_apply (P : W₁.Point) :
    φ.toPointHom P = Point.toClassEquiv.symm (φ.pushClass P.toClass) := by
  -- `toClassEquiv` is not exposed, so its application is rewritten rather than unfolded; what is
  -- left is this file's own definition, applied
  rw [← Point.toClassEquiv_apply]
  rfl

/-- **The class of the image point is the pushed-forward class.** This characterises `toPointHom`,
since `WeierstrassCurve.Affine.Point.toClass` is injective.

Not `@[simp]`: `WeierstrassCurve.Affine.Point.toClass_apply` is, and it splits the left-hand side
into the two cases of a point, so this lemma is not in simp-normal form. -/
theorem toClass_toPointHom (P : W₁.Point) :
    (φ.toPointHom P).toClass = φ.pushClass P.toClass := by
  rw [toPointHom_apply, ← Point.toClassEquiv_apply, AddEquiv.apply_symm_apply]

/-- **A point is the image of `P` exactly when its class is the pushed-forward class of `P`.** -/
theorem toPointHom_eq_iff {P : W₁.Point} {Q : W₂.Point} :
    φ.toPointHom P = Q ↔ φ.pushClass P.toClass = Q.toClass := by
  rw [← toClass_toPointHom]
  exact Point.toClass_injective.eq_iff.symm

/-- **A point lands at infinity exactly when its class dies in the target.** This is the kernel of
the induced map, in class-group terms. -/
theorem toPointHom_eq_zero_iff {P : W₁.Point} :
    φ.toPointHom P = 0 ↔ φ.pushClass P.toClass = 0 := by
  rw [toPointHom_eq_iff, map_zero]

/-- **The identity isogeny induces the identity on points.** -/
@[simp]
theorem toPointHom_id (W : WeierstrassCurve.Affine F) [IsIntegrallyClosed W.CoordinateRing] :
    (Isogeny.id W).toPointHom = AddMonoidHom.id W.Point := by
  refine AddMonoidHom.ext fun P ↦ ?_
  rw [toPointHom_apply, pushClass_id, AddMonoidHom.id_apply, ← Point.toClassEquiv_apply,
    AddEquiv.symm_apply_apply, AddMonoidHom.id_apply]

end Isogeny

end TauCeti

end
