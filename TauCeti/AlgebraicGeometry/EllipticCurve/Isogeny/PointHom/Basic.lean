/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.ToClass
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PushClass
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IntermediateRing.PointIdeal
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.InfinityPlace.Basic
-- Proof-only: the pole of `x₂` at the place at infinity of the target.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.InfinityPlace.Unique

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

The geometric reading is that the image of a point is the point lying under it, in the sense that
its place restricts along `φ` to the place of the image. Its first half is proved here: a point of
`W₁` whose place lies over the point at infinity of `W₂` — a point of the fibre `φ⁻¹(O₂)` — is sent
to `0`, because its ideal extends to the unit ideal of the intermediate ring
(`TauCeti.Isogeny.map_XYIdeal_eq_top_of_one_lt_valuation`). The affine half needs the relative norm
of the prime of the intermediate ring at such a point; it is computed in `PointHom/Affine.lean`
(`TauCeti.Isogeny.toPointHom_some_eq_some_of_isEquiv_comap_pointPlace`), for a separable isogeny
over a separably closed field. Functoriality in `φ` beyond the identity is not proved here.

## Main definitions

* `TauCeti.Isogeny.toPointHom`: the class-group-defined additive map on points.

## Main results

* `TauCeti.Isogeny.toClass_toPointHom`: the defining computation — the class of the image point is
  the pushed-forward class.
* `TauCeti.Isogeny.toPointHom_eq_iff`: a point is the image of `P` exactly when its class is the
  pushed-forward class of `P`, the point–class dictionary being injective.
* `TauCeti.Isogeny.toPointHom_id`: the map on points induced by the identity isogeny is the
  identity.
* `TauCeti.Isogeny.toPointHom_some_eq_zero_of_isEquiv_comap_infinityPlace`: a point lying over the
  point at infinity of the target is sent to `0`.

## Provenance

The construction — conjugate the class-group map induced by extension and relative norm by the
point--class dictionary — is adapted from D. Angdinata's shared isogeny development,
`Isogeny.lean`, by David Kurniadi Angdinata, declaration `toPointHom`, restated in the
coordinate-ring form this repository gives `pushClass`. The identity law is not in that source;
it is original here.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.3 (the pushforward of
  divisors along a map of curves, dual to the pullback and computed by the norm) and III.3.4-3.5
  (the identification of the points of an elliptic curve with a divisor class group).
-/

public section

open Polynomial WeierstrassCurve.Affine
open scoped nonZeroDivisors

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve.Affine F}
  (φ : Isogeny W₁ W₂) [IsIntegrallyClosed W₂.CoordinateRing]

/-- **The class-group-defined map on points associated to an isogeny**: the map
`Isogeny.pushClass`, read
through the identification `WeierstrassCurve.Affine.Point.toClassEquiv` of the points of a
Weierstrass curve with the ideal classes of its coordinate ring. -/
noncomputable def toPointHom : W₁.Point →+ W₂.Point :=
  ((Point.toClassEquiv (W := W₂)).symm.toAddMonoidHom.comp φ.pushClass).comp
    (Point.toClassEquiv (W := W₁)).toAddMonoidHom

/-- The class-group-defined map sends `P` to the point corresponding to its pushed-forward
class. -/
-- Deliberately not `@[simp]`: it would put `toPointHom` into a `Point.toClassEquiv.symm` normal
-- form that no further lemma consumes, and block the characteristic rule `toClass_toPointHom`
-- below.
theorem toPointHom_apply (P : W₁.Point) :
    φ.toPointHom P = Point.toClassEquiv.symm (φ.pushClass P.toClass) := by
  -- `toClassEquiv` is not exposed, so its application is rewritten rather than unfolded; what is
  -- left is this file's own definition, applied
  rw [← Point.toClassEquiv_apply]
  rfl

/-- **The class of the image point is the pushed-forward class.** This characterises `toPointHom`,
since `WeierstrassCurve.Affine.Point.toClass` is injective. -/
-- Deliberately not `@[simp]`: Mathlib's `@[simps]` on `Point.toClass` already publishes
-- `Point.toClass_apply`, a simp lemma rewriting `Point.toClass Q` to a match on `Q` for *every*
-- `Q`. So this statement's left-hand side is not in simp normal form, and tagging it `@[simp]`
-- is a `simpNF` linter violation, not merely a matter of taste. The characteristic equation is
-- the useful public form, so it is kept as a named rewrite.
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

local instance [IsIntegrallyClosed W₁.CoordinateRing] : IsDedekindDomain W₁.CoordinateRing :=
  W₁.isDedekindDomain_coordinateRing_of_isIntegrallyClosed

/-- **A point over the point at infinity is sent to `0`.** If the place of the affine point
`(x, y)` of `W₁` restricts along `φ` to the place at infinity of `W₂` — the point lies in the fibre
`φ⁻¹(O₂)` — then `φ.toPointHom` sends it to the point at infinity. -/
@[simp]
theorem toPointHom_some_eq_zero_of_isEquiv_comap_infinityPlace
    [IsIntegrallyClosed W₁.CoordinateRing] {x y : F} (h : W₁.Nonsingular x y)
    (hP : (((CoordinateRing.pointPlace h.1).valuation W₁.FunctionField).comap
      (φ.fieldPullback : W₂.FunctionField →+* W₁.FunctionField)).IsEquiv W₂.infinityPlace) :
    φ.toPointHom (.some x y h) = 0 := by
  -- the pulled-back coordinate `φ^* x₂` has a pole at the point, as `x₂` has one at infinity
  have hpole : 1 < (CoordinateRing.pointPlace h.1).valuation W₁.FunctionField
      (φ.pullback (algebraMap F[X] W₂.CoordinateRing X)) := by
    have hx := one_lt_infinityPlace_X W₂
    rw [← not_le, ← Valuation.isEquiv_iff_val_le_one.mp hP, not_le, Valuation.comap_apply,
      IsScalarTower.algebraMap_apply F[X] W₂.CoordinateRing W₂.FunctionField] at hx
    rw [← AlgHom.toRingHom_eq_coe] at hx
    rwa [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, fieldPullback_algebraMap] at hx
  -- the class of the point is that of its ideal, which extends to the unit ideal
  rw [toPointHom_eq_iff, Point.toClass_zero, Point.toClass_some_eq_ofMul_mk0 h, pushClass_apply,
    toMul_ofMul, pushClassMonoidHom_mk0_eq_one_of_map_eq_top φ
      ⟨_, mem_nonZeroDivisors_of_ne_zero (CoordinateRing.XYIdeal_ne_bot x (C y))⟩
      (φ.map_XYIdeal_eq_top_of_one_lt_valuation h.1 hpole), ofMul_one]

end Isogeny

end TauCeti

end
