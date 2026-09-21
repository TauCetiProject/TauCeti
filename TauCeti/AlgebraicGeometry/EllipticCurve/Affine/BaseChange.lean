/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!
# Base change of affine elliptic curves

Mathlib carries ellipticity through `WeierstrassCurve.map`. This module exposes the same instance
for the canonical affine base-change spelling `W⁄A`, so consumers of the point and function-field
base-change APIs do not have to unfold that abbreviation. It also records that base change along
the identity algebra map returns the original curve.

This is infrastructure for the base-change lane of
`TauCetiRoadmap/EllipticCurves/README.md`, Layer 0.5.
-/

public section

open Polynomial

open _root_.WeierstrassCurve

section

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] (W : Affine R)

/-- Base changing along the identity algebra map returns the curve itself. Stated over a
commutative ring: it is a formal `map` identity and uses nothing about `R` beyond its ring
structure. -/
@[simp]
lemma baseChange_self : (W⁄R).toAffine = W := by
  -- `WeierstrassCurve.baseChange` (Weierstrass.lean:236) is a plain `def` and Mathlib exposes no
  -- unfolding lemma for it, so this one definitional step cannot be replaced by an API rewrite.
  -- It must be `change` rather than `show`: the step rewrites the goal rather than restating it,
  -- which is exactly what `linter.style.show` requires. Everything after it is a named rewrite.
  change W.map (algebraMap R R) = W
  rw [show algebraMap R R = RingHom.id R from Algebra.algebraMap_self]
  exact W.map_id

end WeierstrassCurve.Affine

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {W : _root_.WeierstrassCurve.Affine R} [W.IsElliptic]

/-- **Base change preserves ellipticity**, in the `(W⁄A).toAffine` spelling used by the affine
point API. -/
instance _root_.WeierstrassCurve.Affine.instIsEllipticBaseChange : (W⁄A).toAffine.IsElliptic :=
  inferInstanceAs (W.map (algebraMap R A)).IsElliptic

end


end
