/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.PointPlace
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.InfinityPlace.Basic

/-!
# Restriction of the normalized place at infinity along an isogeny

An isogeny `φ : W₁ → W₂` of affine Weierstrass curves over a field `F` embeds `F(W₂)` in `F(W₁)`
as a finite field extension (`TauCeti.Isogeny.finiteDimensional_functionField`) along which the
unnormalized valuation at infinity restricts to that of `W₂`
(`TauCeti.Isogeny.isEquiv_comap_infinityPlace`). This module states that restriction in the
normalized `TauCeti.Place` API without importing divisor theory or polluting the valuation-only
`Isogeny/InfinityPlace/Basic.lean` with `Isogeny.Degree` and `PointPlace`.

## Main results

* `TauCeti.Isogeny.restrict_infinity`: the normalized place at infinity of `W₁` restricts to the
  normalized place at infinity of `W₂` along any isogeny.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2, III.4.
-/

public section

namespace TauCeti.Isogeny

open _root_.WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F} (φ : Isogeny W₁ W₂)
  [Algebra W₂.FunctionField W₁.FunctionField]
  (h : ∀ z, algebraMap W₂.FunctionField W₁.FunctionField z = φ.fieldPullback z)

/-- **The place at infinity restricts to the place at infinity** along any isogeny, in the
normalized `TauCeti.Place` API. -/
theorem restrict_infinity :
    haveI := isScalarTower_of_algebraMap_eq_fieldPullback φ h
    haveI := φ.finiteDimensional_functionField h
    (Place.infinity W₁).restrict F W₂.FunctionField = Place.infinity W₂ := by
  have := isScalarTower_of_algebraMap_eq_fieldPullback φ h
  have := φ.finiteDimensional_functionField h
  rw [Place.restrict_eq_iff_isEquiv_comap, Place.valuation_infinity, Place.valuation_infinity]
  have hcomap : algebraMap W₂.FunctionField W₁.FunctionField = φ.fieldPullback.toRingHom :=
    RingHom.ext h
  rw [hcomap]
  exact φ.isEquiv_comap_infinityPlace

end TauCeti.Isogeny

end
