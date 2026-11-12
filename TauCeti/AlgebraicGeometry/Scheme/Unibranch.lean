/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Scheme.Normal
public import TauCeti.RingTheory.LocalRing.Unibranch

/-!
# Geometrically unibranch schemes

A scheme `X` is *geometrically unibranch at a point* `x` if its local ring `𝒪_{X,x}` is a
geometrically unibranch local ring (`IsLocalRing.IsGeometricallyUnibranch`), and *geometrically
unibranch* if this holds at every point. Normal schemes are geometrically unibranch, since their
local rings are integrally closed domains.

## Main definitions

* `AlgebraicGeometry.Scheme.IsGeometricallyUnibranchAt X x`: the local ring of `X` at `x` is
  geometrically unibranch.
* `AlgebraicGeometry.IsGeometricallyUnibranch X`: `X` is geometrically unibranch at every point.

## Main results

* `AlgebraicGeometry.IsGeometricallyUnibranch.of_isNormalScheme`: normal schemes are
  geometrically unibranch.

## References

* [Stacks Project, Definition 15.108.1](https://stacks.math.columbia.edu/tag/0BPZ)
-/

public section

namespace AlgebraicGeometry

universe u

/-- A scheme `X` is **geometrically unibranch at** `x` if its local ring at `x` is a
geometrically unibranch local ring. -/
def Scheme.IsGeometricallyUnibranchAt (X : Scheme.{u}) (x : X) : Prop :=
  IsLocalRing.IsGeometricallyUnibranch (X.presheaf.stalk x)

/-- Unfolding `Scheme.IsGeometricallyUnibranchAt`. -/
theorem Scheme.isGeometricallyUnibranchAt_iff {X : Scheme.{u}} {x : X} :
    X.IsGeometricallyUnibranchAt x ↔
      IsLocalRing.IsGeometricallyUnibranch (X.presheaf.stalk x) :=
  Iff.rfl

/-- A scheme is **geometrically unibranch** if it is geometrically unibranch at every point,
that is, if each of its local rings is a geometrically unibranch local ring. -/
class IsGeometricallyUnibranch (X : Scheme.{u}) : Prop where
  isGeometricallyUnibranchAt : ∀ x : X, X.IsGeometricallyUnibranchAt x

/-- The local rings of a geometrically unibranch scheme are geometrically unibranch. -/
instance IsGeometricallyUnibranch.isGeometricallyUnibranch_stalk (X : Scheme.{u})
    [IsGeometricallyUnibranch X] (x : X) :
    IsLocalRing.IsGeometricallyUnibranch (X.presheaf.stalk x) :=
  IsGeometricallyUnibranch.isGeometricallyUnibranchAt x

/-- A normal scheme is geometrically unibranch: its local rings are integrally closed domains. -/
instance IsGeometricallyUnibranch.of_isNormalScheme (X : Scheme.{u})
    [TauCeti.AlgebraicGeometry.IsNormalScheme X] : IsGeometricallyUnibranch X :=
  ⟨fun _ ↦ Scheme.isGeometricallyUnibranchAt_iff.mpr inferInstance⟩

end AlgebraicGeometry
