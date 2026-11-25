/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-!
# Integral morphisms are local on the target, for instance search

Mathlib proves that integral morphisms of schemes are local on the target through the instance
`IsIntegralHom.hasAffineProperty`, whose affine property
`fun X _ f _ ↦ IsAffine X ∧ RingHom.IsIntegral (f.app ⊤).hom` is stored as a lambda whose type is a
dependent function type, not `AffineTargetMorphismProperty`. Instance search cannot assign it to
the out-parameter of `HasAffineProperty`, so `IsZariskiLocalAtTarget @IsIntegralHom` and
`HasAffineProperty @IsIntegralHom _` fail to synthesize.

This file restates the affine property as a constant of type `AffineTargetMorphismProperty`
(`AlgebraicGeometry.affineAndIsIntegralAffineTarget`) and registers the instances through it, so
instance search finds them. The same is done for affine morphisms in
`TauCeti.AlgebraicGeometry.Morphisms.Affine.TargetLocal`.

## Main results

* `AlgebraicGeometry.hasAffineProperty_isIntegralHom`: the `HasAffineProperty` instance.
* `AlgebraicGeometry.isZariskiLocalAtTarget_isIntegralHom`: being integral is local on the
  target.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- The affine target property of integral morphisms: the source is affine and the map of global
sections is integral. -/
abbrev affineAndIsIntegralAffineTarget : AffineTargetMorphismProperty.{u} :=
  fun X _ f _ ↦ IsAffine X ∧ RingHom.IsIntegral (f.app ⊤).hom

/-- A morphism to an affine scheme is integral exactly when its source is affine and its map of
global sections is integral, as an instance that instance search can use. -/
instance hasAffineProperty_isIntegralHom :
    HasAffineProperty @IsIntegralHom.{u} affineAndIsIntegralAffineTarget :=
  IsIntegralHom.hasAffineProperty

/-- **Being integral is local on the target.** -/
instance isZariskiLocalAtTarget_isIntegralHom : IsZariskiLocalAtTarget @IsIntegralHom.{u} :=
  HasAffineProperty.instIsZariskiLocalAtTarget (Q := affineAndIsIntegralAffineTarget)

end AlgebraicGeometry
