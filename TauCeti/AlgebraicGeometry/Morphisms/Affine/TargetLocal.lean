/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Affine morphisms are local on the target, for instance search

Mathlib proves that affine morphisms of schemes are local on the target through the instance
`HasAffineProperty @IsAffineHom (fun X _ _ _ ↦ IsAffine X)`. Instance search cannot use it: the
affine property is stored as a lambda whose type is a dependent function type, not
`AffineTargetMorphismProperty`, so it cannot be assigned to the out-parameter of
`HasAffineProperty`. Hence `IsZariskiLocalAtTarget @IsAffineHom` and
`HasAffineProperty @IsAffineHom _` fail to synthesize.

This file restates the affine property as a constant of type `AffineTargetMorphismProperty`
(`AlgebraicGeometry.isAffineAffineTarget`) and registers the instances through it, so instance
search finds them. The same is done for quasi-compact and quasi-separated morphisms in
`TauCeti.AlgebraicGeometry.Morphisms.QuasiCompact`.

## Main results

* `AlgebraicGeometry.hasAffineProperty_isAffineHom`: the `HasAffineProperty` instance.
* `AlgebraicGeometry.isZariskiLocalAtTarget_isAffineHom`: being affine is local on the target.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- The affine target property of affine morphisms: the source is affine. -/
abbrev isAffineAffineTarget : AffineTargetMorphismProperty.{u} :=
  fun X _ _ _ ↦ IsAffine X

/-- A morphism to an affine scheme is affine exactly when its source is, as an instance that
instance search can use. -/
instance hasAffineProperty_isAffineHom :
    HasAffineProperty @IsAffineHom.{u} isAffineAffineTarget :=
  instHasAffinePropertyIsAffineHomIsAffine

/-- **Being affine is local on the target.** -/
instance isZariskiLocalAtTarget_isAffineHom : IsZariskiLocalAtTarget @IsAffineHom.{u} :=
  HasAffineProperty.instIsZariskiLocalAtTarget (Q := isAffineAffineTarget)

end AlgebraicGeometry
