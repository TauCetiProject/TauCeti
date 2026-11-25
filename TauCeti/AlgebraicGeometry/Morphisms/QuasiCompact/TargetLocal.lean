/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Quasi-compactness and quasi-separatedness are local on the target, for instance search

Mathlib proves that quasi-compact and quasi-separated morphisms of schemes are local on the target
through instances `HasAffineProperty @QuasiCompact (fun X _ _ _ ↦ CompactSpace X)` and
`HasAffineProperty @QuasiSeparated (fun X _ _ _ ↦ QuasiSeparatedSpace X)`. Instance search cannot
use them: the affine property is stored as a lambda whose type is a dependent function type, not
`AffineTargetMorphismProperty`, so it cannot be assigned to the out-parameter of
`HasAffineProperty`. Hence `IsZariskiLocalAtTarget @QuasiCompact`,
`IsZariskiLocalAtTarget @QuasiSeparated` and `HasAffineProperty @QuasiCompact _` fail to
synthesize, and with them lemmas such as `IsZariskiLocalAtTarget.of_openCover` and
`HasAffineProperty.of_iSup_eq_top` for these properties.

This file restates the two affine properties as constants of type `AffineTargetMorphismProperty`
(`AlgebraicGeometry.compactSpaceAffineTarget`, `AlgebraicGeometry.quasiSeparatedSpaceAffineTarget`)
and registers the instances through them, so instance search finds them.

## Main results

* `AlgebraicGeometry.hasAffineProperty_quasiCompact`,
  `AlgebraicGeometry.hasAffineProperty_quasiSeparated`: the `HasAffineProperty` instances.
* `AlgebraicGeometry.isZariskiLocalAtTarget_quasiCompact`,
  `AlgebraicGeometry.isZariskiLocalAtTarget_quasiSeparated`: quasi-compactness and
  quasi-separatedness are local on the target.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- The affine target property of quasi-compact morphisms: the source is quasi-compact. -/
abbrev compactSpaceAffineTarget : AffineTargetMorphismProperty.{u} :=
  fun X _ _ _ ↦ CompactSpace X

/-- The affine target property of quasi-separated morphisms: the source is quasi-separated. -/
abbrev quasiSeparatedSpaceAffineTarget : AffineTargetMorphismProperty.{u} :=
  fun X _ _ _ ↦ QuasiSeparatedSpace X

/-- A morphism to an affine scheme is quasi-compact exactly when its source is, as an instance
that instance search can use. -/
instance hasAffineProperty_quasiCompact :
    HasAffineProperty @QuasiCompact.{u} compactSpaceAffineTarget :=
  instHasAffinePropertyQuasiCompactCompactSpaceCarrierCarrierCommRingCat

/-- A morphism to an affine scheme is quasi-separated exactly when its source is, as an instance
that instance search can use. -/
instance hasAffineProperty_quasiSeparated :
    HasAffineProperty @QuasiSeparated.{u} quasiSeparatedSpaceAffineTarget :=
  instHasAffinePropertyQuasiSeparatedQuasiSeparatedSpaceCarrierCarrierCommRingCat

/-- **Quasi-compactness is local on the target.** -/
instance isZariskiLocalAtTarget_quasiCompact : IsZariskiLocalAtTarget @QuasiCompact.{u} :=
  HasAffineProperty.instIsZariskiLocalAtTarget (Q := compactSpaceAffineTarget)

/-- **Quasi-separatedness is local on the target.** -/
instance isZariskiLocalAtTarget_quasiSeparated : IsZariskiLocalAtTarget @QuasiSeparated.{u} :=
  HasAffineProperty.instIsZariskiLocalAtTarget (Q := quasiSeparatedSpaceAffineTarget)

end AlgebraicGeometry
