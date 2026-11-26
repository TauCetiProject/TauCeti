/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Tactic.Observe

/-!
# Finite morphisms are local on the target, for instance search

Mathlib proves that finite morphisms of schemes are local on the target through an instance
`HasAffineProperty @IsFinite (fun X _ f _ ↦ IsAffine X ∧ RingHom.Finite (f.appTop).hom)`.
Instance search cannot use it: the affine property is stored as a lambda whose type is a
dependent function type, not `AffineTargetMorphismProperty`, so it cannot be assigned to the
out-parameter of `HasAffineProperty`. Hence `IsZariskiLocalAtTarget @IsFinite` and
`HasAffineProperty @IsFinite _` fail to synthesize.

This file restates the instance with the affine property written as Mathlib's constant
`affineAnd RingHom.Finite`, of type `AffineTargetMorphismProperty`, so instance search finds it.
The same is done for affine morphisms in `TauCeti.AlgebraicGeometry.Morphisms.Affine.TargetLocal`
and for integral morphisms in `TauCeti.AlgebraicGeometry.Morphisms.Integral.TargetLocal`.

## Main results

* `AlgebraicGeometry.hasAffineProperty_isFinite`: the `HasAffineProperty` instance.
* `AlgebraicGeometry.isZariskiLocalAtTarget_isFinite`: being finite is local on the target.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- A morphism to an affine scheme is finite exactly when its source is affine and its map of
global sections is finite, as an instance that instance search can use. -/
instance hasAffineProperty_isFinite :
    HasAffineProperty @IsFinite.{u} (affineAnd RingHom.Finite) := by
  -- Mathlib's instance has an automatically generated name too long to write within the line
  -- length limit, so it is retrieved by `observe`.
  observe h : HasAffineProperty @IsFinite.{u}
    fun X _ f _ ↦ IsAffine X ∧ RingHom.Finite (f.appTop).hom
  exact h

/-- **Being finite is local on the target.** -/
instance isZariskiLocalAtTarget_isFinite : IsZariskiLocalAtTarget @IsFinite.{u} :=
  HasAffineProperty.instIsZariskiLocalAtTarget (Q := affineAnd RingHom.Finite)

end AlgebraicGeometry
