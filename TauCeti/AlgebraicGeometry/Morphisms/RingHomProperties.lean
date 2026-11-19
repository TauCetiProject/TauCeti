/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import TauCeti.AlgebraicGeometry.Morphisms.Basic

/-!
# Open-immersion postcomposition stability for `HasRingHomProperty`

This file specializes `AlgebraicGeometry.IsZariskiLocalAtSource.respectsRight_isOpenImmersion` to
raw scheme morphism predicates equipped with `AlgebraicGeometry.HasRingHomProperty` so typeclass
search resolves `MorphismProperty.RespectsRight P @IsOpenImmersion` at `instances` transparency.

## Main results

* `AlgebraicGeometry.HasRingHomProperty.respectsRight_isOpenImmersion`: any multiplicative scheme
  morphism property defined from a ring homomorphism property respects postcomposition with open
  immersions.
-/

public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Any multiplicative scheme morphism property defined from a ring homomorphism property respects
postcomposition with open immersions. -/
instance HasRingHomProperty.respectsRight_isOpenImmersion
    (P : ∀ ⦃X Y : Scheme.{u}⦄, (X ⟶ Y) → Prop)
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    [HasRingHomProperty P Q] [MorphismProperty.IsMultiplicative P] :
    MorphismProperty.RespectsRight P @IsOpenImmersion :=
  let P' : MorphismProperty Scheme.{u} := P
  have : HasRingHomProperty P' Q := ‹_›
  have : P'.IsMultiplicative := ‹_›
  IsZariskiLocalAtSource.respectsRight_isOpenImmersion P'

end AlgebraicGeometry
