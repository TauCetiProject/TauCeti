/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.MorphismProperty.Descent

/-!
# Surjective descent for geometrically-`P` morphisms

If an object property `P` of schemes descends along flat surjective morphisms, then
`geometrically P` descends along arbitrary surjective morphisms of schemes.

## Main declarations

* `TauCeti.AlgebraicGeometry.geometrically_descendsAlong_surjective`: general descent principle
  for `AlgebraicGeometry.geometrically P` along surjective morphisms.
-/

public section

open CategoryTheory Limits MorphismProperty AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- If an object property `P` descends along flat surjective morphisms, then `geometrically P`
descends along arbitrary surjective morphisms. -/
theorem geometrically_descendsAlong_surjective (P : ObjectProperty Scheme.{u})
    (hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f], P X → P Y) :
    (geometrically P).DescendsAlong @Surjective.{u} where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := fun K _ y W₀ pY pK hW₀ ↦ by
    have : Surjective f := hf
    obtain ⟨t, -⟩ := (pullback.snd f y).surjective (IsLocalRing.closedPoint K)
    let α := (pullback f y).fromSpecResidueField t ≫ pullback.snd f y
    let β := (pullback f y).fromSpecResidueField t ≫ pullback.fst f y
    have hαy : α ≫ y = β ≫ f := by simp [α, β, ← pullback.condition]
    exact hP (pullback.fst pK α)
      (hfst β _ _ (IsPullback.of_right' (hαy ▸ (IsPullback.of_hasPullback pK α).paste_horiz hW₀)
        h.flip))

end AlgebraicGeometry

end TauCeti
