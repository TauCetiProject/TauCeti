/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import TauCeti.RingTheory.Flat.Descent

/-!
# Flat morphisms satisfy fpqc descent

A morphism whose base change along a surjective, flat and quasi-compact morphism is flat is
itself flat. The affine statement is the descent of flatness of a module along a faithfully
flat extension of scalars (`RingHom.Flat.codescendsAlong_faithfullyFlat`), and Mathlib's
`AlgebraicGeometry.HasRingHomProperty.descendsAlong_flat` globalizes it.

We also provide
`CategoryTheory.MorphismProperty.of_isPullback_of_surjective_of_flat_of_quasiCompact`, which
applies fpqc descent (`DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`) along a cartesian
square directly from the typeclass instances `[Surjective f] [Flat f] [QuasiCompact f]`.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- If a morphism property of schemes satisfies fpqc descent (`DescendsAlong` surjective, flat,
quasi-compact morphisms), then it descends along any cartesian square whose base-change morphism
is surjective, flat and quasi-compact. -/
theorem _root_.CategoryTheory.MorphismProperty.of_isPullback_of_surjective_of_flat_of_quasiCompact
    {P : MorphismProperty Scheme.{u}}
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    {A X Y Z : Scheme.{u}} {fst : A ⟶ X} {snd : A ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    [Surjective f] [Flat f] [QuasiCompact f]
    (h : IsPullback fst snd f g) (hfst : P fst) : P g :=
  MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hfst

/-- **Flat morphisms satisfy fpqc descent.** Flatness descends along surjective, flat,
quasi-compact morphisms. -/
instance Flat.descendsAlong_surjective_inf_flat_inf_quasicompact :
    MorphismProperty.DescendsAlong @Flat.{u} (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat RingHom.Flat.codescendsAlong_faithfullyFlat

end AlgebraicGeometry
