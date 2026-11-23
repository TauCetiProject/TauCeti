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

Mathlib also passes from fpqc to fppf descent for properties local on the target, by an anonymous
instance which instance search does not apply to concrete properties such as `@Flat`.
`MorphismProperty.descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation` names it,
so that it can be invoked for a given property.
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

namespace CategoryTheory.MorphismProperty

open AlgebraicGeometry

/-- **fpqc descent implies fppf descent.** A property of morphisms of schemes which is local on
the target and descends along surjective, flat, quasi-compact morphisms descends along surjective,
flat morphisms locally of finite presentation. This is Mathlib's instance, stated for a generic
predicate: instance search does not unify it with concrete predicates such as `@Flat`. -/
theorem descendsAlong_surjective_inf_flat_inf_locallyOfFinitePresentation
    (P : MorphismProperty Scheme.{u}) [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    [IsZariskiLocalAtTarget P] :
    P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
  inferInstance

end CategoryTheory.MorphismProperty
