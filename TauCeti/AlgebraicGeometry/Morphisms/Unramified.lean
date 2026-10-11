/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Unramified morphisms

A morphism of schemes is unramified when it is locally of finite type and formally
unramified. This packages the two conditions as a morphism property, so geometric
constructions such as the singular subscheme of a nodal family can state the usual
unramifiedness condition directly.

## Main definition

* `AlgebraicGeometry.Unramified f`: `f` is locally of finite type and formally unramified.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes is unramified if it is locally of finite type and formally
unramified. -/
def Unramified : MorphismProperty Scheme := @LocallyOfFiniteType ⊓ @FormallyUnramified

instance : MorphismProperty.IsStableUnderComposition @Unramified where
  comp_mem f g hf hg :=
    ⟨MorphismProperty.comp_mem _ f g hf.1 hg.1,
      MorphismProperty.comp_mem _ f g hf.2 hg.2⟩

instance : MorphismProperty.IsStableUnderBaseChange @Unramified where
  of_isPullback sq hf :=
    ⟨MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq hf.1,
      MorphismProperty.of_isPullback (P := @FormallyUnramified) sq hf.2⟩

/-- The two conditions in the definition of an unramified morphism. -/
theorem unramified_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Unramified f ↔ LocallyOfFiniteType f ∧ FormallyUnramified f := Iff.rfl

end AlgebraicGeometry
