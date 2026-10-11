/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Unramified morphisms

A morphism of schemes is unramified when it is locally of finite type and formally
unramified. This packages the two conditions as a morphism property, so geometric
constructions such as the singular subscheme of a nodal family can state the usual
unramifiedness condition directly.

## Main definition

* `TauCeti.AlgebraicGeometry.Unramified f`: `f` is locally of finite type and formally
  unramified.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

namespace TauCeti.AlgebraicGeometry

/-- A morphism of schemes is unramified if it is locally of finite type and formally
unramified. -/
@[mk_iff]
class Unramified (f : X ⟶ Y) : Prop extends LocallyOfFiniteType f, FormallyUnramified f

lemma unramified_eq : @Unramified =
    (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty Scheme) := by
  ext X Y f
  rw [unramified_iff]
  rfl

namespace Unramified

lemma of_locallyOfFiniteType {X Y : Scheme} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [FormallyUnramified f] : Unramified f := by
  constructor

instance : MorphismProperty.IsStableUnderComposition @Unramified := by
  rw [unramified_eq]
  exact MorphismProperty.IsStableUnderComposition.inf

instance : MorphismProperty.IsStableUnderBaseChange @Unramified := by
  rw [unramified_eq]
  exact MorphismProperty.IsStableUnderBaseChange.inf

instance : MorphismProperty.IsMultiplicative @Unramified := by
  rw [unramified_eq]
  exact MorphismProperty.IsMultiplicative.inf

instance : IsZariskiLocalAtSource @Unramified := by
  rw [unramified_eq]
  have h₁ : IsZariskiLocalAtSource @LocallyOfFiniteType := by
    have h : HasRingHomProperty @LocallyOfFiniteType RingHom.FiniteType :=
      AlgebraicGeometry.instHasRingHomPropertyLocallyOfFiniteTypeFiniteType
    exact @HasRingHomProperty.instIsZariskiLocalAtSource _ _ h
  have h₂ : IsZariskiLocalAtSource @FormallyUnramified := by
    have h : HasRingHomProperty @FormallyUnramified RingHom.FormallyUnramified := inferInstance
    exact @HasRingHomProperty.instIsZariskiLocalAtSource _ _ h
  exact @CategoryTheory.MorphismProperty.IsLocalAtSource.inf Scheme inferInstance
    _ @LocallyOfFiniteType @FormallyUnramified h₁ h₂

instance : IsZariskiLocalAtTarget @Unramified := by
  rw [unramified_eq]
  have h₁ : IsZariskiLocalAtTarget @LocallyOfFiniteType := by
    have h : HasRingHomProperty @LocallyOfFiniteType RingHom.FiniteType :=
      AlgebraicGeometry.instHasRingHomPropertyLocallyOfFiniteTypeFiniteType
    exact @HasRingHomProperty.instIsZariskiLocalAtTarget _ _ h
  have h₂ : IsZariskiLocalAtTarget @FormallyUnramified := by
    have h : HasRingHomProperty @FormallyUnramified RingHom.FormallyUnramified := inferInstance
    exact @HasRingHomProperty.instIsZariskiLocalAtTarget _ _ h
  exact @CategoryTheory.MorphismProperty.IsLocalAtTarget.inf Scheme inferInstance
    _ @LocallyOfFiniteType @FormallyUnramified h₁ h₂

instance (priority := 900) {X Y : Scheme} (f : X ⟶ Y) [IsClosedImmersion f] :
    Unramified f := by
  apply of_locallyOfFiniteType

instance (priority := 900) {X Y : Scheme} (f : X ⟶ Y)
    [AlgebraicGeometry.IsImmersion f] :
    Unramified f := by
  apply of_locallyOfFiniteType

instance (priority := 900) {X Y : Scheme} (f : X ⟶ Y) [Etale f] : Unramified f := by
  apply of_locallyOfFiniteType

end Unramified

end TauCeti.AlgebraicGeometry
