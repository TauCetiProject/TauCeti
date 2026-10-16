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

open CategoryTheory AlgebraicGeometry Limits

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

instance : HasRingHomProperty @Unramified
    (fun f ↦ f.FiniteType ∧ f.FormallyUnramified) := by
  rw [unramified_eq]
  exact HasRingHomProperty.inf

/-- The affine criterion for an unramified morphism. -/
theorem Spec_iff {R S : CommRingCat.{u}} {φ : R ⟶ S} :
    Unramified (Spec.map φ) ↔
      letI := φ.hom.toAlgebra
      Algebra.Unramified R S := by
  rw [HasRingHomProperty.Spec_iff (P := @Unramified)]
  algebraize [φ.hom]
  constructor
  · rintro ⟨hft, hfu⟩
    exact ⟨hfu, hft⟩
  · intro h
    exact ⟨h.finiteType, h.formallyUnramified⟩

/-- If a composite is unramified, then its first map is unramified. -/
theorem of_comp {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Unramified (f ≫ g)] : Unramified f :=
  { toLocallyOfFiniteType := locallyOfFiniteType_of_comp f g
    toFormallyUnramified := FormallyUnramified.of_comp f g }

instance : MorphismProperty.IsStableUnderComposition @Unramified := by
  rw [unramified_eq]
  exact MorphismProperty.IsStableUnderComposition.inf

instance isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @Unramified := by
  rw [unramified_eq]
  exact MorphismProperty.IsStableUnderBaseChange.inf

instance : MorphismProperty.IsMultiplicative @Unramified := by
  rw [unramified_eq]
  exact MorphismProperty.IsMultiplicative.inf

instance unramified_comp {Z : Scheme.{u}} (g : Y ⟶ Z)
    [Unramified f] [Unramified g] : Unramified (f ≫ g) :=
  MorphismProperty.comp_mem _ f g ‹Unramified f› ‹Unramified g›

instance {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [Unramified g] :
    Unramified (pullback.fst f g) :=
  isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f g).flip inferInstance

instance {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [Unramified f] :
    Unramified (pullback.snd f g) :=
  isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f g) inferInstance

instance (priority := 900) {X Y : Scheme} (f : X ⟶ Y)
    [AlgebraicGeometry.IsImmersion f] :
    Unramified f := by
  exact ⟨⟩

instance (priority := 900) {X Y : Scheme} (f : X ⟶ Y) [Etale f] : Unramified f := by
  exact ⟨⟩

instance (f : X ⟶ Y) (V : Y.Opens) [Unramified f] : Unramified (f ∣_ V) :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict f V).flip ‹Unramified f›

instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [Unramified f] :
    Unramified (f.resLE V U e) := by
  delta Scheme.Hom.resLE
  infer_instance

end Unramified

end TauCeti.AlgebraicGeometry
