/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.CategoryTheory.MorphismProperty.Descent
import TauCeti.AlgebraicGeometry.Geometrically.Descent
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Reduced

/-!
# Geometrically integral morphisms

Mathlib's `AlgebraicGeometry.GeometricallyIntegral` is stable under base change. This file records
its compatibility with isomorphisms and Zariski-local and surjective descent on the target:

* `TauCeti.AlgebraicGeometry.geometricallyIntegral_of_isIso`: an isomorphism of schemes is
  geometrically integral.
* `TauCeti.AlgebraicGeometry.isClosedUnderIsomorphisms_isIntegral`: `AlgebraicGeometry.IsIntegral`
  is closed under scheme isomorphisms.
* `TauCeti.AlgebraicGeometry.respectsIso_geometricallyIntegral`: `GeometricallyIntegral` respects
  isomorphisms.
* `TauCeti.AlgebraicGeometry.isZariskiLocalAtTarget_geometricallyIntegral`: `GeometricallyIntegral`
  is Zariski-local on the target.
* `TauCeti.AlgebraicGeometry.isIntegral_of_flat_of_surjective`,
  `TauCeti.AlgebraicGeometry.descendsAlong_surjective_geometricallyIntegral`,
  `TauCeti.AlgebraicGeometry.geometricallyIntegral_iff_of_isPullback_of_surjective`:
  flat-surjective and surjective descent for integrality and geometric integrality.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- An isomorphism of schemes is geometrically integral. -/
lemma geometricallyIntegral_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    GeometricallyIntegral f :=
  ⟨fun _ _ _ _ _ snd h ↦ have := h.isIso_snd_of_isIso; .of_isIso (inv snd)⟩

/-- `AlgebraicGeometry.IsIntegral` is closed under isomorphisms of schemes. -/
instance isClosedUnderIsomorphisms_isIntegral :
    ObjectProperty.IsClosedUnderIsomorphisms _root_.AlgebraicGeometry.IsIntegral :=
  ⟨fun e _ ↦ .of_isIso e.hom⟩

/-- `GeometricallyIntegral` respects isomorphisms on both source and target. -/
instance respectsIso_geometricallyIntegral : MorphismProperty.RespectsIso @GeometricallyIntegral :=
  GeometricallyIntegral.eq_geometrically ▸ inferInstance

/-- `GeometricallyIntegral` is Zariski-local on the target. -/
instance isZariskiLocalAtTarget_geometricallyIntegral :
    IsZariskiLocalAtTarget @GeometricallyIntegral :=
  GeometricallyIntegral.eq_geometrically ▸ inferInstance

open Limits MorphismProperty

/-- Integrality of a scheme descends along any flat surjective morphism, with no Noetherian
assumption. -/
theorem isIntegral_of_flat_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
    [IsIntegral X] : IsIntegral Y :=
  have := f.isReduced_of_flat_of_surjective
  have := f.surjective.irreducibleSpace f.continuous
  isIntegral_of_irreducibleSpace_of_isReduced Y

/-- `GeometricallyIntegral` descends along arbitrary surjective morphisms of schemes. -/
instance descendsAlong_surjective_geometricallyIntegral :
    DescendsAlong @GeometricallyIntegral.{u} @Surjective.{u} :=
  GeometricallyIntegral.eq_geometrically ▸ geometrically_descendsAlong_surjective IsIntegral
    fun f _ _ hX ↦ have := hX; isIntegral_of_flat_of_surjective f

/-- In a pullback square along a surjective morphism `f : X ⟶ Z`, `fst` is geometrically integral
iff `g` is geometrically integral. -/
theorem geometricallyIntegral_iff_of_isPullback_of_surjective {A X Y Z : Scheme.{u}}
    {fst : A ⟶ X} {snd : A ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) [Surjective f] :
    GeometricallyIntegral fst ↔ GeometricallyIntegral g :=
  MorphismProperty.iff_of_isPullback (P := @GeometricallyIntegral) (Q := @Surjective) h
    inferInstance

end AlgebraicGeometry

end TauCeti
