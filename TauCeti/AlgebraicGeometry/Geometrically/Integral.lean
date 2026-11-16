/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Geometrically integral morphisms

Mathlib's `AlgebraicGeometry.GeometricallyIntegral` is stable under base change. This file records
its compatibility with isomorphisms and Zariski-local descent on the target:

* `TauCeti.AlgebraicGeometry.geometricallyIntegral_of_isIso`: an isomorphism of schemes is
  geometrically integral.
* `TauCeti.AlgebraicGeometry.isClosedUnderIsomorphisms_isIntegral`: `AlgebraicGeometry.IsIntegral`
  is closed under scheme isomorphisms.
* `TauCeti.AlgebraicGeometry.respectsIso_geometricallyIntegral`: `GeometricallyIntegral` respects
  isomorphisms.
* `TauCeti.AlgebraicGeometry.isZariskiLocalAtTarget_geometricallyIntegral`: `GeometricallyIntegral`
  is Zariski-local on the target.
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

end AlgebraicGeometry

end TauCeti
