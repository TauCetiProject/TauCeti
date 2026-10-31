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
the base case of isomorphisms:

* `TauCeti.AlgebraicGeometry.geometricallyIntegral_of_isIso`: an isomorphism of schemes is
  geometrically integral.
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

end AlgebraicGeometry

end TauCeti
