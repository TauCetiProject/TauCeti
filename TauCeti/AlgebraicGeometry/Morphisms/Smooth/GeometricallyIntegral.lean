/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

/-!
# Geometric integrality of smooth, geometrically connected morphisms

After base change to a field, a smooth scheme is locally Noetherian with regular local rings.
Its local rings are therefore domains, and connectedness implies integrality via
`TauCeti.AlgebraicGeometry.isIntegral_of_connected_of_isRegularLocalRing_stalk`.

## Main declaration

* `TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral`: a smooth, geometrically connected
  morphism is geometrically integral.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- A smooth, geometrically connected morphism of schemes is geometrically integral. -/
instance (priority := low) Smooth.geometricallyIntegral {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    [GeometricallyConnected f] : GeometricallyIntegral f := by
  constructor
  intro K _ y Z fst snd h
  have : Smooth snd := MorphismProperty.of_isPullback h inferInstance
  have : ConnectedSpace Z := GeometricallyConnected.geometrically_connectedSpace y fst snd h
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian snd
  have : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z) := isRegularLocalRing_stalk_of_smooth snd
  exact isIntegral_of_connected_of_isRegularLocalRing_stalk Z

end AlgebraicGeometry

end TauCeti
