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
import TauCeti.AlgebraicGeometry.Geometrically.Connected

/-!
# Geometric integrality of smooth, geometrically connected morphisms

After base change to a field, a smooth scheme is locally Noetherian with regular local rings.
Its local rings are therefore domains, and connectedness implies integrality via
`TauCeti.AlgebraicGeometry.isIntegral_of_connected_of_isRegularLocalRing_stalk`.

Over a field, a connected scheme with a rational point is geometrically connected
(`TauCeti.geometricallyConnected_of_section`). Hence a connected scheme smooth over a field with a
rational point is geometrically integral. Smoothness is needed here: the connected scheme
`Spec k[x, y] ⧸ (x y)` has the rational point `(0, 0)` but is not irreducible.

## Main declarations

* `TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral`: a smooth, geometrically connected
  morphism is geometrically integral.
* `TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral_of_section`: a connected scheme smooth
  over a field with a rational point is geometrically integral.

## References

* [The Stacks Project, Lemma 33.25.10 (0CDW)](https://stacks.math.columbia.edu/tag/0CDW), for the
  geometric integrality of a smooth connected scheme with a rational point.
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

/-- **A connected smooth scheme with a rational point is geometrically integral.** If `X` is a
connected scheme, `f : X ⟶ Spec k` is smooth over a field `k`, and `f` has a section `s`, then
`X ×_k Spec K` is integral for every field `K` over `k`. -/
theorem Smooth.geometricallyIntegral_of_section {k : Type u} [Field k] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of k)} [Smooth f] [ConnectedSpace X] {s : Spec (.of k) ⟶ X}
    (hs : s ≫ f = 𝟙 _) : GeometricallyIntegral f :=
  have := geometricallyConnected_of_section hs
  inferInstance

end AlgebraicGeometry

end TauCeti
