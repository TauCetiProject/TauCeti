/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Isomorphisms are geometrically integral

Mathlib's `GeometricallyIntegral` API records stability of geometric integrality under base
change, but has no instance for isomorphisms. This file fills that gap with
`TauCeti.AlgebraicGeometry.geometricallyIntegral_of_isIso`: every isomorphism of schemes, in
particular every identity morphism, is geometrically integral.

It is used as the geometric-integrality input for the trivial group scheme in
`TauCeti.AlgebraicGeometry.AbelianVariety.Trivial`.
-/

public section

open CategoryTheory AlgebraicGeometry MorphismProperty

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- Every isomorphism of schemes is geometrically integral.

This fills a small gap in Mathlib's `GeometricallyIntegral` API, which records stability under base
change but no instance for isomorphisms (in particular none for identity morphisms). -/
instance (priority := low) geometricallyIntegral_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    GeometricallyIntegral f := by
  rw [GeometricallyIntegral.eq_geometrically]
  intro κ _ y Z fst snd h
  -- every base change of `f` along `Spec κ → Y` is again an isomorphism, and `Spec κ` is integral
  have hiso : IsIso snd :=
    (isomorphisms Scheme).of_isPullback h (isomorphisms.infer_property f)
  exact IsIntegral.of_isIso (inv snd)

end AlgebraicGeometry

end TauCeti
