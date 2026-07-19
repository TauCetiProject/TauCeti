/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Identity morphisms are geometrically integral

Mathlib's `GeometricallyIntegral` API records stability of geometric integrality under base
change, but has no instance for identity morphisms. This file fills that gap with
`TauCeti.AlgebraicGeometry.geometricallyIntegral_id`: the identity morphism of any scheme is
geometrically integral, because every base change of `𝟙 X` along `Spec κ → X` (with `κ` a field)
is an isomorphism onto `Spec κ`, which is integral.

It is used as the geometric-integrality input for the trivial group scheme in
`TauCeti.AlgebraicGeometry.AbelianVariety.Trivial`.
-/

public section

open CategoryTheory AlgebraicGeometry MorphismProperty

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- The identity morphism of any scheme is geometrically integral: every base change of `𝟙 X` along
`Spec κ → X` (with `κ` a field) is an isomorphism onto `Spec κ`, which is integral.

This fills a small gap in Mathlib's `GeometricallyIntegral` API, which records stability under base
change but no instance for identities. -/
theorem geometricallyIntegral_id (X : Scheme.{u}) : GeometricallyIntegral (𝟙 X) := by
  rw [GeometricallyIntegral.eq_geometrically]
  intro κ _ y Z fst snd h
  have hiso : IsIso snd :=
    (isomorphisms Scheme).of_isPullback h (isomorphisms.infer_property (𝟙 X))
  exact IsIntegral.of_isIso (inv snd)

end AlgebraicGeometry

end TauCeti
