/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import TauCeti.AlgebraicGeometry.Geometrically.Integral

/-!
# The structure morphism of the monoidal unit of `Over S`

The monoidal unit `𝟙_ (Over S)` of the cartesian monoidal category of schemes over `S` is `S`
itself, with structure morphism the identity `𝟙 S` (`CategoryTheory.Over.tensorUnit_hom`). This
file records, as instances, that this structure morphism is proper, smooth and geometrically
integral, so the monoidal unit is a group scheme over `S` satisfying the hypotheses of abelian
varieties and abelian schemes.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- The structure morphism of the monoidal unit of `Over S` is proper: it is the identity. -/
instance isProper_tensorUnit_hom (S : Scheme.{u}) : IsProper (𝟙_ (Over S)).hom := by
  rw [Over.tensorUnit_hom]
  exact inferInstanceAs (IsProper (𝟙 S))

/-- The structure morphism of the monoidal unit of `Over S` is smooth: it is the identity. -/
instance smooth_tensorUnit_hom (S : Scheme.{u}) : Smooth (𝟙_ (Over S)).hom := by
  rw [Over.tensorUnit_hom]
  exact inferInstanceAs (Smooth (𝟙 S))

/-- The structure morphism of the monoidal unit of `Over S` is geometrically integral: it is the
identity, an isomorphism (`geometricallyIntegral_of_isIso`). -/
instance geometricallyIntegral_tensorUnit_hom (S : Scheme.{u}) :
    GeometricallyIntegral (𝟙_ (Over S)).hom := by
  have : GeometricallyIntegral (𝟙 S) := geometricallyIntegral_of_isIso _
  rw [Over.tensorUnit_hom]
  exact this

end AlgebraicGeometry

end TauCeti
