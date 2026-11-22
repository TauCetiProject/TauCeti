/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Condensed.Light.Monoidal
public import TauCeti.CategoryTheory.Monoidal.Closed.Preadditive

/-!
# Additivity of the tensor product of light condensed modules

Tensoring with a fixed light condensed module is a left adjoint, so the tensor product is
additive in each variable.
-/

public section

universe u

open CategoryTheory MonoidalCategory Limits

namespace LightCondensed

variable (R : Type u) [CommRing R]

/-- The tensor product of light condensed modules is additive in each variable. -/
instance : MonoidalPreadditive (LightCondMod.{u} R) :=
  have : HasBinaryCoproducts (LightCondMod.{u} R) := hasBinaryCoproducts_of_hasBinaryBiproducts
  TauCeti.monoidalPreadditive_of_isLeftAdjoint _

end LightCondensed
