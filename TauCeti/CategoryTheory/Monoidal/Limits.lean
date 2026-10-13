/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Colimit preservation for tensoring with the unit

The left unitor identifies tensoring on the left by the tensor unit with the identity functor.
Thus this functor preserves colimits, without any closedness assumption on the monoidal category.
This allows constructions that require tensoring to preserve coproducts to be used with the unit.
-/

public section

open CategoryTheory Limits MonoidalCategory

universe w w' v u

namespace TauCeti

/-- Tensoring on the left with the tensor unit preserves colimits, via
`MonoidalCategory.leftUnitorNatIso`. -/
instance preservesColimits_tensorUnitLeft (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    PreservesColimitsOfSize.{w, w'} (tensorUnitLeft C) :=
  preservesColimits_of_natIso (leftUnitorNatIso C).symm

end TauCeti
