/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Tensoring modules preserves colimits

Over a commutative ring `R`, tensoring on the left with an `R`-module preserves colimits of every
shape, as the left adjoint of the internal hom of `ModuleCat R`. This file records that tensoring
on the right does too (`TauCeti.moduleCat_preservesColimitsOfShape_tensorRight`), through the
braiding.
-/

public section

namespace TauCeti

open CategoryTheory Limits MonoidalCategory

universe w w' u

/-- Tensoring on the right with an `R`-module preserves colimits of every shape. Tensoring on the
left already does, as the left adjoint of the internal hom. -/
instance moduleCat_preservesColimitsOfShape_tensorRight {R : Type u} [CommRing R] (J : Type w)
    [Category.{w'} J] (Z : ModuleCat.{u} R) : PreservesColimitsOfShape J (tensorRight Z) :=
  preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight Z)

end TauCeti
