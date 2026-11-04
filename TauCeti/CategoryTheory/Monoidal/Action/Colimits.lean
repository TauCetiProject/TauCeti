/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Action.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Colimit preservation for the tensor self-action

A monoidal category acts on itself by tensoring. The action functor in Mathlib's native
module-object API and the tensor functor have the same objects and maps, but instance search
does not identify them automatically. These instances pass colimit preservation from tensoring
to that self-action, so colimit creation for module objects applies without local adapters.
-/

public section

universe v u v' u'

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.MonoidalCategory.MonoidalLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The tensor self-action preserves every colimit shape preserved by left tensoring. -/
instance preservesColimitsOfShape_actionLeft_self (J : Type u') [Category.{v'} J]
    (X : C) [PreservesColimitsOfShape J (tensorLeft X)] :
    PreservesColimitsOfShape J (actionLeft C X) :=
  inferInstanceAs (PreservesColimitsOfShape J (tensorLeft X))

/-- The tensor self-action preserves colimits of every size preserved by left tensoring. -/
instance preservesColimits_actionLeft_self (X : C)
    [PreservesColimitsOfSize.{v', u'} (tensorLeft X)] :
    PreservesColimitsOfSize.{v', u'} (actionLeft C X) where
  preservesColimitsOfShape := inferInstance

end CategoryTheory.MonoidalCategory.MonoidalLeftAction
