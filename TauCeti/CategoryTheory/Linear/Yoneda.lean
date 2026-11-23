/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Limits and the linear Yoneda embedding

For an object `Y` of a `k`-linear preadditive category `C`, the functor
`Hom(-, Y) = (linearYoneda k C).obj Y : Cᵒᵖ ⥤ ModuleCat k` preserves limits of every size: it
sends colimits in `C` to limits of `k`-modules. Read as a functor `C ⥤ (ModuleCat k)ᵒᵖ`, it
preserves colimits. Both follow from the corresponding statement for the Yoneda embedding, through
Mathlib's `whiskering_linearYoneda` and the reflection of limits of every size by the forgetful
functor of `k`-modules, which factors through additive groups.

## Main declarations

* `CategoryTheory.preservesLimits_linearYoneda_obj`: `Hom(-, Y)` preserves limits.
* `CategoryTheory.preservesColimits_linearYoneda_obj_rightOp`: `Hom(-, Y)`, read in the opposite
  category of `k`-modules, preserves colimits.
-/

public section

universe t t' w v u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C] (k : Type w) [Ring k] [Linear k C]

/-- `Hom(-, Y)` sends colimits in `C` to limits of `k`-modules. -/
instance preservesLimits_linearYoneda_obj (Y : C) :
    PreservesLimitsOfSize.{t, t'} ((linearYoneda k C).obj Y) := by
  have hforget : (linearYoneda k C).obj Y ⋙ forget (ModuleCat.{v} k) = yoneda.obj Y :=
    Functor.congr_obj (whiskering_linearYoneda k C) Y
  have : PreservesLimitsOfSize.{t, t'} ((linearYoneda k C).obj Y ⋙ forget (ModuleCat.{v} k)) :=
    hforget ▸ inferInstance
  -- The forgetful functor of `k`-modules is the composite of the forgetful functors to additive
  -- groups and to types, which reflect limits of every size.
  have : ReflectsLimitsOfSize.{t, t'} (forget (ModuleCat.{v} k)) :=
    inferInstanceAs (ReflectsLimitsOfSize
      (forget₂ (ModuleCat.{v} k) AddCommGrpCat.{v} ⋙ forget AddCommGrpCat.{v}))
  exact preservesLimits_of_reflects_of_preserves _ (forget (ModuleCat.{v} k))

/-- `Hom(-, Y)`, read as a functor to the opposite category of `k`-modules, preserves colimits. -/
instance preservesColimits_linearYoneda_obj_rightOp (Y : C) :
    PreservesColimitsOfSize.{t, t'} ((linearYoneda k C).obj Y).rightOp :=
  preservesColimitsOfSize_rightOp _

end CategoryTheory
