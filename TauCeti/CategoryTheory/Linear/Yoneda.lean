/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Limits and the linear Yoneda embedding

For an object `Y` of a `k`-linear preadditive category `C`, the functor
`Hom(-, Y) = (linearYoneda k C).obj Y : Cᵒᵖ ⥤ ModuleCat k` preserves limits: it sends colimits in
`C` to limits of `k`-modules. Read as a functor `C ⥤ (ModuleCat k)ᵒᵖ`, it preserves colimits.
Both follow from the corresponding statement for the Yoneda embedding, through Mathlib's
`whiskering_linearYoneda` and the reflection of limits by the forgetful functor of `k`-modules.

## Main declarations

* `CategoryTheory.preservesLimits_linearYoneda_obj`: `Hom(-, Y)` preserves limits.
* `CategoryTheory.preservesColimits_linearYoneda_obj_rightOp`: `Hom(-, Y)`, read in the opposite
  category of `k`-modules, preserves colimits.
-/

public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C] (k : Type w) [Ring k] [Linear k C]

/-- `Hom(-, Y)` sends colimits in `C` to limits of `k`-modules. -/
instance preservesLimits_linearYoneda_obj (Y : C) :
    PreservesLimits ((linearYoneda k C).obj Y) := by
  have hforget : (linearYoneda k C).obj Y ⋙ forget (ModuleCat.{v} k) = yoneda.obj Y :=
    Functor.congr_obj (whiskering_linearYoneda k C) Y
  have : PreservesLimits ((linearYoneda k C).obj Y ⋙ forget (ModuleCat.{v} k)) :=
    hforget ▸ inferInstance
  exact preservesLimits_of_reflects_of_preserves _ (forget (ModuleCat.{v} k))

/-- `Hom(-, Y)`, read as a functor to the opposite category of `k`-modules, preserves colimits. -/
instance preservesColimits_linearYoneda_obj_rightOp (Y : C) :
    PreservesColimits ((linearYoneda k C).obj Y).rightOp :=
  preservesColimits_rightOp _

end CategoryTheory
