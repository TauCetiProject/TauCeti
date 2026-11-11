/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Filtered colimits of modules with independent universe levels

The native filtered-colimit cocone allows the module universe to be larger than the ring
universe. This file exports preservation by the forgetful functor for that universe combination.
-/

public noncomputable section

open CategoryTheory Limits

namespace ModuleCat

universe u v

/-- Forgetting modules preserves filtered colimits also when the module universe is larger
than the ring universe. -/
instance forget_preservesFilteredColimits_max (R : Type v) [Ring R] :
    PreservesFilteredColimits (CategoryTheory.forget (ModuleCat.{max u v} R)) where
  preserves_filtered_colimits J _ _ := by
    let : PreservesColimitsOfShape J
        (CategoryTheory.forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}) :=
      { preservesColimit := fun {F} ↦
          preservesColimit_of_preserves_colimit_cocone
            (ModuleCat.FilteredColimits.colimitCoconeIsColimit F)
            (AddCommGrpCat.FilteredColimits.colimitCoconeIsColimit
              (F ⋙ CategoryTheory.forget₂ (ModuleCat.{max u v} R)
                AddCommGrpCat.{max u v})) }
    exact Limits.comp_preservesColimitsOfShape
      (CategoryTheory.forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
      (CategoryTheory.forget AddCommGrpCat.{max u v})

end ModuleCat
