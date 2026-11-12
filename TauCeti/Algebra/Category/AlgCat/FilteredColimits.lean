/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.AlgCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Filtered colimits of algebras as colimits of modules

The forgetful functor from algebras over a commutative ring `R` to `R`-modules preserves small
filtered colimits. Both categories compute such colimits on underlying types, and the forgetful
functor from `R`-modules to types reflects them, so this follows from the corresponding fact for
the forgetful functor from algebras to types. It lets module-theoretic properties of a filtered
colimit of algebras, such as flatness, be read off from the colimit of the underlying modules.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgCat

variable {R : Type u} [CommRing R]

/-- The forgetful functor from algebras to modules preserves small filtered colimits. -/
noncomputable instance forget₂Module_preservesFilteredColimits :
    PreservesFilteredColimits (forget₂ (AlgCat.{u} R) (ModuleCat.{u} R)) where
  preserves_filtered_colimits J _ _ :=
    have : PreservesColimitsOfShape J
        (forget₂ (AlgCat.{u} R) (ModuleCat.{u} R) ⋙ forget (ModuleCat.{u} R)) :=
      preservesColimitsOfShape_of_natIso (eqToIso HasForget₂.forget_comp).symm
    preservesColimitsOfShape_of_reflects_of_preserves _ (forget (ModuleCat.{u} R))

end AlgCat
