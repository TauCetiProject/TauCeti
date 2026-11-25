/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Linearity of `colim` and of flipped functors

For an `R`-linear category `C`, the functor category `J ⥤ C` is `R`-linear with the objectwise
scalar action (`CategoryTheory.functorCategoryLinear`). This file records two consequences, the
scalar counterparts of the additivity of `colim` and of `Functor.flip`:

* `CategoryTheory.Limits.colim_linear`: taking colimits of shape `J` is an `R`-linear functor
  `(J ⥤ C) ⥤ C`, since a map out of a colimit is determined by its composites with the
  colimit insertions;
* `CategoryTheory.Functor.flip_linear`: if `F : C ⥤ D ⥤ E` is objectwise `R`-linear, that is, each
  `F.obj X` is `R`-linear, then `F.flip : D ⥤ C ⥤ E` is `R`-linear.
-/

public section

namespace CategoryTheory

open Limits

variable (R : Type*) [Semiring R]

/-- **`colim` is linear.** For an `R`-linear category `C` with colimits of shape `J`, taking the
colimit is an `R`-linear functor `(J ⥤ C) ⥤ C`. -/
instance Limits.colim_linear {J C : Type*} [Category* J] [Category* C] [Preadditive C]
    [Linear R C] [HasColimitsOfShape J C] : (colim (J := J) (C := C)).Linear R where
  map_smul {F G} α r := colimit.hom_ext fun j ↦ by
    rw [colimit.ι_map, Linear.comp_smul, colimit.ι_map, NatTrans.app_smul, Linear.smul_comp]

/-- **Flipping an objectwise linear functor gives a linear functor.** If each `F.obj X` is
`R`-linear, then `F.flip` is `R`-linear. -/
instance Functor.flip_linear {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive D] [Preadditive E] [CategoryTheory.Linear R D] [CategoryTheory.Linear R E]
    (F : C ⥤ D ⥤ E)
    [∀ X, (F.obj X).Linear R] : F.flip.Linear R where
  map_smul f r := by
    ext X
    exact Functor.map_smul (F.obj X) r f

end CategoryTheory
