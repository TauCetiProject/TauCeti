/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Limits and the functor induced on sheaves

If a functor `F : A ⥤ B` preserves limits of shape `K`, then so does the induced functor
`sheafCompose J F : Sheaf J A ⥤ Sheaf J B`
(`CategoryTheory.Sheaf.preservesLimitsOfShape_sheafCompose`), since limits of sheaves are computed
on the underlying presheaves (Mathlib's `CategoryTheory.Sites.Limits`).
-/

public section

open CategoryTheory Limits

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)

/-- If `F` preserves limits of shape `K`, then so does the induced functor on sheaves, since limits
of sheaves are computed on the underlying presheaves. -/
instance preservesLimitsOfShape_sheafCompose {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) [J.HasSheafCompose F] (K : Type*) [Category* K] [HasLimitsOfShape K A]
    [PreservesLimitsOfShape K F] :
    PreservesLimitsOfShape K (sheafCompose J F) := by
  -- `sheafCompose J F` is defined as `ObjectProperty.lift` of the composite
  -- `sheafToPresheaf J A ⋙ (whiskeringRight _ _ _).obj F`, so composing it with
  -- `sheafToPresheaf J B` gives that composite definitionally, as in Mathlib's
  -- `CategoryTheory.Sites.Whiskering`.
  have : PreservesLimitsOfShape K (sheafCompose J F ⋙ sheafToPresheaf J B) :=
    inferInstanceAs
      (PreservesLimitsOfShape K (sheafToPresheaf J A ⋙ (Functor.whiskeringRight _ _ _).obj F))
  exact preservesLimitsOfShape_of_reflects_of_preserves _ (sheafToPresheaf J B)

end CategoryTheory.Sheaf
