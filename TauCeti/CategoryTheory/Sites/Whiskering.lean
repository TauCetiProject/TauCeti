/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Additivity of the functor induced on sheaves

An additive functor `F : A ⥤ B` between preadditive categories induces an additive functor
`sheafCompose J F : Sheaf J A ⥤ Sheaf J B` (`CategoryTheory.Sheaf.additive_sheafCompose`), since
morphisms of sheaves are added sectionwise. For instance, forgetting the module structure of a
sheaf of `R`-modules sectionwise is additive, so it acts on complexes of sheaves.
-/

public section

open CategoryTheory

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) {A B : Type*} [Category* A]
  [Category* B] [Preadditive A] [Preadditive B] (F : A ⥤ B) [F.Additive] [J.HasSheafCompose F]

/-- The functor induced on sheaves by an additive functor is additive. -/
instance additive_sheafCompose : (sheafCompose J F).Additive where
  map_add {_ _ _ _} := by
    ext1
    ext U
    -- sums of morphisms of sheaves are computed sectionwise
    exact F.map_add

end CategoryTheory.Sheaf
