/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.FinitelyPresentedFunctor.AlmostSplit
public import TauCeti.CategoryTheory.Preadditive.ModCat.Basic

/-!
# The radical and simple functors as modules

For an object `Z` of a preadditive category `C`, the radical subfunctor of `Hom(-, Z)` and
the quotient by that radical are objects of `ModCat C`.
-/

public section

universe v u

open CategoryTheory Preadditive

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The radical subfunctor `rad(-, Z)` of the representable module on `Z`. -/
abbrev radical (Z : C) : ModCat.{v} C := ⟨radicalFunctor Z, (additiveFunctor_iff _).2
  { map_add := by
      intro W W' k l
      let i := radicalFunctorι Z
      have : Mono (i.app W') := inferInstanceAs (Mono ((radicalFunctorι Z).app W'))
      rw [← cancel_mono (i.app W'), add_comp, i.naturality, i.naturality, i.naturality]
      simp [comp_add] }⟩

/-- The quotient `Hom(-, Z) / rad(-, Z)` as a module on the preadditive category. -/
noncomputable abbrev simple (Z : C) : ModCat.{v} C :=
  ⟨simpleFunctor Z, (additiveFunctor_iff _).2 inferInstance⟩

end TauCeti.ModCat
