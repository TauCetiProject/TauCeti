/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Semiring-linear functors out of a localization

Mathlib's `CategoryTheory.Localization.functor_linear_iff` states that when `L : C ⥤ D` is an
`R`-linear localization functor with respect to `W : MorphismProperty C`, a lifted functor
`G : D ⥤ E` is `R`-linear if and only if `F : C ⥤ E` is `R`-linear, assuming `[Ring R]`.
Its proof, however, only uses `[Semiring R]` once `D` and `L` carry compatible `R`-linear
structures.

This file provides that semiring generalization
`TauCeti.CategoryTheory.Localization.functor_linear_iff`, used in
`TauCeti.Algebra.Homology.DerivedCategory.Linear` to descend linearity of homology functors
over arbitrary semirings.
-/

public section

namespace TauCeti.CategoryTheory.Localization

open _root_.CategoryTheory _root_.CategoryTheory.Localization

section

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  (R : Type*) [Semiring R] [Linear R C] [Linear R D] [Linear R E] [L.Linear R]

/-- A functor `G : D ⥤ E` lifting `F : C ⥤ E` along an `R`-linear localization functor
`L : C ⥤ D` is `R`-linear if and only if `F` is `R`-linear. This generalizes Mathlib's
`CategoryTheory.Localization.functor_linear_iff` from `[Ring R]` to `[Semiring R]`. -/
theorem functor_linear_iff (F : C ⥤ E) (G : D ⥤ E) [Lifting L W F G] :
    F.Linear R ↔ G.Linear R := by
  constructor
  · intro
    have : (L ⋙ G).Linear R := Functor.linear_of_iso _ (Lifting.iso L W F G).symm
    have := Localization.essSurj L W
    rw [Functor.linear_iff]
    intro X r
    have e := L.objObjPreimageIso X
    have : r • 𝟙 X = e.inv ≫ (r • 𝟙 _) ≫ e.hom := by simp
    rw [this, G.map_comp, G.map_comp, ← L.map_id, ← L.map_smul, ← Functor.comp_map,
      (L ⋙ G).map_smul]
    simp
  · intro
    exact Functor.linear_of_iso _ (Lifting.iso L W F G)

end

end TauCeti.CategoryTheory.Localization
