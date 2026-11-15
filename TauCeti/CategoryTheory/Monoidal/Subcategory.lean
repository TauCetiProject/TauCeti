/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Subcategory

/-!
# Evaluation, coevaluation and precomposition in a closed monoidal full subcategory

If `P` is a monoidal property of objects of a closed monoidal category `C` that is closed under
internal Homs, Mathlib makes the full subcategory of `P` closed monoidal
(`CategoryTheory.ObjectProperty.fullMonoidalClosedSubcategory`), with internal Homs computed in
`C` (`CategoryTheory.ObjectProperty.ihom_obj`, `CategoryTheory.ObjectProperty.ihom_map_hom`).
This file records that its evaluation, coevaluation and precomposition maps are also those of
`C`, so that computations with internal Homs in the subcategory reduce to computations in `C`.

## Main declarations

* `CategoryTheory.ObjectProperty.ihom_ev_app_hom` and
  `CategoryTheory.ObjectProperty.ihom_coev_app_hom`: evaluation and coevaluation;
* `CategoryTheory.ObjectProperty.pre_app_hom`: precomposition with a morphism of the
  subcategory.
-/

public section

namespace CategoryTheory.ObjectProperty

open MonoidalCategory MonoidalClosed

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  (P : ObjectProperty C) [P.IsMonoidal] [P.IsMonoidalClosed]

/-- Evaluation in the closed monoidal full subcategory is evaluation in the ambient category. -/
@[simp]
theorem ihom_ev_app_hom (X Y : P.FullSubcategory) :
    ((ihom.ev X).app Y).hom = (ihom.ev X.obj).app Y.obj :=
  (rfl)

/-- Coevaluation in the closed monoidal full subcategory is coevaluation in the ambient
category. -/
@[simp]
theorem ihom_coev_app_hom (X Y : P.FullSubcategory) :
    ((ihom.coev X).app Y).hom = (ihom.coev X.obj).app Y.obj :=
  (rfl)

variable {P}

/-- Precomposition of internal Homs in the closed monoidal full subcategory is precomposition in
the ambient category. -/
@[simp]
theorem pre_app_hom {X X' : P.FullSubcategory} (f : X ⟶ X') (Y : P.FullSubcategory) :
    ((pre f).app Y).hom = (pre f.hom).app Y.obj := by
  -- Both maps are the transpose of `f ▷ _` followed by evaluation in `C`.
  refine ((eq_curry_iff (A := X.obj) _ _).mpr ?_).trans
    ((curry_eq_iff _ _).mpr (uncurry_pre f.hom Y.obj).symm)
  exact congrArg InducedCategory.Hom.hom (id_tensor_pre_app_comp_ev f Y)

end CategoryTheory.ObjectProperty
