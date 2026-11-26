/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-!
# Left Kan extensions along a fully faithful functor, evaluated on its essential image

For a fully faithful functor `G : C ⥤ D` along which pointwise left Kan extensions exist, the unit
of `G.op.lan ⊣ (whiskeringLeft _ _ _).obj G.op` is an isomorphism. Consequently, evaluating the
left Kan extension along `G.op` at an object `d` isomorphic to `G.obj c` is naturally isomorphic to
evaluation at `c`.

## Main declarations

* `CategoryTheory.Functor.lanCompEvaluationIsoOfIso`: the isomorphism
  `G.op.lan ⋙ (evaluation Dᵒᵖ A).obj (op d) ≅ (evaluation Cᵒᵖ A).obj (op c)` induced by
  `e : G.obj c ≅ d`, with its components `lanCompEvaluationIsoOfIso_hom_app` and
  `lanCompEvaluationIsoOfIso_inv_app`.
-/

public section

open CategoryTheory Opposite

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] {G : C ⥤ D} {A : Type*} [Category* A]

/-- For a fully faithful `G` along which pointwise left Kan extensions exist, evaluating the left
Kan extension along `G.op` at an object isomorphic to `G.obj c` is evaluation at `c`. -/
noncomputable def lanCompEvaluationIsoOfIso [G.Full] [G.Faithful]
    [∀ F : Cᵒᵖ ⥤ A, G.op.HasPointwiseLeftKanExtension F] {c : C} {d : D} (e : G.obj c ≅ d) :
    G.op.lan ⋙ (evaluation Dᵒᵖ A).obj (op d) ≅ (evaluation Cᵒᵖ A).obj (op c) :=
  isoWhiskerLeft G.op.lan ((evaluation Dᵒᵖ A).mapIso e.op) ≪≫
    isoWhiskerRight (asIso G.op.lanUnit).symm ((evaluation Cᵒᵖ A).obj (op c))

/-- The components of `lanCompEvaluationIsoOfIso` are `e` followed by the inverse of the unit. -/
@[simp]
lemma lanCompEvaluationIsoOfIso_hom_app [G.Full] [G.Faithful]
    [∀ F : Cᵒᵖ ⥤ A, G.op.HasPointwiseLeftKanExtension F] {c : C} {d : D} (e : G.obj c ≅ d)
    (F : Cᵒᵖ ⥤ A) :
    (lanCompEvaluationIsoOfIso e).hom.app F =
      (G.op.lan.obj F).map e.hom.op ≫ CategoryTheory.inv ((G.op.lanUnit.app F).app (op c)) := by
  simp [lanCompEvaluationIsoOfIso]

/-- The inverse of `lanCompEvaluationIsoOfIso` is the unit followed by `e.inv`. -/
@[simp]
lemma lanCompEvaluationIsoOfIso_inv_app [G.Full] [G.Faithful]
    [∀ F : Cᵒᵖ ⥤ A, G.op.HasPointwiseLeftKanExtension F] {c : C} {d : D} (e : G.obj c ≅ d)
    (F : Cᵒᵖ ⥤ A) :
    (lanCompEvaluationIsoOfIso e).inv.app F =
      (G.op.lanUnit.app F).app (op c) ≫ (G.op.lan.obj F).map e.inv.op := by
  simp [lanCompEvaluationIsoOfIso]

end CategoryTheory.Functor
