/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.Order.SuccPred.Archimedean

/-!
# Eventually constant functors from their successor maps

A functor `F : J ⥤ C` on a succ-archimedean order is eventually constant from `m` as soon as
`F.map (j ⟶ Order.succ j)` is an isomorphism for every `j ≥ m`
(`CategoryTheory.Functor.isEventuallyConstantFrom_of_isIso_map_succ`): every map `j ⟶ j'` with
`m ≤ j` is a composite of such successor maps.
-/

public section

namespace CategoryTheory.Functor

variable {J C : Type*} [Preorder J] [SuccOrder J] [IsSuccArchimedean J] [Category* C]

/-- A functor on a succ-archimedean order whose successor maps are isomorphisms from `m` on is
eventually constant from `m`. -/
theorem isEventuallyConstantFrom_of_isIso_map_succ {F : J ⥤ C} {m : J}
    (h : ∀ j, m ≤ j → IsIso (F.map (homOfLE (Order.le_succ j)))) :
    F.IsEventuallyConstantFrom m := by
  intro j f
  rw [Subsingleton.elim f (homOfLE (leOfHom f))]
  generalize leOfHom f = hmj
  clear f
  induction hmj using Succ.rec with
  | rfl => rw [Subsingleton.elim (homOfLE _) (𝟙 m), F.map_id]; infer_instance
  | succ j hj ih =>
    have := h j hj
    rw [← homOfLE_comp hj (Order.le_succ j), F.map_comp]
    infer_instance

end CategoryTheory.Functor
