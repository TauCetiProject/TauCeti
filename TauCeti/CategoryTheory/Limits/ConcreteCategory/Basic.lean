/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Limits and filtered colimits in concrete categories

The `j`-th coordinate of the image of an element under the map `IsLimit.map c hd α` between limit
cones in a concrete category is the image under `α j` of its `j`-th coordinate
(`CategoryTheory.Limits.IsLimit.map_π_apply`).

Every element of the point of a colimit cocone of a filtered diagram in a concrete category comes
from some stage (Mathlib's `CategoryTheory.Limits.Concrete.isColimit_exists_rep`). Finitely many
elements then come from a common stage, obtained by bounding their stages in the filtered
category.

## Main results

* `CategoryTheory.Limits.IsLimit.map_π_apply`: the elementwise form of
  `CategoryTheory.Limits.IsLimit.map_π`.
* `CategoryTheory.Limits.Concrete.isColimit_exists_rep_fin`: finitely many elements of the point
  of a colimit cocone of a filtered diagram come from a common stage.
-/

public section

open CategoryTheory

namespace CategoryTheory.Limits.IsLimit

/-- The `j`-th coordinate of the image of an element `x` under the map `hd.map c α` between limit
cones in a concrete category is the image under `α j` of the `j`-th coordinate of `x`. -/
@[simp]
theorem map_π_apply {C : Type*} [Category C]
    {FC : C → C → Type*} {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC] {J : Type*} [Category J] {F G : J ⥤ C} (c : Cone F) {d : Cone G}
    (hd : IsLimit d) (α : F ⟶ G) (j : J) (x : ToType c.pt) :
    -- The source of `d.π.app j` is given as `d.pt`, as `elementwise` does, so that the left-hand
    -- side is in simp normal form; `simp` still rewrites the usual `d.π.app j (hd.map c α x)`.
    ConcreteCategory.hom (X := d.pt) (d.π.app j) (hd.map c α x) = α.app j (c.π.app j x) := by
  rw [← ConcreteCategory.comp_apply, IsLimit.map_π, ConcreteCategory.comp_apply]

end CategoryTheory.Limits.IsLimit

namespace CategoryTheory.Limits.Concrete

/-- Finitely many elements of the point of a colimit cocone of a filtered diagram in a concrete
category come from a common stage. -/
theorem isColimit_exists_rep_fin {C : Type*} [Category C]
    {FC : C → C → Type*} {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC] {J : Type*} [Category J] [IsFiltered J] (F : J ⥤ C)
    [PreservesColimit F (forget C)] {c : Cocone F} (hc : IsColimit c) {ι : Type*} [Finite ι]
    (x : ι → ToType c.pt) :
    ∃ (k : J) (y : ι → ToType (F.obj k)), ∀ i, c.ι.app k (y i) = x i := by
  classical
  cases nonempty_fintype ι
  choose j y hy using fun i => isColimit_exists_rep F hc (x i)
  let O : Finset J := Finset.univ.image j
  have hO (i : ι) : j i ∈ O := Finset.mem_image_of_mem j (Finset.mem_univ i)
  refine ⟨IsFiltered.sup O ∅, fun i => F.map (IsFiltered.toSup O ∅ (hO i)) (y i), fun i => ?_⟩
  rw [← hy i, ← c.w (IsFiltered.toSup O ∅ (hO i)), ConcreteCategory.comp_apply]

end CategoryTheory.Limits.Concrete
