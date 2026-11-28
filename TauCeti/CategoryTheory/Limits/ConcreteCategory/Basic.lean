/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered

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
* `CategoryTheory.Limits.Concrete.exists_map_eq_zero_of_ι_eq_zero`: elements in a filtered colimit
  mapping to zero vanish at some later stage.
-/

public section

open CategoryTheory Limits

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

/-- In a concrete category with zero-preserving morphisms whose forgetful functor preserves the
colimit of `F`, an element at stage `n` of a filtered diagram that maps to zero in a colimit
cocone is annihilated by `F.map f` for some morphism `f : n ⟶ m`. -/
theorem exists_map_eq_zero_of_ι_eq_zero {C : Type*} [Category* C]
    {FC : C → C → Type*} {CC : C → Type*} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC] [∀ X : C, Zero (CC X)] [∀ X Y : C, ZeroHomClass (FC X Y) (CC X) (CC Y)]
    {J : Type*} [Category* J] [IsFiltered J] (F : J ⥤ C) [PreservesColimit F (forget C)]
    {c : Cocone F} (hc : IsColimit c) {n : J} {x : ToType (F.obj n)}
    (h : c.ι.app n x = (0 : ToType c.pt)) :
    ∃ (m : J) (f : n ⟶ m), F.map f x = (0 : ToType (F.obj m)) := by
  obtain ⟨m, f, g, hm⟩ := Concrete.isColimit_exists_of_rep_eq F hc x (0 : ToType (F.obj n))
    (h.trans (map_zero (ConcreteCategory.hom (c.ι.app n))).symm)
  exact ⟨m, f, by rwa [map_zero (ConcreteCategory.hom (F.map g))] at hm⟩

end CategoryTheory.Limits.Concrete
