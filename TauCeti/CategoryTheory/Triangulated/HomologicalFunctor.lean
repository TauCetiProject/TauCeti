/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated

import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Homological functors: composition, rotated exactness, and elementwise lifting

Postcomposing a homological functor `E : C ⥤ A` from a pretriangulated category to an abelian
category with a functor `G : A ⥤ B` preserving zero morphisms and homology yields a homological
functor `E ⋙ G : C ⥤ B`.

We also provide:
* `CategoryTheory.Functor.map_distinguished_op_exact₃₁`: the sign-free exactness statement at
  `F((T.obj₁)⟦1⟧)` for a contravariant homological functor `F : Cᵒᵖ ⥤ A` applied to a
  distinguished triangle `T` in `C`.
* `CategoryTheory.Functor.exists_map_op_mor₂_eq_of_moduleCat` and
  `CategoryTheory.Functor.exists_map_op_mor₂_eq_of_addCommGrpCat`: elementwise exactness for
  contravariant homological functors valued in `ModuleCat R` and `AddCommGrpCat`.

## Main results

* `CategoryTheory.Functor.instIsHomologicalComp`: `(E ⋙ G).IsHomological`.
* `CategoryTheory.Functor.map_distinguished_op_exact₃₁`: exactness of
  `F((T.obj₂)⟦1⟧) ⟶ F((T.obj₁)⟦1⟧) ⟶ F(T.obj₃)` without sign.
* `CategoryTheory.Functor.exists_map_op_mor₂_eq_of_moduleCat`,
  `CategoryTheory.Functor.exists_map_op_mor₂_eq_of_addCommGrpCat`: elementwise lifting along
  `F.map T.mor₂.op`.
-/

public section

namespace CategoryTheory.Functor

open CategoryTheory Pretriangulated Limits Opposite

/-- Postcomposing a homological functor with a functor preserving zero morphisms and homology
yields a homological functor. -/
instance instIsHomologicalComp {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {A : Type*} [Category* A] [Abelian A] {B : Type*} [Category* B] [Abelian B]
    (E : C ⥤ A) [E.IsHomological] (G : A ⥤ B) [G.PreservesZeroMorphisms] [G.PreservesHomology] :
    (E ⋙ G).IsHomological where
  exact s hs := by
    simpa only [ShortComplex.map_comp] using (E.map_distinguished_exact s hs).map G

section Contravariant

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- For a contravariant homological functor `F : Cᵒᵖ ⥤ A` and a distinguished triangle `T` in `C`,
the sign-free rotated complex
`F((T.obj₂)⟦1⟧) ──F((T.mor₁⟦1⟧').op)──▶ F((T.obj₁)⟦1⟧) ──F(T.mor₃.op)──▶ F(T.obj₃)`
is exact. -/
theorem map_distinguished_op_exact₃₁ {A : Type*} [Category* A] [Abelian A]
    (F : Cᵒᵖ ⥤ A) [F.IsHomological] (T : Triangle C) (hT : T ∈ distTriang C) :
    (ShortComplex.mk (F.map (T.mor₁⟦(1 : ℤ)⟧').op) (F.map T.mor₃.op) (by
      simp only [← F.map_comp, ← op_comp, comp_distTriang_mor_zero₃₁ _ hT, op_zero,
        F.map_zero])).Exact := by
  refine ShortComplex.exact_of_iso ?_
    (F.map_distinguished_op_exact _ (rot_of_distTriang _ (rot_of_distTriang _ hT)))
  exact ShortComplex.isoMk (-Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)

/-- Elementwise exactness of a contravariant homological functor `F : Cᵒᵖ ⥤ ModuleCat R` on a
distinguished triangle `T`: if `F.map T.mor₁.op x = 0`, then `x` lies in the image of
`F.map T.mor₂.op`. -/
theorem exists_map_op_mor₂_eq_of_moduleCat {R : Type*} [Ring R]
    (F : Cᵒᵖ ⥤ ModuleCat R) [F.IsHomological] {T : Triangle C} (hT : T ∈ distTriang C)
    {x : F.obj (op T.obj₂)} (hx : F.map T.mor₁.op x = 0) :
    ∃ y : F.obj (op T.obj₃), F.map T.mor₂.op y = x :=
  (ShortComplex.moduleCat_exact_iff _).1 (F.map_distinguished_op_exact T hT) x hx

/-- Elementwise exactness of a contravariant homological functor `E : Cᵒᵖ ⥤ AddCommGrpCat` on a
distinguished triangle `T`: if `E.map T.mor₁.op x = 0`, then `x` lies in the image of
`E.map T.mor₂.op`. -/
theorem exists_map_op_mor₂_eq_of_addCommGrpCat
    (E : Cᵒᵖ ⥤ AddCommGrpCat) [E.IsHomological] {T : Triangle C} (hT : T ∈ distTriang C)
    {x : E.obj (op T.obj₂)} (hx : E.map T.mor₁.op x = 0) :
    ∃ y : E.obj (op T.obj₃), E.map T.mor₂.op y = x :=
  (ShortComplex.ab_exact_iff _).1 (E.map_distinguished_op_exact T hT) x hx

end Contravariant

end CategoryTheory.Functor
