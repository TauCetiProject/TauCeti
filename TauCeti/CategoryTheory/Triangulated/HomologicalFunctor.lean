/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated

/-!
# Homological functors: composition and rotated exactness

Postcomposing a homological functor `E : C ⥤ A` from a pretriangulated category to an abelian
category with a functor `G : A ⥤ B` preserving zero morphisms and homology yields a homological
functor `E ⋙ G : C ⥤ B`.

We also provide `CategoryTheory.Functor.map_distinguished_op_exact₃₁`, the sign-free exactness
statement at `F((T.obj₁)⟦1⟧)` for a contravariant homological functor `F : Cᵒᵖ ⥤ A` applied to a
distinguished triangle `T` in `C`.

## Main results

* `CategoryTheory.Functor.instIsHomologicalComp`: `(E ⋙ G).IsHomological`.
* `CategoryTheory.Functor.map_distinguished_op_exact₃₁`: exactness of
  `F((T.obj₂)⟦1⟧) ⟶ F((T.obj₁)⟦1⟧) ⟶ F(T.obj₃)` without sign.
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

/-- For a contravariant homological functor `F : Cᵒᵖ ⥤ A` and a distinguished triangle `T` in `C`,
the sign-free rotated complex
`F((T.obj₂)⟦1⟧) ──F((T.mor₁⟦1⟧').op)──▶ F((T.obj₁)⟦1⟧) ──F(T.mor₃.op)──▶ F(T.obj₃)`
is exact. -/
theorem map_distinguished_op_exact₃₁ {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {A : Type*} [Category* A] [Abelian A] (F : Cᵒᵖ ⥤ A) [F.IsHomological]
    (T : Triangle C) (hT : T ∈ distTriang C) :
    (ShortComplex.mk (F.map (T.mor₁⟦(1 : ℤ)⟧').op) (F.map T.mor₃.op) (by
      rw [← F.map_comp, ← op_comp, comp_distTriang_mor_zero₃₁ _ hT, op_zero,
        F.map_zero])).Exact := by
  refine ShortComplex.exact_of_iso ?_
    (F.map_distinguished_op_exact _ (rot_of_distTriang _ (rot_of_distTriang _ hT)))
  exact ShortComplex.isoMk (-Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)

end CategoryTheory.Functor
