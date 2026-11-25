/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Yoneda

/-!
# Yoneda sections on a presheaf diagonal

A map from a representable presheaf to the square of a presheaf classifies two sections.
The second leg of a cone over the presheaf diagonal restricts these sections to equal sections.
-/

public section

namespace CategoryTheory.Limits.PullbackCone

open Opposite

universe u v

/-- The second leg of a cone over a presheaf diagonal restricts the two sections classified by
the map from a representable presheaf to the square to equal sections. -/
theorem map_yonedaEquiv_prod_fst_eq_snd {C : Type v} [Category.{u} C]
    {F : Cᵒᵖ ⥤ Type u} {T : C} {a : yoneda.obj T ⟶ F ⨯ F}
    (cone : PullbackCone (diag F) a) {W : Cᵒᵖ} (x : cone.pt.obj W) :
    F.map (cone.snd.app W x).op (yonedaEquiv (a ≫ prod.fst)) =
      F.map (cone.snd.app W x).op (yonedaEquiv (a ≫ prod.snd)) := by
  have h : cone.snd ≫ a ≫ prod.fst = cone.snd ≫ a ≫ prod.snd := by
    calc
      _ = cone.fst := by simpa using (cone.condition =≫ prod.fst).symm
      _ = _ := by simpa using (cone.condition =≫ prod.snd)
  rw [yonedaEquiv_naturality (a ≫ prod.fst) (cone.snd.app W x),
    yonedaEquiv_naturality (a ≫ prod.snd) (cone.snd.app W x)]
  simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map, NatTrans.comp_app,
    types_comp_apply] using congrArg (fun q ↦ q.app W x) h

end CategoryTheory.Limits.PullbackCone
