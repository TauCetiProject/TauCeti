/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Comparing pushout functor maps with chosen pushouts

The map induced by `Under.pushout` agrees with a given map between any chosen pushout
presentations when it agrees on both injections.
-/

public section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory.Under

variable {C : Type u} [Category.{v} C]

/-- A map between chosen pushouts represents the corresponding `Under.pushout` map if
it commutes with both injections. Only pushouts along the base arrow `a` are required. -/
theorem pushout_map_right_isoPushout_inv {E F X Y X' Y' : C}
    {a : E ⟶ F} [HasPushoutsAlong a] {x : E ⟶ X} {y : E ⟶ Y}
    (u : Under.mk x ⟶ Under.mk y)
    {xx : X ⟶ X'} {yy : Y ⟶ Y'} {x' : F ⟶ X'} {y' : F ⟶ Y'}
    (hx : IsPushout x a xx x') (hy : IsPushout y a yy y') (v : X' ⟶ Y')
    (hv : xx ≫ v = u.right ≫ yy) (hbase : x' ≫ v = y') :
    ((Under.pushout a).map u).right ≫ hy.isoPushout.inv = hx.isoPushout.inv ≫ v := by
  -- Fix the pushout carriers when extracting the public map equation, so the
  -- injection equations below do not need to reduce the under-category objects.
  have hu : x ≫ u.right = y := Under.w u
  have hmap :
      (show Limits.pushout x a ⟶ Limits.pushout y a from ((Under.pushout a).map u).right) =
      pushout.desc (f := x) (g := a) (u.right ≫ pushout.inl y a) (pushout.inr y a)
        (by rw [← Category.assoc, hu, pushout.condition]) :=
    congrArg Under.Hom.right (pushout_map a (Under.mk x) (u := u))
  refine (congrArg (fun m : Limits.pushout x a ⟶ Limits.pushout y a =>
    m ≫ hy.isoPushout.inv) hmap).trans ?_
  apply pushout.hom_ext (f := x) (g := a)
  · simp only [Category.assoc, pushout.inl_desc_assoc,
      hy.inl_isoPushout_inv, hx.inl_isoPushout_inv_assoc]
    exact hv.symm
  · simp only [pushout.inr_desc_assoc, hy.inr_isoPushout_inv,
      hx.inr_isoPushout_inv_assoc]
    exact hbase.symm

end CategoryTheory.Under
