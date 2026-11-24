/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Condensed.Light.Module

/-!
# Sections of light condensed modules

Evaluation of morphisms on sections preserves subtraction over any coefficient ring.
-/

public section

universe u

open CategoryTheory

namespace LightCondMod

/-- Evaluating a difference of light condensed module maps subtracts their evaluations. -/
@[simp]
lemma hom_app_sub_apply {R : Type u} [Ring R] {M N : LightCondMod R} (f g : M ⟶ N)
    (S : LightProfinite.{u}) (s : M.obj.obj (Opposite.op S)) :
    (f - g).hom.app (Opposite.op S) s =
      f.hom.app (Opposite.op S) s - g.hom.app (Opposite.op S) s := by
  have h := (sheafToPresheaf (coherentTopology LightProfinite.{u}) (ModuleCat R) ⋙
    (evaluation _ _).obj (Opposite.op S)).map_sub (f := f) (g := g)
  simpa only [Functor.comp_map, evaluation_obj_map, ObjectProperty.ι_map,
    ModuleCat.hom_sub, LinearMap.sub_apply] using congrArg (fun h => h.hom s) h

end LightCondMod
