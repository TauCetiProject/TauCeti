/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Condensed.Discrete.Module

/-!
# Sections of locally constant light condensed modules

The section comparison identifies the section module of the locally constant realization
with locally constant functions. Restriction is precomposition and coefficient maps act pointwise.
-/

public section

open CategoryTheory Opposite

universe u

namespace LightCondMod.LocallyConstant

variable {R : Type u} [Ring R] (M : ModuleCat.{u} R)

/-- Sections of the locally constant realization, presented as locally constant functions. -/
def sectionsEquiv (S : LightProfinite.{u}) :
    ((functor R).obj M).obj.obj (op S) ≃ₗ[R] LocallyConstant S M :=
  LinearEquiv.refl R _

/-- Restricting a locally constant section evaluates by precomposition. -/
@[simp]
lemma sectionsEquiv_map_apply {S T : LightProfinite.{u}} (f : S ⟶ T)
    (s : ((functor R).obj M).obj.obj (op T)) (x : S) :
    sectionsEquiv M S (((functor R).obj M).obj.map f.op s) x =
      sectionsEquiv M T s (f x) := by
  exact CompHausLike.LocallyConstantModule.functor_obj_obj_map_hom_apply_apply R
    (fun _ _ f ↦ (LightProfinite.effectiveEpi_iff_surjective f).mp) M f.op s x

/-- A coefficient-module map acts pointwise under the section comparison. -/
@[simp]
lemma sectionsEquiv_map_app_apply {N : ModuleCat.{u} R} (f : M ⟶ N)
    (S : LightProfinite.{u}) (s : ((functor R).obj M).obj.obj (op S)) (x : S) :
    sectionsEquiv N S (((functor R).map f).hom.app (op S) s) x =
      f (sectionsEquiv M S s x) := by
  exact CompHausLike.LocallyConstantModule.functor_map_hom_app_hom_apply_apply R
    (fun _ _ f ↦ (LightProfinite.effectiveEpi_iff_surjective f).mp) f (op S) s x

end LightCondMod.LocallyConstant
