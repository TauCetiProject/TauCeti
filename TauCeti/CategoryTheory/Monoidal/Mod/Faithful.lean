/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import TauCeti.CategoryTheory.Monoidal.Mod.Basic

/-!
# Actions of monoid objects along faithful monoidal functors

Let `F : C ⥤ D` be a faithful monoidal functor, `M` a monoid object of `C` and `X : C`. A
monoidal functor carries an action of `M` on `X` to an action of `F.obj M` on `F.obj X`
(`CategoryTheory.Functor.modObjObj`). Conversely, an action of `F.obj M` on `F.obj X` comes from an
action of `M` on `X` as soon as its action morphism is the image under `F` of a morphism
`M ⊗ X ⟶ X`: the action axioms hold on `X` because they hold after applying `F`. Faithfulness
also makes the action on `X` unique, and it reflects equivariant morphisms. Between cartesian
monoidal categories, a monoidal functor which reflects isomorphisms also reflects the
pseudo-torsor condition that `(m, x) ↦ (m • x, x)` is an isomorphism.

This is the formal part of descent of group actions: for a base change functor along a morphism of
effective descent, the morphism-descent theorem supplies the required action morphism. The
construction parallels `CategoryTheory.Functor.monObjOfFaithful` for monoid objects.

## Main declarations

* `CategoryTheory.Functor.modObjOfFaithful`: the action of `M` on `X` whose action morphism is a
  given lift of that of `F.obj M` on `F.obj X`.
* `CategoryTheory.Functor.modObjObj_modObjOfFaithful`: its image under `F` is the given action.
* `CategoryTheory.Functor.modObjObj_injective`: a faithful monoidal functor is injective on
  actions.
* `CategoryTheory.Functor.isModHom_map_iff`: a faithful monoidal functor reflects equivariant
  morphisms.
* `CategoryTheory.Functor.isIso_lift_smul_snd_modObjObj_iff`: a monoidal functor which reflects
  isomorphisms reflects the pseudo-torsor condition.
-/

public section

namespace CategoryTheory.Functor

open MonoidalCategory MonObj OplaxMonoidal LaxMonoidal
open scoped Obj

section Faithful

variable {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] [F.Faithful] (M : C) [MonObj M]

/-- Pull back an action of `F.obj M` on `F.obj X` along a faithful monoidal functor `F`, given a
lift `smul : M ⊗ X ⟶ X` of its action morphism. -/
@[simps]
abbrev modObjOfFaithful (X : C) [ModObj (F.obj M) (F.obj X)] (smul : M ⊗ X ⟶ X)
    (h_smul : F.map smul = δ F M X ≫ γ[F.obj M,F.obj X]) : ModObj M X where
  smul := smul
  one_smul := F.map_injective <| by
    have h_one : F.map η[M] = OplaxMonoidal.η F ≫ η[F.obj M] := by
      rw [obj.η_def, Monoidal.η_ε_assoc]
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionUnitIso, F.map_comp, h_smul,
      ← δ_natural_left_assoc]
    rw [h_one, comp_whiskerRight_assoc, ModObj.one_smul_self, Monoidal.map_leftUnitor]
  mul_smul := F.map_injective <| by
    have h_mul : F.map μ[M] = δ F M M ≫ μ[F.obj M] := by
      rw [obj.μ_def, Monoidal.δ_μ_assoc]
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionHomRight,
      selfLeftAction_actionAssocIso, selfLeftAction_actionObj, F.map_comp, h_smul,
      ← δ_natural_left_assoc, ← δ_natural_right_assoc]
    rw [h_mul, comp_whiskerRight_assoc, ModObj.mul_smul_self, Monoidal.map_associator_assoc]
    simp

/-- The image under `F` of the action `F.modObjOfFaithful M X smul _` is the action of `F.obj M`
on `F.obj X` it was built from. -/
theorem modObjObj_modObjOfFaithful (X : C) [ModObj (F.obj M) (F.obj X)] (smul : M ⊗ X ⟶ X)
    (h_smul : F.map smul = δ F M X ≫ γ[F.obj M,F.obj X]) :
    letI := F.modObjOfFaithful M X smul h_smul
    F.modObjObj M X = ‹ModObj (F.obj M) (F.obj X)› :=
  ModObj.ext _ _ (by simp [h_smul])

/-- A faithful monoidal functor is injective on actions of a monoid object. -/
theorem modObjObj_injective (X : C) :
    Function.Injective fun _ : ModObj M X ↦ F.modObjObj M X := by
  intro h₁ h₂ e
  refine ModObj.ext _ _ (F.map_injective ?_)
  have := congr(($e).smul)
  simpa [← cancel_epi (LaxMonoidal.μ F M X)] using this

/-- A faithful monoidal functor reflects equivariant morphisms. -/
theorem isModHom_map_iff {X Y : C} [ModObj M X] [ModObj M Y] (f : X ⟶ Y) :
    letI := F.modObjObj M X
    letI := F.modObjObj M Y
    IsModHom (F.obj M) (F.map f) ↔ IsModHom M f := by
  let := F.modObjObj M X
  let := F.modObjObj M Y
  refine ⟨fun h ↦ ⟨F.map_injective ?_⟩, fun _ ↦ F.modObjObj_isModHom M f⟩
  have := h.smul_hom
  simp only [modObjObj_smul, selfLeftAction_actionHomRight, Category.assoc,
    μ_natural_right_assoc, ← F.map_comp] at this
  simpa [← cancel_epi (LaxMonoidal.μ F M X)] using this

end Faithful

section Cartesian

open CartesianMonoidalCategory

variable {C D : Type*} [Category C] [Category D] [CartesianMonoidalCategory C]
  [CartesianMonoidalCategory D] (F : C ⥤ D) [F.Monoidal] (M X : C) [MonObj M] [ModObj M X]

/-- The image under a monoidal functor `F` of the morphism `M ⊗ X ⟶ X ⊗ X`, `(m, x) ↦ (m • x, x)`,
of an action is the corresponding morphism of the transported action, up to the tensorators. -/
theorem map_lift_smul_snd :
    letI := F.modObjObj M X
    F.map (lift γ[M,X] (snd M X)) =
      δ F M X ≫ lift γ[F.obj M,F.obj X] (snd (F.obj M) (F.obj X)) ≫ LaxMonoidal.μ F X X := by
  rw [← Monoidal.lift_μ, comp_lift_assoc]
  simp

/-- **Pseudo-torsors along a conservative monoidal functor.** For a monoidal functor `F` which
reflects isomorphisms, the morphism `(m, x) ↦ (m • x, x)` of an action of `M` on `X` is an
isomorphism if and only if that of the transported action of `F.obj M` on `F.obj X` is. -/
theorem isIso_lift_smul_snd_modObjObj_iff [F.ReflectsIsomorphisms] :
    letI := F.modObjObj M X
    IsIso (lift γ[F.obj M,F.obj X] (snd (F.obj M) (F.obj X))) ↔ IsIso (lift γ[M,X] (snd M X)) := by
  let := F.modObjObj M X
  rw [← isIso_iff_of_reflects_iso _ F, map_lift_smul_snd, isIso_comp_left_iff,
    isIso_comp_right_iff]

end Cartesian

end CategoryTheory.Functor
