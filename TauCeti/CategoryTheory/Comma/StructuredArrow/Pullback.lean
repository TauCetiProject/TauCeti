/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Structured arrow categories as pullbacks

Mathlib's `StructuredArrow.proj` and `StructuredArrow.pre` exhibit the category of
arrows into the values of a composite functor as a pullback in `Cat`.

## References

* J. Lurie, *Higher Topos Theory*, Theorem 4.1.3.1, for the simplicial comma construction.
-/

public section

universe u v w

namespace CategoryTheory.StructuredArrow
open Limits

variable {B C : Type (max u v)} {D : Type w} [Category.{v} B] [Category.{v} C] [Category.{v} D]

/-- The structured arrow category of a composite `F ⋙ T` is the strict pullback of
`F` along the projection from the structured arrow category of `T`. -/
theorem isPullback_proj_pre (x : D) (F : B ⥤ C) (T : C ⥤ D) :
    IsPullback (StructuredArrow.proj x (F ⋙ T)).toCatHom
      (StructuredArrow.pre x F T).toCatHom F.toCatHom (StructuredArrow.proj x T).toCatHom := by
  let p := (StructuredArrow.proj x (F ⋙ T)).toCatHom
  let q := (StructuredArrow.pre x F T).toCatHom
  let r := (StructuredArrow.proj x T).toCatHom
  have w : p ≫ F.toCatHom = q ≫ r := rfl
  have comm (s : PullbackCone F.toCatHom r) :
      s.fst.toFunctor ⋙ F = s.snd.toFunctor ⋙ StructuredArrow.proj x T :=
    congrArg Cat.Hom.toFunctor s.condition
  let e (s : PullbackCone F.toCatHom r) i := Functor.congr_obj (comm s) i
  let lift (s : PullbackCone F.toCatHom r) : s.pt ⟶ Cat.of (StructuredArrow x (F ⋙ T)) := by
    refine (s.fst.toFunctor.toStructuredArrow x (F ⋙ T)
      (fun i ↦ (s.snd.toFunctor.obj i).hom ≫ T.map (eqToHom (e s i).symm)) ?_).toCatHom
    intro i j f
    have hm := Functor.congr_hom (comm s) f
    simp only [Functor.comp_map, StructuredArrow.proj_map] at hm
    have he : eqToHom (e s i).symm ≫ F.map (s.fst.toFunctor.map f) =
        (s.snd.toFunctor.map f).right ≫ eqToHom (e s j).symm := by
      simp [hm]
    simp only [Functor.comp_map, Category.assoc, ← T.map_comp, he]
    rw [T.map_comp, StructuredArrow.w_assoc]
  have lift_hom (s : PullbackCone F.toCatHom r) (i : s.pt) :
      ((lift s).toFunctor.obj i).hom =
        (s.snd.toFunctor.obj i).hom ≫ T.map (eqToHom (e s i).symm) := rfl
  refine IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk w lift ?_ ?_ ?_)
  · exact fun _ ↦ rfl
  · intro s
    refine Cat.ext (Functor.ext (fun i ↦ obj_ext _ _ (e s i) ?_) ?_)
    · simp only [Functor.comp_obj, Cat.Hom.comp_toFunctor, q, Functor.toCatHom_toFunctor,
        StructuredArrow.pre_obj_hom, lift_hom]
      -- Make both transport endpoints explicit so the cancellation lemmas match.
      change ((s.snd.toFunctor.obj i).hom ≫ T.map (eqToHom (e s i).symm)) ≫
        T.map (eqToHom (e s i)) = (s.snd.toFunctor.obj i).hom
      simp [← T.map_comp]
    · intro i j f
      apply (StructuredArrow.proj x T).map_injective
      simp only [Functor.map_comp, eqToHom_map]
      exact Functor.congr_hom (comm s) f
  · intro s m hm₁ hm₂
    have h₁ := congrArg Cat.Hom.toFunctor hm₁
    have h₂ := congrArg Cat.Hom.toFunctor hm₂
    refine Cat.ext (Functor.ext (fun i ↦ obj_ext _ _ (Functor.congr_obj h₁ i) ?_) ?_)
    · have hi := StructuredArrow.w (eqToHom (Functor.congr_obj h₂ i))
      refine (congrArg ((m.toFunctor.obj i).hom ≫ ·)
        (congrArg T.map (eqToHom_map F (Functor.congr_obj h₁ i)))).trans ?_
      simpa only [Cat.Hom.comp_toFunctor, Functor.comp_obj, q, Functor.toCatHom_toFunctor,
        StructuredArrow.pre_obj_hom, lift_hom, StructuredArrow.eqToHom_right, ← T.map_comp,
        Category.assoc, eqToHom_trans] using congrArg (fun a ↦ a ≫ T.map (eqToHom (e s i).symm)) hi
    · intro i j f
      apply (StructuredArrow.proj x (F ⋙ T)).map_injective
      simp only [Functor.map_comp, eqToHom_map]
      exact Functor.congr_hom h₁ f

end CategoryTheory.StructuredArrow
