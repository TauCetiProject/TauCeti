/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import TauCeti.CategoryTheory.ComposableArrows.Basic

/-!
# Strings of arrows in an under category

A string of n arrows under x is the same as a string of n + 1 arrows whose first
object is x. The extra first arrow supplies the structure maps of all the under-category
objects, by composition. This correspondence describes the simplices of the nerve of
an under category, including the structure maps that its forgetful functor discards.
-/

public section

open CategoryTheory

universe v u

namespace CategoryTheory.ComposableArrows

variable {C : Type u} [Category.{v} C] (x : C)

/-- Regard a string starting at x as a string of objects under x. -/
-- Its object map determines the endpoint types of the structure arrows.
@[expose]
def toUnder {n : ℕ}
    (t : {t : ComposableArrows C (n + 1) // t.obj 0 = x}) :
    ComposableArrows (Under x) n :=
  Under.lift (Fin.succFunctor (n + 1) ⋙ t.1)
    { app i := eqToHom t.2.symm ≫ t.1.map (homOfLE (Fin.zero_le i.succ))
      naturality i j f := by
        dsimp
        rw [Category.id_comp, Category.assoc, ← t.1.map_comp]
        congr 2 }

/-- Prepending the first structure arrow recovers the original string. -/
@[simp]
lemma precomp_toUnder {n : ℕ}
    (t : {t : ComposableArrows C (n + 1) // t.obj 0 = x}) :
    ComposableArrows.precomp (toUnder x t ⋙ Under.forget x)
      ((toUnder x t).obj 0).hom = t.1 := by
  obtain ⟨t, rfl⟩ := t
  apply ComposableArrows.ext_succ_of_totalArrow
  · rfl
  · rw [totalArrow_def, totalArrow_def]
    -- The lifted first arrow is the original first arrow, preceded by an identity.
    change (⟨t.obj 0, t.obj 1, 𝟙 _ ≫ t.map (homOfLE (Fin.zero_le 1))⟩ : Quiver.Total C) =
      ⟨t.obj 0, t.obj 1, t.map (homOfLE (Fin.zero_le 1))⟩
    simp

/-- Removing the prepended structure arrow recovers an under-category string. -/
@[simp]
lemma toUnder_precomp {n : ℕ} (s : ComposableArrows (Under x) n) :
    toUnder x ⟨ComposableArrows.precomp (s ⋙ Under.forget x) (s.obj 0).hom, rfl⟩ = s := by
  have ho (i : Fin (n + 1)) :
      (toUnder x ⟨ComposableArrows.precomp (s ⋙ Under.forget x) (s.obj 0).hom, rfl⟩).obj i =
        s.obj i := by
    refine StructuredArrow.obj_ext _ _ (by rfl) ?_
    -- The arrow to vertex i is the prepended arrow composed with the old arrow to i.
    have h := totalArrow_precomp_zero_succ (s ⋙ Under.forget x) (s.obj 0).hom i
    rw [totalArrow_def] at h
    have hh := (eq_of_heq (Quiver.Total.mk.inj h).2.2).trans
      (Under.w (s.map (homOfLE (Fin.zero_le i))))
    -- Unfolding the lift only exposes identities around this arrow.
    change (𝟙 x ≫ (ComposableArrows.precomp (s ⋙ Under.forget x) (s.obj 0).hom).map
      (homOfLE (Fin.zero_le i.succ))) ≫ 𝟙 _ = (s.obj i).hom
    erw [Category.comp_id, Category.id_comp]
    exact hh
  refine Functor.ext ho ?_
  intro i j f
  apply Under.UnderMorphism.ext
  have hmap : ((toUnder x ⟨ComposableArrows.precomp (s ⋙ Under.forget x)
      (s.obj 0).hom, rfl⟩).map f).right = (s.map f).right := rfl
  erw [hmap, Under.comp_right, Under.comp_right,
    Under.eqToHom_right, Under.eqToHom_right]
  have hi : eqToHom (congrArg Under.right (ho i)) = 𝟙 (s.obj i).right := by rfl
  have hj : eqToHom (congrArg Under.right (ho j).symm) = 𝟙 (s.obj j).right := by rfl
  erw [hi, hj, Category.id_comp, Category.comp_id]

/-- Strings of n arrows under x correspond to strings of n + 1 arrows starting at x. -/
-- The object map must reduce so the structure arrows and right parts have their stated types.
@[expose]
def underEquiv (n : ℕ) :
    {t : ComposableArrows C (n + 1) // t.obj 0 = x} ≃ ComposableArrows (Under x) n where
  toFun := toUnder x
  invFun s := ⟨ComposableArrows.precomp (s ⋙ Under.forget x) (s.obj 0).hom, rfl⟩
  left_inv t := Subtype.ext (precomp_toUnder x t)
  right_inv := toUnder_precomp x

/-- The inverse correspondence prepends the structure arrow of the first object. -/
@[simp]
lemma underEquiv_symm_val {n : ℕ} (s : ComposableArrows (Under x) n) :
    ((underEquiv x n).symm s).1 =
      ComposableArrows.precomp (s ⋙ Under.forget x) (s.obj 0).hom := (rfl)

/-- The underlying objects are the old objects after the initial vertex. -/
@[simp]
lemma underEquiv_obj_right {n : ℕ}
    (t : {t : ComposableArrows C (n + 1) // t.obj 0 = x}) (i : Fin (n + 1)) :
    ((underEquiv x n t).obj i).right = t.1.obj i.succ := (rfl)

/-- The structure arrow to an old vertex is its arrow from the initial vertex. -/
@[simp]
lemma underEquiv_obj_hom {n : ℕ}
    (t : {t : ComposableArrows C (n + 1) // t.obj 0 = x}) (i : Fin (n + 1)) :
    ((underEquiv x n t).obj i).hom =
      eqToHom t.2.symm ≫ t.1.map (homOfLE (Fin.zero_le i.succ)) := (rfl)

/-- The underlying morphisms are those between the old vertices. -/
@[simp]
lemma underEquiv_map_right {n : ℕ}
    (t : {t : ComposableArrows C (n + 1) // t.obj 0 = x})
    {i j : Fin (n + 1)} (f : i ⟶ j) :
    ((underEquiv x n t).map f).right = t.1.map ((Fin.succFunctor (n + 1)).map f) := (rfl)

end CategoryTheory.ComposableArrows
