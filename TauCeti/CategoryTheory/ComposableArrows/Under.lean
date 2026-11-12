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

/-- Strings of n arrows under x correspond to strings of n + 1 arrows starting at x. -/
-- The object map must reduce so the structure arrows and right parts have their stated types.
@[expose]
def underEquiv (n : ℕ) :
    {t : ComposableArrows C (n + 1) // t.obj 0 = x} ≃ ComposableArrows (Under x) n where
  toFun t := Under.lift (Fin.succFunctor (n + 1) ⋙ t.1)
    { app i := eqToHom t.2.symm ≫ t.1.map (homOfLE (Fin.zero_le i.succ))
      naturality i j f := by
        dsimp
        rw [Category.id_comp, Category.assoc, ← t.1.map_comp]
        congr 2 }
  invFun s := ⟨ComposableArrows.precomp (s ⋙ Under.forget x) (s.obj 0).hom, rfl⟩
  left_inv := by
    rintro ⟨t, rfl⟩
    refine Subtype.ext (ext_succ_of_totalArrow rfl ?_)
    rw [totalArrow_def, totalArrow_def]
    -- The lifted first arrow is the original first arrow, preceded by an identity.
    exact congrArg (fun g ↦ (⟨t.obj 0, t.obj 1, g⟩ : Quiver.Total C)) (Category.id_comp _)
  right_inv s := by
    -- Lifting the structure arrows of s recovers s: `Under.lift (s ⋙ Under.forget x) α` is
    -- definitionally s, by eta for functors and for objects and morphisms of `Under x` (Mathlib
    -- has no eta lemma for `Under.lift`), which the final `rfl` uses.
    let α : (Functor.const _).obj x ⟶ s ⋙ Under.forget x :=
      { app i := (s.obj i).hom
        naturality i j f := by simp }
    refine (congrArg (Under.lift (s ⋙ Under.forget x))
      (NatTrans.ext (funext fun i ↦ ?_) : _ = α)).trans rfl
    -- The structure arrow to vertex i is the first structure arrow followed by the arrow to i.
    exact (Category.id_comp _).trans ((precomp_map_zero_succ _ _ i).trans
      (Under.w (s.map (homOfLE (Fin.zero_le i)))))

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
