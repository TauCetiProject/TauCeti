/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import TauCeti.Combinatorics.Quiver.Prefunctor

/-!
# Arrows of composable strings, and isomorphism classes of their vertices

For positions `i ≤ j` of a string `F : ComposableArrows C n` of composable arrows, its arrow from
the `i`-th to the `j`-th object, viewed as a total arrow of `C`, is `F.totalArrow i j hij`. The
string is determined by these arrows (`CategoryTheory.ComposableArrows.ext_of_totalArrow`);
reindexing the string along a functor of the indexing posets reindexes its arrows
(`CategoryTheory.ComposableArrows.totalArrow_whiskerLeft`), prepending an arrow with
`CategoryTheory.ComposableArrows.precomp` shifts them
(`CategoryTheory.ComposableArrows.totalArrow_precomp_succ_succ`), and applying a functor to the
string maps its arrows along the functor
(`CategoryTheory.ComposableArrows.totalArrow_mapComposableArrows_obj`).

All vertices of a composable string in a groupoid have the same isomorphism class.

## Main declarations

* `CategoryTheory.ComposableArrows.totalArrow`: the arrow of a string between two positions.
* `CategoryTheory.ComposableArrows.ext_of_totalArrow`: a string is determined by its arrows.
* `CategoryTheory.ComposableArrows.quotient_mk_obj`: the vertices of a string in a groupoid are
  isomorphic.
-/

public noncomputable section

universe v u

namespace CategoryTheory.ComposableArrows

variable {C : Type u} [Category.{v} C] {n : ℕ}

/-- The arrow of a string of composable arrows from its `i`-th to its `j`-th object, as a total
arrow of `C`. For `i = j` this is the identity arrow of the `i`-th object. -/
def totalArrow (F : ComposableArrows C n) (i j : Fin (n + 1)) (hij : i ≤ j) : Quiver.Total C :=
  ⟨F.obj i, F.obj j, F.map (homOfLE hij)⟩

@[simp]
theorem totalArrow_left (F : ComposableArrows C n) (i j : Fin (n + 1)) (hij : i ≤ j) :
    (F.totalArrow i j hij).left = F.obj i := (rfl)

@[simp]
theorem totalArrow_right (F : ComposableArrows C n) (i j : Fin (n + 1)) (hij : i ≤ j) :
    (F.totalArrow i j hij).right = F.obj j := (rfl)

theorem totalArrow_def (F : ComposableArrows C n) (i j : Fin (n + 1)) (hij : i ≤ j) :
    F.totalArrow i j hij = ⟨F.obj i, F.obj j, F.map (homOfLE hij)⟩ := (rfl)

/-- The arrow of a string of composable arrows from a position to itself is an identity arrow. -/
@[simp]
theorem totalArrow_self (F : ComposableArrows C n) (i : Fin (n + 1)) :
    F.totalArrow i i le_rfl = ⟨F.obj i, F.obj i, 𝟙 (F.obj i)⟩ := by
  simp [totalArrow_def]

/-- The first arrow of a string obtained by prepending an arrow is that arrow, including
when its target is identified with the first vertex by an equality. -/
@[simp]
theorem totalArrow_precomp_zero_one {n : ℕ} (a : Quiver.Total C)
    (F : ComposableArrows C n) (h : a.right = F.left) :
    (F.precomp (a.hom ≫ eqToHom h)).totalArrow 0 1 (Fin.zero_le _) = a := by
  rcases a with ⟨x, z, f⟩
  dsimp only at h
  subst z
  rw [totalArrow_def]
  simp only [precomp, Precomp.obj_zero, Precomp.obj_one, Precomp.map_zero_one,
    eqToHom_refl, Category.comp_id]

/-- An arrow from the new first vertex to a later vertex is the prepended arrow followed by
an arrow of the original string. -/
@[simp]
theorem totalArrow_precomp_zero_succ_succ (F : ComposableArrows C n) {X : C}
    (f : X ⟶ F.left) (j : ℕ) (hj : j + 2 < n + 1 + 1) :
    (F.precomp f).totalArrow 0 ⟨j + 2, hj⟩ (Nat.zero_le _) =
      ⟨X, F.obj' (j + 1) (by omega), f ≫ F.map' 0 (j + 1) (by omega) (by omega)⟩ := by
  -- At these indices precomp inserts f before the original arrow from vertex 0 to j + 1.
  rfl

/-- Arrows between shifted vertices of a prepended string are the arrows of the original
string. -/
@[simp]
theorem totalArrow_precomp_succ_succ (F : ComposableArrows C n) {X : C}
    (f : X ⟶ F.left) (i j : Fin (n + 1)) (hij : i ≤ j) :
    (F.precomp f).totalArrow i.succ j.succ (Fin.succ_le_succ_iff.mpr hij) =
      F.totalArrow i j hij := by
  -- Both endpoints lie in the shifted tail, where precomp retains the original map.
  rfl

/-- Reindexing a string of composable arrows along a functor `Φ` of the indexing posets reindexes
its arrows. -/
@[simp]
theorem totalArrow_whiskerLeft {m : ℕ} (F : ComposableArrows C m)
    (Φ : Fin (n + 1) ⥤ Fin (m + 1)) (i j : Fin (n + 1)) (hij : i ≤ j) :
    (F.whiskerLeft Φ).totalArrow i j hij = F.totalArrow (Φ.obj i) (Φ.obj j) (Φ.monotone hij) := by
  -- Morphisms in the poset `Fin (m + 1)` are unique, so `Φ` sends `homOfLE hij` to `homOfLE _`.
  have h : Φ.map (homOfLE hij) = homOfLE (Φ.monotone hij) := Subsingleton.elim _ _
  simp only [totalArrow, whiskerLeft, Functor.comp_obj, Functor.comp_map, h]

/-- An arrow of the image of a string under a functor is the image of the arrow of the string. -/
@[simp]
theorem totalArrow_mapComposableArrows_obj {D : Type*} [Category D] (Φ : C ⥤ D)
    (F : ComposableArrows C n) (i j : Fin (n + 1)) (hij : i ≤ j) :
    ((Φ.mapComposableArrows n).obj F).totalArrow i j hij =
      Φ.toPrefunctor.mapTotal (F.totalArrow i j hij) := by
  rw [totalArrow_def, totalArrow_def]
  rfl

/-- A string of composable arrows is determined by its arrows. -/
theorem ext_of_totalArrow {F G : ComposableArrows C n}
    (h : ∀ i j (hij : i ≤ j), F.totalArrow i j hij = G.totalArrow i j hij) : F = G := by
  refine Functor.hext (fun i ↦ congrArg Quiver.Total.left (h i i le_rfl)) fun i j g ↦ ?_
  -- Morphisms in the poset `Fin (n + 1)` are unique, so `g` is the morphism `homOfLE g.le` that
  -- `totalArrow` uses, and the hypothesis `h i j g.le` applies to it.
  rw [show g = homOfLE g.le from Subsingleton.elim _ _]
  have := h i j g.le
  simp only [totalArrow, Quiver.Total.mk.injEq] at this
  exact this.2.2

end CategoryTheory.ComposableArrows

namespace CategoryTheory.ComposableArrows

variable {C : Type*} [Category C] [IsGroupoid C] {n : ℕ}

/-- All vertices of a composable string in a groupoid represent the same isomorphism class. -/
@[simp]
theorem quotient_mk_obj (F : ComposableArrows C n) (i : Fin (n + 1)) :
    Quotient.mk (isIsomorphicSetoid C) (F.obj i) =
      Quotient.mk (isIsomorphicSetoid C) (F.obj 0) := by
  symm
  exact Quotient.sound (s := isIsomorphicSetoid C)
    ⟨asIso (F.map (homOfLE (Fin.zero_le i)))⟩


omit [IsGroupoid C] in
/-- The composable arrows `mk₁ f` and `mk₁ f'` are equal exactly when `f` and `f'` are equal
as arrows. -/
lemma mk₁_eq_mk₁_iff {X₀ X₁ Y₀ Y₁ : C} {f : X₀ ⟶ X₁} {f' : Y₀ ⟶ Y₁} :
    mk₁ f = mk₁ f' ↔ Arrow.mk f = Arrow.mk f' :=
  arrowEquiv.apply_eq_iff_eq.symm

end CategoryTheory.ComposableArrows
