/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import TauCeti.Combinatorics.Quiver.Prefunctor

/-!
# Arrows of composable strings, and isomorphism classes of their vertices

For positions `i ≤ j` of a string `F : ComposableArrows C n` of composable arrows, its arrow from
the `i`-th to the `j`-th object, viewed as a total arrow of `C`, is `F.totalArrow i j hij`. The
string is determined by these arrows (`CategoryTheory.ComposableArrows.ext_of_totalArrow`);
reindexing the string along a functor of the indexing posets reindexes its arrows
(`CategoryTheory.ComposableArrows.totalArrow_whiskerLeft`), prepending an arrow with
`CategoryTheory.ComposableArrows.precomp` shifts them
(`CategoryTheory.ComposableArrows.totalArrow_precomp_succ_succ`), appending a terminal object with
`CategoryTheory.ComposableArrows.snocTerminal` preserves existing arrows and sends every vertex to
the terminal object (`CategoryTheory.ComposableArrows.totalArrow_snocTerminal_castSucc`,
`CategoryTheory.ComposableArrows.totalArrow_snocTerminal_last`), and applying a functor to the
string maps its arrows along the functor
(`CategoryTheory.ComposableArrows.totalArrow_mapComposableArrows_obj`) and commutes with
prepending (`CategoryTheory.Functor.mapComposableArrows_obj_precomp`). A string of at least one
arrow is already determined by its first arrow and the remaining string
(`CategoryTheory.ComposableArrows.ext_succ_of_totalArrow`).

All vertices of a composable string in a groupoid have the same isomorphism class.

## Main declarations

* `CategoryTheory.ComposableArrows.totalArrow`: the arrow of a string between two positions.
* `CategoryTheory.ComposableArrows.snocTerminal`: append a terminal object to a string.
* `CategoryTheory.ComposableArrows.ext_of_totalArrow`: a string is determined by its arrows.
* `CategoryTheory.ComposableArrows.ext_succ_of_totalArrow`: a string is determined by its first
  arrow and its remaining arrows.
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

/-- An arrow from the new first vertex of a prepended string to a shifted vertex is the prepended
arrow followed by an arrow of the original string. Unlike
`CategoryTheory.ComposableArrows.totalArrow_precomp_zero_succ_succ`, this holds uniformly in the
target position, including the first arrow. -/
theorem totalArrow_precomp_zero_succ (F : ComposableArrows C n) {X : C} (f : X ⟶ F.left)
    (j : Fin (n + 1)) :
    (F.precomp f).totalArrow 0 j.succ (Fin.zero_le _) =
      ⟨X, F.obj j, f ≫ F.map (homOfLE (Fin.zero_le j))⟩ := by
  obtain ⟨_ | j, hj⟩ := j
  · -- The first arrow is `f` itself, followed by the identity of the old first vertex: `0` and
    -- `⟨0, hj⟩` are the same element of `Fin (n + 1)`, so `homOfLE` is its identity arrow.
    exact congrArg (fun g ↦ (⟨X, F.obj ⟨0, hj⟩, g⟩ : Quiver.Total C))
      ((Category.comp_id f).symm.trans (by rw [← F.map_id]; rfl))
  · rfl

/-- The morphism from the new first vertex of a prepended string to a shifted vertex is the
prepended arrow followed by a morphism of the original string. -/
theorem precomp_map_zero_succ (F : ComposableArrows C n) {X : C} (f : X ⟶ F.left)
    (j : Fin (n + 1)) :
    (F.precomp f).map (homOfLE (Fin.zero_le j.succ)) = f ≫ F.map (homOfLE (Fin.zero_le j)) :=
  eq_of_heq (Quiver.Total.mk.inj (totalArrow_precomp_zero_succ F f j)).2.2

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

/-- A string of at least one composable arrow is determined by its first arrow and the string
`F.δ₀` of the remaining arrows. -/
theorem ext_succ_of_totalArrow {F G : ComposableArrows C (n + 1)} (h : F.δ₀ = G.δ₀)
    (w : F.totalArrow 0 1 (Fin.zero_le _) = G.totalArrow 0 1 (Fin.zero_le _)) : F = G := by
  obtain ⟨h₀, h₁, hw⟩ := Quiver.Total.mk.inj w
  exact ext_succ h₀ h ((conj_eqToHom_iff_heq _ _ h₀ h₁).2 hw)

/-- Applying a functor to a string with a prepended arrow prepends the image of that arrow to the
image of the string. -/
@[simp]
theorem _root_.CategoryTheory.Functor.mapComposableArrows_obj_precomp {D : Type*} [Category D]
    (Φ : C ⥤ D) (F : ComposableArrows C n) {X : C} (f : X ⟶ F.left) :
    (Φ.mapComposableArrows (n + 1)).obj (F.precomp f) =
      ((Φ.mapComposableArrows n).obj F).precomp (Φ.map f) := by
  refine ext_succ_of_totalArrow rfl ?_
  rw [totalArrow_mapComposableArrows_obj, totalArrow_def, totalArrow_def]
  -- By definition of `precomp`, both first arrows are `Φ.map f`.
  rfl

section SnocTerminal

open Category Limits

private def snocTerminalObj (σ : ComposableArrows C n) (t : C) (i : Fin (n + 2)) : C :=
  if hi : i.val < n + 1 then σ.obj ⟨i.val, hi⟩ else t

private lemma snocTerminalObj_pos (σ : ComposableArrows C n) (t : C) {i : Fin (n + 2)}
    (hi : i.val < n + 1) : snocTerminalObj σ t i = σ.obj ⟨i.val, hi⟩ := dite_eq_left hi

private lemma snocTerminalObj_neg (σ : ComposableArrows C n) (t : C) {i : Fin (n + 2)}
    (hi : ¬ i.val < n + 1) : snocTerminalObj σ t i = t := dite_eq_right hi

/-- Append a terminal object `t` of `C` at the end of `σ : ComposableArrows C n`. -/
def snocTerminal (σ : ComposableArrows C n) {t : C} (ht : IsTerminal t) :
    ComposableArrows C (n + 1) where
  obj := snocTerminalObj σ t
  map {i j} f :=
    if hj : j.val < n + 1 then
      have hi : i.val < n + 1 := Nat.lt_of_le_of_lt f.le hj
      eqToHom (snocTerminalObj_pos σ t hi) ≫
        σ.map (homOfLE (show (⟨i.val, hi⟩ : Fin (n + 1)) ≤ ⟨j.val, hj⟩ from f.le)) ≫
          eqToHom (snocTerminalObj_pos σ t hj).symm
    else ht.from (snocTerminalObj σ t i) ≫ eqToHom (snocTerminalObj_neg σ t hj).symm
  map_id i := by
    by_cases hi : i.val < n + 1
    · rw [dite_eq_left hi]; simp
    · rw [dite_eq_right hi, ← cancel_mono (eqToHom (snocTerminalObj_neg σ t hi)),
        assoc, eqToHom_trans, eqToHom_refl, comp_id]
      exact ht.hom_ext _ _
  map_comp {i j k} f g := by
    by_cases hk : k.val < n + 1
    · have hj : j.val < n + 1 := Nat.lt_of_le_of_lt g.le hk
      have hi : i.val < n + 1 := Nat.lt_of_le_of_lt f.le hj
      rw [dite_eq_left hk, dite_eq_left hj, dite_eq_left hk]
      simp only [assoc, eqToHom_trans_assoc, eqToHom_refl, id_comp, ← σ.map_comp_assoc]
      exact congrArg (fun u ↦ eqToHom (snocTerminalObj_pos σ t hi) ≫ σ.map u ≫
        eqToHom (snocTerminalObj_pos σ t hk).symm) (Subsingleton.elim _ _)
    · rw [dite_eq_right hk, ← cancel_mono (eqToHom (snocTerminalObj_neg σ t hk))]
      exact ht.hom_ext _ _

/-- On `castSucc j`, `σ.snocTerminal ht` retains the `j`-th vertex of `σ`. -/
@[simp]
theorem snocTerminal_obj_castSucc (σ : ComposableArrows C n) {t : C} (ht : IsTerminal t)
    (j : Fin (n + 1)) : (σ.snocTerminal ht).obj j.castSucc = σ.obj j :=
  snocTerminalObj_pos σ t j.isLt

/-- Appending a terminal object preserves the initial vertex `0`. -/
@[simp]
theorem snocTerminal_obj_zero (σ : ComposableArrows C n) {t : C} (ht : IsTerminal t) :
    (σ.snocTerminal ht).obj 0 = σ.obj 0 := by
  rw [← Fin.castSucc_zero]; exact σ.snocTerminal_obj_castSucc ht 0

/-- The final vertex of `σ.snocTerminal ht` is the terminal object `t`. -/
@[simp]
theorem snocTerminal_obj_last (σ : ComposableArrows C n) {t : C} (ht : IsTerminal t) :
    (σ.snocTerminal ht).obj (Fin.last (n + 1)) = t :=
  snocTerminalObj_neg σ t (Nat.lt_irrefl (n + 1))

/-- Arrows between `castSucc` positions of `σ.snocTerminal ht` are the arrows of `σ`. -/
@[simp]
theorem totalArrow_snocTerminal_castSucc (σ : ComposableArrows C n) {t : C}
    (ht : IsTerminal t) (i j : Fin (n + 1)) (hij : i ≤ j) :
    (σ.snocTerminal ht).totalArrow i.castSucc j.castSucc (Fin.castSucc_le_castSucc_iff.mpr hij) =
      σ.totalArrow i j hij := by
  rw [totalArrow_def, totalArrow_def]
  refine Quiver.Total.ext (σ.snocTerminal_obj_castSucc ht i) (σ.snocTerminal_obj_castSucc ht j)
    ((conj_eqToHom_iff_heq _ _ (σ.snocTerminal_obj_castSucc ht i)
      (σ.snocTerminal_obj_castSucc ht j)).mp ?_)
  dsimp [snocTerminal]; rw [dite_eq_left j.isLt]

/-- The arrow of `σ.snocTerminal ht` from any position to the last vertex is `ht.from _`. -/
@[simp]
theorem totalArrow_snocTerminal_last (σ : ComposableArrows C n) {t : C}
    (ht : IsTerminal t) (i : Fin (n + 2)) :
    (σ.snocTerminal ht).totalArrow i (Fin.last (n + 1)) (Fin.le_last i) =
      ⟨(σ.snocTerminal ht).obj i, t, ht.from ((σ.snocTerminal ht).obj i)⟩ := by
  rw [totalArrow_def]
  refine Quiver.Total.ext rfl (σ.snocTerminal_obj_last ht)
    ((conj_eqToHom_iff_heq _ _ rfl (σ.snocTerminal_obj_last ht)).mp ?_)
  rw [eqToHom_refl, id_comp, ← cancel_mono (eqToHom (σ.snocTerminal_obj_last ht))]
  exact ht.hom_ext _ _

/-- Appending `t` to the `0`-simplex at `X` yields the `1`-simplex of `ht.from X : X ⟶ t`. -/
@[simp]
theorem mk₀_snocTerminal (X : C) {t : C} (ht : IsTerminal t) :
    (mk₀ X).snocTerminal ht = mk₁ (ht.from X) :=
  ext₁ ((mk₀ X).snocTerminal_obj_zero ht) ((mk₀ X).snocTerminal_obj_last ht) (by
    rw [← cancel_mono (eqToHom ((mk₀ X).snocTerminal_obj_last ht))]; exact ht.hom_ext _ _)

end SnocTerminal

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
