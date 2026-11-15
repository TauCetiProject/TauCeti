/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.ComposableArrows.Basic

/-!
# Appending an arrow to a string of composable arrows

Dual to Mathlib's `CategoryTheory.ComposableArrows.precomp`, which prepends an arrow to the left
end of a string `F : ComposableArrows C n`, this file defines
`CategoryTheory.ComposableArrows.postcomp`, which appends an arrow `f : F.right ⟶ X` to the right
end of `F` to form a string in `ComposableArrows C (n + 1)`.

Because the object map tests `i.val < n + 1`, the initial vertex `(F.postcomp f).left` is
definitionally equal to `F.left`. Deleting the final vertex recovers `F`
(`CategoryTheory.ComposableArrows.postcomp_δlast`), reindexing along `j.castSucc.succAbove` deletes
the `j`-th vertex of `F` and composes `f` with the trailing arrow from the new last vertex to the
old last vertex (`CategoryTheory.ComposableArrows.whiskerLeft_castSucc_succAbove_postcomp`), and
applying a functor commutes with `postcomp`
(`CategoryTheory.Functor.mapComposableArrows_obj_postcomp`).

## Main declarations

* `CategoryTheory.ComposableArrows.postcomp`: append `f : F.right ⟶ X` to `F`.
* `CategoryTheory.ComposableArrows.totalArrow_postcomp_castSucc_castSucc`,
  `CategoryTheory.ComposableArrows.totalArrow_postcomp_castSucc_last`: the arrows of `F.postcomp f`.
* `CategoryTheory.ComposableArrows.postcomp_δlast`: deleting the last vertex of `F.postcomp f`
  recovers `F`.
* `CategoryTheory.ComposableArrows.whiskerLeft_castSucc_succAbove_postcomp`: deleting an earlier
  vertex of `F.postcomp f` deletes the corresponding vertex of `F` and composes the trailing arrow
  with `f`.
-/

public section

universe v u

namespace CategoryTheory.ComposableArrows

variable {C : Type u} [Category.{v} C] {n : ℕ}

private lemma total_mk_eq {x y x' y' : C} {g : x ⟶ y} {g' : x' ⟶ y'}
    (hx : x = x') (hy : y = y') (hg : g = eqToHom hx ≫ g' ≫ eqToHom hy.symm) :
    (⟨x, y, g⟩ : Quiver.Total C) = ⟨x', y', g'⟩ := by
  subst hx hy
  simpa using hg

private lemma total_id_eq {x y : C} (h : x = y) :
    (⟨x, x, 𝟙 x⟩ : Quiver.Total C) = ⟨y, y, 𝟙 y⟩ :=
  congrArg (fun z : C ↦ (⟨z, z, 𝟙 z⟩ : Quiver.Total C)) h

namespace Postcomp

variable (F : ComposableArrows C n) (X : C)

/-- Appends `X` at the final position `n + 1` of a string `F : ComposableArrows C n`, keeping the
initial `n + 1` vertices unchanged. -/
@[expose, implicit_reducible]
def obj (i : Fin (n + 2)) : C :=
  if h : i.val < n + 1 then F.obj ⟨i.val, h⟩ else X

lemma obj_of_lt {i : Fin (n + 2)} (h : i.val < n + 1) :
    obj F X i = F.obj ⟨i.val, h⟩ := by
  simp [obj, h]

lemma obj_of_not_lt {i : Fin (n + 2)} (h : ¬ i.val < n + 1) :
    obj F X i = X := by
  simp [obj, h]

@[simp]
lemma obj_zero : obj F X 0 = F.obj 0 := (rfl)

@[simp]
lemma obj_castSucc (i : Fin (n + 1)) : obj F X i.castSucc = F.obj i :=
  obj_of_lt F X i.isLt

@[simp]
lemma obj_last : obj F X (Fin.last (n + 1)) = X :=
  obj_of_not_lt F X (Nat.lt_irrefl (n + 1))

variable {X}

/-- Action on morphisms of `F.postcomp f`: arrows inside `0, …, n` are those of `F`, arrows ending
at `n + 1` compose the trailing arrow of `F` with `f`, and the identity at `n + 1` is `𝟙 X`. -/
@[implicit_reducible]
def map (f : F.right ⟶ X) (i j : Fin (n + 2)) (hij : i ≤ j) :
    obj F X i ⟶ obj F X j :=
  if hj : j.val < n + 1 then
    have hi : i.val < n + 1 := Nat.lt_of_le_of_lt hij hj
    eqToHom (obj_of_lt F X hi) ≫ F.map (homOfLE hij) ≫ eqToHom (obj_of_lt F X hj).symm
  else if hi : i.val < n + 1 then
    eqToHom (obj_of_lt F X hi) ≫ F.map (homOfLE (Nat.le_of_lt_succ hi)) ≫ f ≫
      eqToHom (obj_of_not_lt F X hj).symm
  else
    eqToHom (obj_of_not_lt F X hi) ≫ eqToHom (obj_of_not_lt F X hj).symm

lemma map_id (f : F.right ⟶ X) (i : Fin (n + 2)) : map F f i i le_rfl = 𝟙 _ := by
  by_cases hi : i.val < n + 1 <;> simp [map, hi]

lemma map_comp (f : F.right ⟶ X) {i j k : Fin (n + 2)} (hij : i ≤ j) (hjk : j ≤ k) :
    map F f i k (hij.trans hjk) = map F f i j hij ≫ map F f j k hjk := by
  by_cases hk : k.val < n + 1
  · have hj : j.val < n + 1 := Nat.lt_of_le_of_lt hjk hk
    simp only [map, dite_eq_left_of_eq_true (eq_true hk), dite_eq_left_of_eq_true (eq_true hj),
      Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← F.map_comp_assoc, homOfLE_comp]
  · by_cases hj : j.val < n + 1
    · have hi : i.val < n + 1 := Nat.lt_of_le_of_lt hij hj
      simp only [map, dite_eq_right_of_eq_false (eq_false hk),
        dite_eq_left_of_eq_true (eq_true hj), dite_eq_left_of_eq_true (eq_true hi),
        Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← F.map_comp_assoc, homOfLE_comp]
    · by_cases hi : i.val < n + 1 <;> simp [map, hk, hj, hi]

end Postcomp

/-- Appends an arrow `f : F.right ⟶ X` to the right end of `F : ComposableArrows C n`, producing a
string in `ComposableArrows C (n + 1)`. -/
@[expose, implicit_reducible]
def postcomp (F : ComposableArrows C n) {X : C} (f : F.right ⟶ X) :
    ComposableArrows C (n + 1) where
  obj := Postcomp.obj F X
  map g := Postcomp.map F f _ _ (leOfHom g)
  map_id := Postcomp.map_id F f
  map_comp g g' := Postcomp.map_comp F f (leOfHom g) (leOfHom g')

/-- The initial vertex `(F.postcomp f).obj 0` is definitionally `F.obj 0`. -/
@[simp]
lemma postcomp_obj_zero (F : ComposableArrows C n) {X : C} (f : F.right ⟶ X) :
    (F.postcomp f).obj 0 = F.obj 0 := (rfl)

/-- On the initial `n + 1` positions, `F.postcomp f` agrees with `F`. -/
@[simp]
lemma postcomp_obj_castSucc (F : ComposableArrows C n) {X : C} (f : F.right ⟶ X)
    (i : Fin (n + 1)) :
    (F.postcomp f).obj i.castSucc = F.obj i :=
  Postcomp.obj_castSucc F X i

/-- At the final position, `F.postcomp f` evaluates to the target of `f`. -/
@[simp]
lemma postcomp_obj_last (F : ComposableArrows C n) {X : C} (f : F.right ⟶ X) :
    (F.postcomp f).obj (Fin.last (n + 1)) = X :=
  Postcomp.obj_last F X

/-- The leftmost object of `F.postcomp f` is definitionally `F.left`. -/
@[simp]
lemma postcomp_left (F : ComposableArrows C n) {X : C} (f : F.right ⟶ X) :
    (F.postcomp f).left = F.left := (rfl)

/-- The rightmost object of `F.postcomp f` is the target of `f`. -/
@[simp]
lemma postcomp_right (F : ComposableArrows C n) {X : C} (f : F.right ⟶ X) :
    (F.postcomp f).right = X :=
  Postcomp.obj_last F X

/-- On morphisms between the initial `n + 1` vertices, `F.postcomp f` agrees with `F` modulo
`postcomp_obj_castSucc`. -/
theorem postcomp_map_castSucc (F : ComposableArrows C n) {X : C} (f : F.right ⟶ X)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    (F.postcomp f).map (homOfLE (Fin.castSucc_le_castSucc_iff.mpr hij)) =
      eqToHom (F.postcomp_obj_castSucc f i) ≫ F.map (homOfLE hij) ≫
        eqToHom (F.postcomp_obj_castSucc f j).symm := by
  simp [postcomp, Postcomp.map, j.isLt]

/-- Arrows between the initial `n + 1` vertices of `F.postcomp f` are the arrows of `F`. -/
@[simp]
theorem totalArrow_postcomp_castSucc_castSucc (F : ComposableArrows C n) {X : C}
    (f : F.right ⟶ X) (i j : Fin (n + 1)) (hij : i ≤ j) :
    (F.postcomp f).totalArrow i.castSucc j.castSucc (Fin.castSucc_le_castSucc_iff.mpr hij) =
      F.totalArrow i j hij := by
  rw [totalArrow_def, totalArrow_def]
  exact total_mk_eq (Postcomp.obj_castSucc F X i) (Postcomp.obj_castSucc F X j)
    (postcomp_map_castSucc F f i j hij)

/-- The arrow of `F.postcomp f` from an earlier vertex `i` to the final vertex is the arrow of `F`
from `i` to `F.right` followed by `f`. -/
@[simp]
theorem totalArrow_postcomp_castSucc_last (F : ComposableArrows C n) {X : C}
    (f : F.right ⟶ X) (i : Fin (n + 1)) :
    (F.postcomp f).totalArrow i.castSucc (Fin.last (n + 1)) (Fin.le_last _) =
      ⟨F.obj i, X, F.map (homOfLE (Nat.le_of_lt_succ i.isLt)) ≫ f⟩ := by
  rw [totalArrow_def]
  exact total_mk_eq (Postcomp.obj_castSucc F X i) (Postcomp.obj_last F X)
    (by simp [postcomp, Postcomp.map, i.isLt])

/-- Appending an arrow `f : X ⟶ Y` to the zero-arrow string `mk₀ X` produces `mk₁ f`. -/
@[simp]
theorem mk₀_postcomp {X Y : C} (f : X ⟶ Y) :
    (mk₀ X).postcomp f = mk₁ f := by
  refine ext_succ_of_totalArrow (ext₀ (postcomp_obj_last (mk₀ X) f)) ?_
  refine (totalArrow_postcomp_castSucc_last (mk₀ X) f 0).trans ?_
  rw [totalArrow_def]
  let hx : (mk₀ X).obj 0 = (mk₁ f).obj 0 := rfl
  let hy : Y = (mk₁ f).obj 1 := rfl
  have h₀ : (mk₀ X).map (homOfLE (Nat.le_of_lt_succ (0 : Fin 1).isLt)) = 𝟙 ((mk₀ X).obj 0) :=
    (congrArg (mk₀ X).map (Subsingleton.elim _ (𝟙 (0 : Fin 1)))).trans ((mk₀ X).map_id 0)
  have hlhs : (mk₀ X).map (homOfLE (Nat.le_of_lt_succ (0 : Fin 1).isLt)) ≫ f = f :=
    (congrArg (· ≫ f) h₀).trans (Category.id_comp (f : (mk₀ X).obj 0 ⟶ Y))
  have hrhs : eqToHom hx ≫ (mk₁ f).map (homOfLE (Fin.zero_le 1)) ≫ eqToHom hy.symm = f :=
    (Category.id_comp _).trans (by simp; rfl)
  exact total_mk_eq hx hy (hlhs.trans hrhs.symm)

/-- Deleting the final vertex of `F.postcomp f` recovers `F`, dual to `precomp_δ₀`. -/
@[simp]
theorem postcomp_δlast (F : ComposableArrows C n) {X : C} (f : F.right ⟶ X) :
    (F.postcomp f).δlast = F := by
  refine ext_of_totalArrow fun i j hij ↦ ?_
  refine ((F.postcomp f).totalArrow_whiskerLeft (Fin.castSuccFunctor (n + 1)) i j hij).trans ?_
  exact totalArrow_postcomp_castSucc_castSucc F f i j hij

/-- Reindexing `F.postcomp f` along `j.castSucc.succAbove` (deleting a vertex other than the last
from a string `F : ComposableArrows C (n + 1)` with an appended arrow `f`) deletes the `j`-th
vertex of `F` and appends the composite of the trailing arrow of `F` with `f`. -/
theorem whiskerLeft_castSucc_succAbove_postcomp (j : Fin (n + 2))
    (F : ComposableArrows C (n + 1)) {X : C} (f : F.right ⟶ X) :
    (F.postcomp f).whiskerLeft (Fin.strictMono_succAbove j.castSucc).monotone.functor =
      (F.whiskerLeft (Fin.strictMono_succAbove j).monotone.functor).postcomp
        (F.map (homOfLE (Fin.le_last (j.succAbove ⟨n, Nat.lt_succ_self n⟩))) ≫ f) := by
  have hlast : j.castSucc.succAbove (Fin.last (n + 1)) = Fin.last (n + 1 + 1) :=
    Fin.succAbove_of_le_castSucc j.castSucc (Fin.last (n + 1))
      (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last j))
  refine ext_of_totalArrow fun a b hab ↦ ?_
  obtain ⟨b', rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last b
  · obtain ⟨a', rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last a
    · have ha'b' : a' ≤ b' := Fin.castSucc_le_castSucc_iff.mp hab
      rw [totalArrow_whiskerLeft]
      dsimp only [Monotone.functor_obj]
      simp only [Fin.castSucc_succAbove_castSucc]
      rw [totalArrow_postcomp_castSucc_castSucc,
        totalArrow_postcomp_castSucc_castSucc _ _ a' b' ha'b', totalArrow_whiskerLeft]
      rfl
    · exact absurd (Fin.le_def.mp hab) (Nat.not_le_of_gt b'.isLt)
  · obtain ⟨a', rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last a
    · rw [totalArrow_whiskerLeft]
      dsimp only [Monotone.functor_obj]
      simp only [Fin.castSucc_succAbove_castSucc, hlast]
      rw [totalArrow_postcomp_castSucc_last, totalArrow_postcomp_castSucc_last]
      refine total_mk_eq rfl rfl ?_
      simp only [ComposableArrows.whiskerLeft, Functor.comp_map, eqToHom_refl, Category.id_comp,
        Category.comp_id, ← Category.assoc, ← F.map_comp]
      exact congrArg (fun g ↦ F.map g ≫ f) (Subsingleton.elim _ _)
    · rw [totalArrow_whiskerLeft, totalArrow_self, totalArrow_self]
      dsimp only [Monotone.functor_obj]
      exact total_id_eq
        ((congrArg (F.postcomp f).obj hlast).trans
          ((postcomp_obj_last F f).trans (postcomp_obj_last _ _).symm))

/-- Applying a functor to `F.postcomp f` appends `Φ.map f` to the image of `F`. -/
@[simp]
theorem _root_.CategoryTheory.Functor.mapComposableArrows_obj_postcomp {D : Type*} [Category* D]
    (Φ : C ⥤ D) (F : ComposableArrows C n) {X : C} (f : F.right ⟶ X) :
    (Φ.mapComposableArrows (n + 1)).obj (F.postcomp f) =
      ((Φ.mapComposableArrows n).obj F).postcomp (Φ.map f) := by
  refine ext_of_totalArrow fun a b hab ↦ ?_
  obtain ⟨b', rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last b
  · obtain ⟨a', rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last a
    · have ha'b' : a' ≤ b' := Fin.castSucc_le_castSucc_iff.mp hab
      rw [totalArrow_mapComposableArrows_obj,
        totalArrow_postcomp_castSucc_castSucc _ _ a' b' ha'b',
        totalArrow_postcomp_castSucc_castSucc _ _ a' b' ha'b',
        totalArrow_mapComposableArrows_obj]
    · exact absurd (Fin.le_def.mp hab) (Nat.not_le_of_gt b'.isLt)
  · obtain ⟨a', rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last a
    · rw [totalArrow_mapComposableArrows_obj]
      simp [totalArrow_postcomp_castSucc_last]
    · rw [totalArrow_self, totalArrow_self]
      exact total_id_eq
        ((congrArg Φ.obj (postcomp_obj_last F f)).trans (postcomp_obj_last _ _).symm)

end CategoryTheory.ComposableArrows
