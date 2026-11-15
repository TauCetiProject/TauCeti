/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.ComposableArrows.Basic

/-!
# Appending an arrow to a string of composable arrows

Given `F : ComposableArrows C n` and `g : F.right ⟶ Y`, `F.postcomp g : ComposableArrows C (n + 1)`
appends `g` at the right end of `F`, dual to `CategoryTheory.ComposableArrows.precomp`. Deleting the
final vertex recovers `F` (`CategoryTheory.ComposableArrows.δlast_postcomp`), and applying a functor
commutes with right-appending (`CategoryTheory.Functor.mapComposableArrows_obj_postcomp`).
-/

public section

universe v u

open CategoryTheory

namespace CategoryTheory.ComposableArrows

variable {C : Type u} [Category.{v} C] {n : ℕ}

namespace Postcomp

private def obj (F : ComposableArrows C n) (Y : C) (i : Fin (n + 2)) : C :=
  if h : i.val < n + 1 then F.obj ⟨i.val, h⟩ else Y

private lemma obj_of_lt (F : ComposableArrows C n) (Y : C) (i : Fin (n + 2)) (h : i.val < n + 1) :
    obj F Y i = F.obj ⟨i.val, h⟩ := dite_eq_left h

private lemma obj_of_not_lt (F : ComposableArrows C n) (Y : C) (i : Fin (n + 2))
    (h : ¬ i.val < n + 1) : obj F Y i = Y := dite_eq_right h

@[simp] private lemma obj_castSucc (F : ComposableArrows C n) (Y : C) (i : Fin (n + 1)) :
    obj F Y i.castSucc = F.obj i := obj_of_lt F Y i.castSucc i.isLt

@[simp] private lemma obj_last (F : ComposableArrows C n) (Y : C) :
    obj F Y (Fin.last (n + 1)) = Y := obj_of_not_lt F Y _ (Nat.lt_irrefl _)

private def map (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y) (i j : Fin (n + 2))
    (hij : i ≤ j) : obj F Y i ⟶ obj F Y j :=
  if hj : j.val < n + 1 then
    have hi : i.val < n + 1 := lt_of_le_of_lt hij hj
    eqToHom (obj_of_lt F Y i hi) ≫
      F.map (homOfLE (Fin.mk_le_mk.mpr (Fin.le_def.mp hij))) ≫
      eqToHom (obj_of_lt F Y j hj).symm
  else if hi : i.val < n + 1 then
    eqToHom (obj_of_lt F Y i hi) ≫ F.map (homOfLE (Fin.le_last ⟨i.val, hi⟩)) ≫ g ≫
      eqToHom (obj_of_not_lt F Y j hj).symm
  else
    eqToHom (obj_of_not_lt F Y i hi) ≫ eqToHom (obj_of_not_lt F Y j hj).symm

private lemma map_id (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y) (i : Fin (n + 2)) :
    map F g i i le_rfl = 𝟙 (obj F Y i) := by unfold map; split_ifs <;> simp

private lemma map_comp (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y)
    {i j k : Fin (n + 2)} (hij : i ≤ j) (hjk : j ≤ k) :
    map F g i k (hij.trans hjk) = map F g i j hij ≫ map F g j k hjk := by
  unfold map; split_ifs <;> first | omega | simp [← F.map_comp_assoc]

end Postcomp

/-- Append a morphism `g : F.right ⟶ Y` at the right end of `F : ComposableArrows C n`. -/
def postcomp (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y) : ComposableArrows C (n + 1) where
  obj := Postcomp.obj F Y
  map h := Postcomp.map F g _ _ (leOfHom h)
  map_id := Postcomp.map_id F g
  map_comp h₁ h₂ := Postcomp.map_comp F g (leOfHom h₁) (leOfHom h₂)

@[simp] theorem postcomp_obj_castSucc (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y)
    (i : Fin (n + 1)) : (F.postcomp g).obj i.castSucc = F.obj i := Postcomp.obj_castSucc F Y i

@[simp] theorem postcomp_obj_zero (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y) :
    (F.postcomp g).obj 0 = F.obj 0 := F.postcomp_obj_castSucc g 0

@[simp] theorem postcomp_obj_last (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y) :
    (F.postcomp g).obj (Fin.last (n + 1)) = Y := Postcomp.obj_last F Y

@[simp] theorem postcomp_left (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y) :
    (F.postcomp g).left = F.left := F.postcomp_obj_castSucc g 0

@[simp] theorem postcomp_right (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y) :
    (F.postcomp g).right = Y := Postcomp.obj_last F Y

/-- Arrows of `F.postcomp g` between non-final vertices coincide with the arrows of `F`. -/
@[simp] theorem totalArrow_postcomp_castSucc_castSucc (F : ComposableArrows C n) {Y : C}
    (g : F.right ⟶ Y) (i j : Fin (n + 1)) (hij : i ≤ j) :
    (F.postcomp g).totalArrow i.castSucc j.castSucc (Fin.castSucc_le_castSucc_iff.mpr hij) =
      F.totalArrow i j hij := by
  rw [totalArrow_def, totalArrow_def]
  refine Quiver.Total.ext (F.postcomp_obj_castSucc g i) (F.postcomp_obj_castSucc g j) ?_
  exact (conj_eqToHom_iff_heq _ _ (F.postcomp_obj_castSucc g i)
    (F.postcomp_obj_castSucc g j)).mp (by simp [postcomp, Postcomp.map, j.isLt])

/-- The arrow of `F.postcomp g` from `i.castSucc` to the final vertex composes with `g`. -/
@[simp] theorem totalArrow_postcomp_castSucc_last (F : ComposableArrows C n) {Y : C}
    (g : F.right ⟶ Y) (i : Fin (n + 1)) :
    (F.postcomp g).totalArrow i.castSucc (Fin.last (n + 1)) (Fin.le_last _) =
      ⟨F.obj i, Y, F.map (homOfLE (Fin.le_last i)) ≫ g⟩ := by
  rw [totalArrow_def]
  refine Quiver.Total.ext (F.postcomp_obj_castSucc g i) (F.postcomp_obj_last g) ?_
  exact (conj_eqToHom_iff_heq _ _ (F.postcomp_obj_castSucc g i)
    (F.postcomp_obj_last g)).mp (by simp [postcomp, Postcomp.map, i.isLt])

/-- Deleting the final vertex of `F.postcomp g` recovers `F`. -/
@[simp] theorem δlast_postcomp (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y) :
    (F.postcomp g).δlast = F :=
  ext_of_totalArrow fun i j hij ↦
    ((F.postcomp g).totalArrow_whiskerLeft (Fin.castSuccFunctor (n + 1)) i j hij).trans
      (F.totalArrow_postcomp_castSucc_castSucc g i j hij)

/-- Applying a functor `Φ` to `F.postcomp g` appends `Φ.map g` to the image of `F`. -/
@[simp] theorem _root_.CategoryTheory.Functor.mapComposableArrows_obj_postcomp {D : Type*}
    [Category* D] (Φ : C ⥤ D) (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y) :
    (Φ.mapComposableArrows (n + 1)).obj (F.postcomp g) =
      ((Φ.mapComposableArrows n).obj F).postcomp (Φ.map g) := by
  let FΦ : ComposableArrows D n := (Φ.mapComposableArrows n).obj F
  refine ext_of_totalArrow fun i j hij ↦ (totalArrow_mapComposableArrows_obj ..).trans ?_
  induction j using Fin.lastCases with
  | last =>
    induction i using Fin.lastCases with
    | last =>
      rw [totalArrow_self, totalArrow_self]
      have hY : Φ.obj ((F.postcomp g).obj (Fin.last (n + 1))) =
          (FΦ.postcomp (Φ.map g)).obj (Fin.last (n + 1)) := by simp [FΦ]
      exact Quiver.Total.ext hY hY ((conj_eqToHom_iff_heq _ _ hY hY).mp (by simp))
    | cast i =>
      rw [totalArrow_postcomp_castSucc_last, FΦ.totalArrow_postcomp_castSucc_last]
      simp [FΦ, Functor.mapComposableArrows]
  | cast j =>
    induction i using Fin.lastCases with
    | last => exact (Nat.not_lt.mpr hij j.isLt).elim
    | cast i =>
      have hij' : i ≤ j := Fin.castSucc_le_castSucc_iff.mp hij
      rw [totalArrow_postcomp_castSucc_castSucc _ _ _ _ hij',
        FΦ.totalArrow_postcomp_castSucc_castSucc _ _ _ hij', totalArrow_mapComposableArrows_obj]

end CategoryTheory.ComposableArrows
