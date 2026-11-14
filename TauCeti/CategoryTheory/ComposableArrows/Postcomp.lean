/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import TauCeti.CategoryTheory.ComposableArrows.Basic

/-!
# Appending an arrow to a string of composable arrows

Given a string `F : ComposableArrows C n` of `n` composable arrows in a category `C` and a morphism
`g : F.right ⟶ Y` out of its rightmost vertex, `F.postcomp g : ComposableArrows C (n + 1)` appends
`g` at the right end of `F`, dual to Mathlib's `CategoryTheory.ComposableArrows.precomp`.

Deleting the final vertex of `F.postcomp g` recovers `F` (`CategoryTheory.nerve.δ_last_postcomp`).
When `Y` is a terminal object `t`, every face other than the last commutes with appending the
unique arrow to `t` (`CategoryTheory.nerve.δ_castSucc_postcomp_isTerminal`), supplying the right
extra degeneracy on nerve chains with functor coefficients.

## Main declarations

* `CategoryTheory.ComposableArrows.postcomp`: append `g : F.right ⟶ Y` at the right end of `F`.
* `CategoryTheory.nerve.δ_last_postcomp`: the last face of `F.postcomp g` in `nerve C` is `F`.
* `CategoryTheory.nerve.δ_castSucc_postcomp_isTerminal`: for a terminal object `t`, every non-last
  face `δ k.castSucc` commutes with appending the unique morphism to `t`.
-/

public section

universe v u

open CategoryTheory Limits Simplicial

namespace CategoryTheory.ComposableArrows

variable {C : Type u} [Category.{v} C] {n : ℕ}

namespace Postcomp

private def obj (F : ComposableArrows C n) (Y : C) (i : Fin (n + 2)) : C :=
  if h : i.val < n + 1 then F.obj ⟨i.val, h⟩ else Y

private lemma obj_of_lt (F : ComposableArrows C n) (Y : C) (i : Fin (n + 2)) (h : i.val < n + 1) :
    obj F Y i = F.obj ⟨i.val, h⟩ := by
  simp [obj, h]

private lemma obj_of_not_lt (F : ComposableArrows C n) (Y : C) (i : Fin (n + 2))
    (h : ¬ i.val < n + 1) :
    obj F Y i = Y := by
  simp [obj, h]

@[simp]
private lemma obj_castSucc (F : ComposableArrows C n) (Y : C) (i : Fin (n + 1)) :
    obj F Y i.castSucc = F.obj i :=
  obj_of_lt F Y i.castSucc i.isLt

@[simp]
private lemma obj_last (F : ComposableArrows C n) (Y : C) :
    obj F Y (Fin.last (n + 1)) = Y :=
  obj_of_not_lt F Y (Fin.last (n + 1)) (Nat.lt_irrefl (n + 1))

private def map (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y) (i j : Fin (n + 2))
    (hij : i ≤ j) :
    obj F Y i ⟶ obj F Y j :=
  if hj : j.val < n + 1 then
    have hi : i.val < n + 1 := lt_of_le_of_lt hij hj
    eqToHom (obj_of_lt F Y i hi) ≫
      F.map (homOfLE (show (⟨i.val, hi⟩ : Fin (n + 1)) ≤ ⟨j.val, hj⟩ from hij)) ≫
      eqToHom (obj_of_lt F Y j hj).symm
  else if hi : i.val < n + 1 then
    eqToHom (obj_of_lt F Y i hi) ≫
      F.map (homOfLE (Fin.le_last ⟨i.val, hi⟩)) ≫ g ≫
      eqToHom (obj_of_not_lt F Y j hj).symm
  else
    eqToHom (obj_of_not_lt F Y i hi) ≫ eqToHom (obj_of_not_lt F Y j hj).symm

private lemma map_id (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y) (i : Fin (n + 2)) :
    map F g i i le_rfl = 𝟙 (obj F Y i) := by
  unfold map
  split_ifs <;> simp

private lemma map_comp (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y)
    {i j k : Fin (n + 2)} (hij : i ≤ j) (hjk : j ≤ k) :
    map F g i k (hij.trans hjk) = map F g i j hij ≫ map F g j k hjk := by
  unfold map
  split_ifs with h₁ h₂ h₃ h₄ h₅ <;> try omega
  · simp [← F.map_comp_assoc]
  · simp [← F.map_comp_assoc]
  · simp
  · simp

end Postcomp

/-- Append a morphism `g : F.right ⟶ Y` at the right end of `F : ComposableArrows C n`. -/
def postcomp (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y) : ComposableArrows C (n + 1) where
  obj := Postcomp.obj F Y
  map h := Postcomp.map F g _ _ (leOfHom h)
  map_id := Postcomp.map_id F g
  map_comp h₁ h₂ := Postcomp.map_comp F g (leOfHom h₁) (leOfHom h₂)

/-- At `i.castSucc`, `F.postcomp g` has the `i`-th object of `F`. -/
@[simp]
theorem postcomp_obj_castSucc (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y)
    (i : Fin (n + 1)) :
    (F.postcomp g).obj i.castSucc = F.obj i :=
  Postcomp.obj_castSucc F Y i

/-- At `0`, `F.postcomp g` has object `F.obj 0`. -/
@[simp]
theorem postcomp_obj_zero (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y) :
    (F.postcomp g).obj 0 = F.obj 0 :=
  F.postcomp_obj_castSucc g 0

/-- At `Fin.last (n + 1)`, `F.postcomp g` has object `Y`. -/
@[simp]
theorem postcomp_obj_last (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y) :
    (F.postcomp g).obj (Fin.last (n + 1)) = Y :=
  Postcomp.obj_last F Y

/-- Appending an arrow on the right preserves `F.left`. -/
@[simp]
theorem postcomp_left (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y) :
    (F.postcomp g).left = F.left :=
  F.postcomp_obj_castSucc g 0

/-- The rightmost vertex of `F.postcomp g` is the target `Y` of `g`. -/
@[simp]
theorem postcomp_right (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y) :
    (F.postcomp g).right = Y :=
  Postcomp.obj_last F Y

/-- Arrows of `F.postcomp g` between non-final vertices coincide with the arrows of `F`. -/
@[simp]
theorem totalArrow_postcomp_castSucc_castSucc (F : ComposableArrows C n) {Y : C}
    (g : F.right ⟶ Y) (i j : Fin (n + 1)) (hij : i ≤ j) :
    (F.postcomp g).totalArrow i.castSucc j.castSucc (Fin.castSucc_le_castSucc_iff.mpr hij) =
      F.totalArrow i j hij := by
  rw [totalArrow_def, totalArrow_def]
  refine Quiver.Total.ext (postcomp_obj_castSucc F g i) (postcomp_obj_castSucc F g j) ?_
  dsimp only
  refine (conj_eqToHom_iff_heq _ _ (postcomp_obj_castSucc F g i)
    (postcomp_obj_castSucc F g j)).mp ?_
  simp [postcomp, Postcomp.map, j.isLt]

/-- The arrow of `F.postcomp g` from `i.castSucc` to the final vertex is the arrow of `F` from `i`
to `F.right` followed by `g`. -/
@[simp]
theorem totalArrow_postcomp_castSucc_last (F : ComposableArrows C n) {Y : C}
    (g : F.right ⟶ Y) (i : Fin (n + 1)) :
    (F.postcomp g).totalArrow i.castSucc (Fin.last (n + 1)) (Fin.le_last _) =
      ⟨F.obj i, Y, F.map (homOfLE (Fin.le_last i)) ≫ g⟩ := by
  rw [totalArrow_def]
  refine Quiver.Total.ext (postcomp_obj_castSucc F g i) (postcomp_obj_last F g) ?_
  dsimp only
  refine (conj_eqToHom_iff_heq _ _ (postcomp_obj_castSucc F g i) (postcomp_obj_last F g)).mp ?_
  simp [postcomp, Postcomp.map, i.isLt]

/-- Deleting the final vertex of `F.postcomp g` recovers `F`. -/
@[simp]
theorem δlast_postcomp (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y) :
    (F.postcomp g).δlast = F := by
  refine ext_of_totalArrow fun i j hij ↦ ?_
  refine ((F.postcomp g).totalArrow_whiskerLeft (Fin.castSuccFunctor (n + 1)) i j hij).trans ?_
  exact F.totalArrow_postcomp_castSucc_castSucc g i j hij

/-- Applying a functor `Φ` to `F.postcomp g` appends `Φ.map g` to the image of `F`. -/
@[simp]
theorem _root_.CategoryTheory.Functor.mapComposableArrows_obj_postcomp {D : Type*} [Category* D]
    (Φ : C ⥤ D) (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y) :
    (Φ.mapComposableArrows (n + 1)).obj (F.postcomp g) =
      ((Φ.mapComposableArrows n).obj F).postcomp (Φ.map g) := by
  let FΦ : ComposableArrows D n := (Φ.mapComposableArrows n).obj F
  refine ext_of_totalArrow fun i j hij ↦ ?_
  rw [totalArrow_mapComposableArrows_obj]
  induction j using Fin.lastCases with
  | last =>
    induction i using Fin.lastCases with
    | last =>
      rw [totalArrow_self, totalArrow_self]
      have hY : Φ.obj ((F.postcomp g).obj (Fin.last (n + 1))) =
          (FΦ.postcomp (Φ.map g)).obj (Fin.last (n + 1)) := by
        rw [F.postcomp_obj_last g, FΦ.postcomp_obj_last (Φ.map g)]
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

namespace CategoryTheory.nerve

variable {C : Type u} [Category.{v} C] {n : ℕ}

private lemma totalArrow_δ {m : ℕ} (i : Fin (m + 2)) (F : ComposableArrows C (m + 1))
    (a b : Fin (m + 1)) (hab : a ≤ b) :
    ((nerve C).δ i F).totalArrow a b hab =
      F.totalArrow (i.succAbove a) (i.succAbove b) ((Fin.strictMono_succAbove i).monotone hab) :=
  F.totalArrow_whiskerLeft _ a b hab

private lemma totalArrow_congr_idx {m : ℕ} (F : ComposableArrows C m) {a a' b b' : Fin (m + 1)}
    (ha : a = a') (hb : b = b') (hab : a ≤ b) :
    F.totalArrow a b hab = F.totalArrow a' b' (ha ▸ hb ▸ hab) := by
  subst ha; subst hb; rfl

/-- The last face of `F.postcomp g` in `nerve C` is `F`. -/
@[simp]
theorem δ_last_postcomp (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y) :
    (nerve C).δ (Fin.last (n + 1)) (F.postcomp g) = F := by
  refine ComposableArrows.ext_of_totalArrow fun i j hij ↦ ?_
  rw [totalArrow_δ, totalArrow_congr_idx _ (Fin.succAbove_last_apply i)
    (Fin.succAbove_last_apply j)]
  exact F.totalArrow_postcomp_castSucc_castSucc g i j hij

/-- When `t` is terminal, every non-last face `δ k.castSucc` commutes with appending the unique
morphism to `t`. -/
theorem δ_castSucc_postcomp_isTerminal (F : ComposableArrows C (n + 1)) {t : C} (ht : IsTerminal t)
    (k : Fin (n + 2)) :
    (nerve C).δ k.castSucc (F.postcomp (ht.from F.right)) =
      ComposableArrows.postcomp (n := n) ((nerve C).δ k F)
        (ht.from (ComposableArrows.right (n := n) ((nerve C).δ k F))) := by
  let G : ComposableArrows C n := (nerve C).δ k F
  refine ComposableArrows.ext_of_totalArrow (n := n + 1) fun i j hij ↦ ?_
  rw [totalArrow_δ (m := n + 1)]
  have hl : k.castSucc.succAbove (Fin.last (n + 1)) = Fin.last (n + 2) :=
    (Fin.succAbove_castSucc_of_le k (Fin.last (n + 1)) (Fin.le_last k)).trans (Fin.succ_last _)
  induction j using Fin.lastCases with
  | last =>
    induction i using Fin.lastCases with
    | last =>
      rw [totalArrow_congr_idx _ hl hl, ComposableArrows.totalArrow_self,
        ComposableArrows.totalArrow_self]
      have hlast : (F.postcomp (ht.from F.right)).obj (Fin.last (n + 2)) =
          (G.postcomp (ht.from G.right)).obj (Fin.last (n + 1)) := by
        rw [F.postcomp_obj_last _, G.postcomp_obj_last _]
      exact Quiver.Total.ext hlast hlast ((conj_eqToHom_iff_heq _ _ hlast hlast).mp (by simp [G]))
    | cast i =>
      rw [totalArrow_congr_idx _ Fin.castSucc_succAbove_castSucc hl,
        ComposableArrows.totalArrow_postcomp_castSucc_last,
        G.totalArrow_postcomp_castSucc_last]
      have hd : F.obj (k.succAbove i) = G.obj i := rfl
      exact Quiver.Total.ext hd rfl ((conj_eqToHom_iff_heq _ _ hd rfl).mp (ht.hom_ext _ _))
  | cast j =>
    induction i using Fin.lastCases with
    | last => exact (Nat.not_lt.mpr hij j.isLt).elim
    | cast i =>
      have hij' : i ≤ j := Fin.castSucc_le_castSucc_iff.mp hij
      rw [totalArrow_congr_idx _ Fin.castSucc_succAbove_castSucc Fin.castSucc_succAbove_castSucc,
        ComposableArrows.totalArrow_postcomp_castSucc_castSucc,
        G.totalArrow_postcomp_castSucc_castSucc _ _ _ hij']
      exact (totalArrow_δ k F i j hij').symm

/-- For a `0`-simplex `σ` of `nerve C`, the zeroth face of `σ.postcomp g` is `mk₀ Y`. -/
@[simp]
theorem δ_zero_postcomp_zero (σ : ComposableArrows C 0) {Y : C} (g : σ.right ⟶ Y) :
    (nerve C).δ 0 (σ.postcomp g) = ComposableArrows.mk₀ Y :=
  ComposableArrows.ext₀ (σ.postcomp_obj_last g)

end CategoryTheory.nerve
