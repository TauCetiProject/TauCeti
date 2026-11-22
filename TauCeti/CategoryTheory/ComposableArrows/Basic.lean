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
(`CategoryTheory.ComposableArrows.totalArrow_precomp_succ_succ`), appending `g : F.right ⟶ Y`
with `CategoryTheory.ComposableArrows.postcomp` preserves existing vertices and arrows and joins
each vertex `i` of `F` to the appended final vertex `Y` by `F.map (homOfLE (Fin.le_last i)) ≫ g`
(`CategoryTheory.ComposableArrows.totalArrow_postcomp_castSucc`,
`CategoryTheory.ComposableArrows.totalArrow_postcomp_castSucc_last`), and applying a functor to the
string maps its arrows along the functor
(`CategoryTheory.ComposableArrows.totalArrow_mapComposableArrows_obj`), respects identities,
composites, `0`-simplices, and `1`-simplices (`CategoryTheory.Functor.id_mapComposableArrows_obj`,
`CategoryTheory.Functor.comp_mapComposableArrows_obj`,
`CategoryTheory.Functor.mapComposableArrows_obj_mk₀`,
`CategoryTheory.Functor.mapComposableArrows_obj_mk₁`), and commutes with prepending
(`CategoryTheory.Functor.mapComposableArrows_obj_precomp`). A string of at least one
arrow is already determined by its first arrow and the remaining string
(`CategoryTheory.ComposableArrows.ext_succ_of_totalArrow`).

All vertices of a composable string in a groupoid have the same isomorphism class.

## Main declarations

* `CategoryTheory.ComposableArrows.totalArrow`: the arrow of a string between two positions.
* `CategoryTheory.ComposableArrows.postcomp`: append a morphism at the right end of a string.
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

/-- The first arrow of a prepended string is the prepended arrow. -/
@[simp]
theorem precomp_map'_zero_one (F : ComposableArrows C n) {X : C} (f : X ⟶ F.left) :
    (F.precomp f).map' 0 1 = f :=
  rfl

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

/-- Applying a functor to the `0`-simplex `mk₀ X` gives `mk₀ (Φ.obj X)`. -/
@[simp]
theorem _root_.CategoryTheory.Functor.mapComposableArrows_obj_mk₀ {D : Type*} [Category D]
    (Φ : C ⥤ D) (X : C) :
    (Φ.mapComposableArrows 0).obj (mk₀ X) = mk₀ (Φ.obj X) :=
  ext₀ rfl

/-- Applying a functor to the `1`-simplex `mk₁ f` gives `mk₁ (Φ.map f)`. -/
@[simp]
theorem _root_.CategoryTheory.Functor.mapComposableArrows_obj_mk₁ {D : Type*} [Category D]
    (Φ : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    (Φ.mapComposableArrows 1).obj (mk₁ f) = mk₁ (Φ.map f) :=
  ext₁ rfl rfl (by simp)

/-- Applying the identity functor to a string of composable arrows leaves it unchanged. -/
@[simp]
theorem _root_.CategoryTheory.Functor.id_mapComposableArrows_obj (F : ComposableArrows C n) :
    ((𝟭 C).mapComposableArrows n).obj F = F :=
  ext_of_totalArrow fun _ _ _ ↦ by simp [totalArrow_def]

/-- Applying a composite functor to a string of composable arrows applies each functor in turn. -/
@[simp]
theorem _root_.CategoryTheory.Functor.comp_mapComposableArrows_obj {D E : Type*}
    [Category D] [Category E] (Φ : C ⥤ D) (Ψ : D ⥤ E) (F : ComposableArrows C n) :
    ((Φ ⋙ Ψ).mapComposableArrows n).obj F =
      (Ψ.mapComposableArrows n).obj ((Φ.mapComposableArrows n).obj F) :=
  ext_of_totalArrow fun _ _ _ ↦ by simp [totalArrow_def]

section Postcomp

open Category

private def postcompObj (σ : ComposableArrows C n) (Y : C) (i : Fin (n + 2)) : C :=
  if hi : i.val < n + 1 then σ.obj ⟨i.val, hi⟩ else Y

private lemma postcompObj_pos (σ : ComposableArrows C n) (Y : C) {i : Fin (n + 2)}
    (hi : i.val < n + 1) : postcompObj σ Y i = σ.obj ⟨i.val, hi⟩ := dite_eq_left hi

private lemma postcompObj_neg (σ : ComposableArrows C n) (Y : C) {i : Fin (n + 2)}
    (hi : ¬ i.val < n + 1) : postcompObj σ Y i = Y := dite_eq_right hi

/-- Append a morphism `g : σ.right ⟶ Y` at the right end of `σ : ComposableArrows C n`. -/
def postcomp (σ : ComposableArrows C n) {Y : C} (g : σ.right ⟶ Y) : ComposableArrows C (n + 1) where
  obj := postcompObj σ Y
  map {i j} f :=
    if hj : j.val < n + 1 then
      have hi : i.val < n + 1 := Nat.lt_of_le_of_lt f.le hj
      eqToHom (postcompObj_pos σ Y hi) ≫
        σ.map (homOfLE (Fin.mk_le_mk.mpr (Fin.le_def.mp f.le))) ≫
          eqToHom (postcompObj_pos σ Y hj).symm
    else if hi : i.val < n + 1 then
      eqToHom (postcompObj_pos σ Y hi) ≫
        σ.map (homOfLE (Fin.le_last ⟨i.val, hi⟩)) ≫ g ≫ eqToHom (postcompObj_neg σ Y hj).symm
    else eqToHom ((postcompObj_neg σ Y hi).trans (postcompObj_neg σ Y hj).symm)
  map_id i := by
    by_cases hi : i.val < n + 1
    · rw [dite_eq_left hi]; simp
    · rw [dite_eq_right hi, dite_eq_right hi]; simp
  map_comp {i j k} f h := by
    by_cases hk : k.val < n + 1
    · have hj : j.val < n + 1 := Nat.lt_of_le_of_lt h.le hk
      have hi : i.val < n + 1 := Nat.lt_of_le_of_lt f.le hj
      rw [dite_eq_left hk, dite_eq_left hj, dite_eq_left hk]
      simp only [assoc, eqToHom_trans_assoc, eqToHom_refl, id_comp, ← σ.map_comp_assoc]
      exact congrArg (fun u ↦ eqToHom (postcompObj_pos σ Y hi) ≫ σ.map u ≫
        eqToHom (postcompObj_pos σ Y hk).symm) (Subsingleton.elim _ _)
    · rw [dite_eq_right hk, dite_eq_right hk]
      by_cases hj : j.val < n + 1
      · have hi : i.val < n + 1 := Nat.lt_of_le_of_lt f.le hj
        rw [dite_eq_left hi, dite_eq_left hj, dite_eq_left hj]
        simp only [assoc, eqToHom_trans_assoc, eqToHom_refl, id_comp, ← σ.map_comp_assoc]
        exact congrArg (fun u ↦ eqToHom (postcompObj_pos σ Y hi) ≫ σ.map u ≫ g ≫
          eqToHom (postcompObj_neg σ Y hk).symm) (Subsingleton.elim _ _)
      · rw [dite_eq_right hj, dite_eq_right hj]
        by_cases hi : i.val < n + 1
        · rw [dite_eq_left hi, dite_eq_left hi]; simp only [assoc, eqToHom_trans]
        · rw [dite_eq_right hi, dite_eq_right hi, eqToHom_trans]

@[simp] theorem postcomp_obj_castSucc (σ : ComposableArrows C n) {Y : C} (g : σ.right ⟶ Y)
    (j : Fin (n + 1)) : (σ.postcomp g).obj j.castSucc = σ.obj j := postcompObj_pos σ Y j.isLt

@[simp] theorem postcomp_obj_zero (σ : ComposableArrows C n) {Y : C} (g : σ.right ⟶ Y) :
    (σ.postcomp g).obj 0 = σ.obj 0 := σ.postcomp_obj_castSucc g 0

theorem postcomp_obj_succ_zero (σ : ComposableArrows C (n + 1)) {Y : C} (g : σ.right ⟶ Y) :
    (σ.postcomp g).obj (Fin.succ 0) = σ.obj (Fin.succ 0) := σ.postcomp_obj_castSucc g (Fin.succ 0)

@[simp] theorem postcomp_obj_last (σ : ComposableArrows C n) {Y : C} (g : σ.right ⟶ Y) :
    (σ.postcomp g).obj (Fin.last (n + 1)) = Y := postcompObj_neg σ Y (Nat.lt_irrefl (n + 1))

theorem postcomp_map_castSucc (σ : ComposableArrows C n) {Y : C} (g : σ.right ⟶ Y)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    (σ.postcomp g).map (homOfLE (Fin.castSucc_le_castSucc_iff.mpr hij)) =
      eqToHom (σ.postcomp_obj_castSucc g i) ≫ σ.map (homOfLE hij) ≫
        eqToHom (σ.postcomp_obj_castSucc g j).symm := by dsimp [postcomp]; rw [dite_eq_left j.isLt]

theorem postcomp_map_last (σ : ComposableArrows C n) {Y : C} (g : σ.right ⟶ Y) (i : Fin (n + 1)) :
    (σ.postcomp g).map (homOfLE (Fin.le_last i.castSucc)) =
      eqToHom (σ.postcomp_obj_castSucc g i) ≫ σ.map (homOfLE (Fin.le_last i)) ≫ g ≫
        eqToHom (σ.postcomp_obj_last g).symm := by
  dsimp [postcomp]; rw [dite_eq_right (Nat.lt_irrefl (n + 1)), dite_eq_left i.isLt]

@[simp] theorem totalArrow_postcomp_castSucc (σ : ComposableArrows C n) {Y : C} (g : σ.right ⟶ Y)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    (σ.postcomp g).totalArrow i.castSucc j.castSucc (Fin.castSucc_le_castSucc_iff.mpr hij) =
      σ.totalArrow i j hij := by
  rw [totalArrow_def, totalArrow_def]
  exact Quiver.Total.ext (σ.postcomp_obj_castSucc g i) (σ.postcomp_obj_castSucc g j)
    ((conj_eqToHom_iff_heq _ _ (σ.postcomp_obj_castSucc g i)
      (σ.postcomp_obj_castSucc g j)).mp (σ.postcomp_map_castSucc g hij))

@[simp] theorem totalArrow_postcomp_castSucc_last (σ : ComposableArrows C n) {Y : C}
    (g : σ.right ⟶ Y) (i : Fin (n + 1)) :
    (σ.postcomp g).totalArrow i.castSucc (Fin.last (n + 1)) (Fin.le_last _) =
      ⟨σ.obj i, Y, σ.map (homOfLE (Fin.le_last i)) ≫ g⟩ := by
  rw [totalArrow_def]
  refine Quiver.Total.ext (σ.postcomp_obj_castSucc g i) (σ.postcomp_obj_last g)
    ((conj_eqToHom_iff_heq _ _ (σ.postcomp_obj_castSucc g i) (σ.postcomp_obj_last g)).mp ?_)
  simpa using σ.postcomp_map_last g i

/-- Forgetting the last arrow of `σ.postcomp g` recovers `σ`, dual to `precomp_δ₀`. -/
@[simp] theorem postcomp_δlast (σ : ComposableArrows C n) {Y : C} (g : σ.right ⟶ Y) :
    (σ.postcomp g).δlast = σ := by
  refine ext_of_totalArrow fun i j hij ↦ ?_
  dsimp [δlast, δlastFunctor, whiskerLeftFunctor]; rw [totalArrow_whiskerLeft]
  exact σ.totalArrow_postcomp_castSucc g i j hij

@[simp] theorem mk₀_postcomp {X Y : C} (g : (mk₀ X).right ⟶ Y) : (mk₀ X).postcomp g = mk₁ g :=
  ext₁ ((mk₀ X).postcomp_obj_zero g) ((mk₀ X).postcomp_obj_last g) (by
    dsimp [hom, map', postcomp, mk₀, mk₁]; simp)

theorem eqToHom_postcomp_map_zero_one {D : Type*} [Category* D] (M : C ⥤ D)
    (σ : ComposableArrows C (n + 1)) {Y : C} (g : σ.right ⟶ Y) :
    eqToHom (congrArg M.obj (σ.postcomp_obj_zero g).symm) ≫
        M.map ((σ.postcomp g).map (homOfLE (Fin.zero_le (Fin.succ 0)))) =
      M.map (σ.map (homOfLE (Fin.zero_le (Fin.succ 0)))) ≫
        eqToHom (congrArg M.obj (σ.postcomp_obj_succ_zero g).symm) := by
  have htot := σ.totalArrow_postcomp_castSucc g 0 (Fin.succ 0) (Fin.zero_le _)
  rw [totalArrow_def, totalArrow_def] at htot; obtain ⟨h0, h1, hm⟩ := Quiver.Total.mk.inj htot
  dsimp only [← Fin.succ_castSucc, Fin.castSucc_zero] at h0 h1 hm
  rw [(conj_eqToHom_iff_heq _ _ h0 h1).mpr hm, M.map_comp, M.map_comp, eqToHom_map, eqToHom_map]
  simp

end Postcomp

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
