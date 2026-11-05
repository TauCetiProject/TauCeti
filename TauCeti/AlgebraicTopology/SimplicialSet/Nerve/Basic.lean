/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.Combinatorics.Quiver.Subquiver
public import TauCeti.Combinatorics.Quiver.Prefunctor

/-!
# Arrows of simplices of the nerve and the images of its degeneracies

An `n`-simplex of the nerve `CategoryTheory.nerve C` of a category is a string
`F : ComposableArrows C n` of composable arrows. For positions `i ≤ j` its arrow from the `i`-th
to the `j`-th object, viewed as a total arrow of `C`, is `F.totalArrow i j hij`; the simplicial
operators of the nerve reindex these arrows
(`CategoryTheory.ComposableArrows.totalArrow_whiskerLeft`), prepending an arrow with
`CategoryTheory.ComposableArrows.precomp` shifts them
(`CategoryTheory.ComposableArrows.totalArrow_precomp_succ_succ`), and applying a functor to the
string maps its arrows along the functor
(`CategoryTheory.ComposableArrows.totalArrow_mapComposableArrows_obj`).

An `n + 1`-simplex of the nerve lies in the image of the `i`-th degeneracy exactly when its
`i`-th arrow is an identity arrow (`CategoryTheory.nerve.mem_range_σ_iff`, in `Set.range` form
`CategoryTheory.nerve.range_σ_eq_preimage`). This generalizes, and adapts the proof of, Mathlib's
`PartialOrder.mem_range_nerve_σ_iff` from partial orders to arbitrary categories.

## Main declarations

* `CategoryTheory.ComposableArrows.totalArrow`: the arrow of a string between two positions.
* `CategoryTheory.nerve.σ_δ_castSucc_eq_self`: a string whose `i`-th arrow is an identity is the
  `i`-th degeneracy of its `i`-th face.
* `CategoryTheory.nerve.mem_range_σ_iff`: the image of the `i`-th degeneracy consists of the
  strings whose `i`-th arrow is an identity.
-/

public section

open CategoryTheory

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

end CategoryTheory.ComposableArrows

namespace CategoryTheory.nerve

variable {C : Type u} [Category.{v} C]

/-- A string of composable arrows whose `i`-th arrow is an identity arrow is the `i`-th degeneracy
of its face deleting the `i`-th object. -/
theorem σ_δ_castSucc_eq_self {n : ℕ} (s : ComposableArrows C (n + 1)) {i : Fin (n + 1)}
    {h : s.obj i.castSucc = s.obj i.succ} (hi : s.map (homOfLE i.castSucc_le_succ) = eqToHom h) :
    (nerve C).σ i ((nerve C).δ i.castSucc s) = s := by
  -- Removing the `i`-th object and then repeating the next one reindexes the string along `Φ`,
  -- which moves position `i.castSucc` to `i.succ` and fixes every other position.
  let Φ (j : Fin (n + 2)) : Fin (n + 2) := i.castSucc.succAbove (i.predAbove j)
  have hmono : Monotone Φ :=
    (Fin.strictMono_succAbove _).monotone.comp (Fin.predAbove_right_monotone i)
  -- By definition the nerve acts on strings by whiskering (on objects this is `nerve.σ_obj` and
  -- `nerve.δ_obj`), so the degeneracy of the face is `s` whiskered by `Φ`.
  have hσδ : (nerve C).σ i ((nerve C).δ i.castSucc s) = s.whiskerLeft hmono.functor := rfl
  have hΦ (j : Fin (n + 2)) : (j = i.castSucc ∧ Φ j = i.succ) ∨ Φ j = j := by
    obtain rfl | h := eq_or_ne j i.castSucc
    · simp [Φ]
    · exact .inr (Fin.succAbove_predAbove h)
  -- Each object of the string is joined to its new position by an identity arrow.
  have key (j : Fin (n + 2)) :
      ∃ e : s.obj j = s.obj (Φ j), ∀ hj : j ≤ Φ j, s.map (homOfLE hj) = eqToHom e := by
    have := hΦ j
    generalize Φ j = k at this ⊢
    rcases this with ⟨rfl, rfl⟩ | rfl
    · exact ⟨_, fun _ ↦ hi⟩
    · exact ⟨rfl, fun _ ↦ by simp⟩
  choose e he using key
  have hle (j : Fin (n + 2)) : j ≤ Φ j := by
    rcases hΦ j with ⟨rfl, h⟩ | h
    · exact h ▸ i.castSucc_le_succ
    · exact h.ge
  rw [hσδ]
  refine Functor.ext (fun j ↦ (e j).symm) fun j k f ↦ ?_
  simp only [ComposableArrows.whiskerLeft, Functor.comp_map]
  rw [← eqToHom_comp_iff (e j), ← he j (hle j), ← he k (hle k), ← s.map_comp, ← s.map_comp]
  exact congrArg s.map (Subsingleton.elim _ _)

/-- A simplex of the nerve lies in the image of the `i`-th degeneracy exactly when its `i`-th
arrow is an identity arrow. This generalizes Mathlib's `PartialOrder.mem_range_nerve_σ_iff`
(in `Mathlib/AlgebraicTopology/SimplicialSet/NerveNondegenerate.lean`) from partial orders to
arbitrary categories, and adapts its proof: the converse exhibits the simplex as the degeneracy
of its face (`σ_δ_castSucc_eq_self`). -/
theorem mem_range_σ_iff {n : ℕ} (s : ComposableArrows C (n + 1)) (i : Fin (n + 1)) :
    s ∈ Set.range ((nerve C).σ i) ↔
      s.totalArrow i.castSucc i.succ i.castSucc_le_succ ∈
        Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C) := by
  constructor
  · -- The `i`-th degeneracy repeats the `i`-th object, so its `i`-th arrow is an identity.
    rintro ⟨t, rfl⟩
    refine ⟨t.obj i, ((t.totalArrow_whiskerLeft _ _ _ _).trans ?_).symm⟩
    -- The degeneracy reindexes along `SimplexCategory.toCat.map (SimplexCategory.σ i)`, whose
    -- object map is `i.predAbove` by definition (as in Mathlib's `nerve.σ_obj`). Simp only unfolds
    -- that functor into a chain of forgetful functors, so `change` states the reduced positions.
    change t.totalArrow (i.predAbove i.castSucc) (i.predAbove i.succ) _ = _
    simp only [Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]
    exact ComposableArrows.totalArrow_self (n := n) t i
  · rintro ⟨x, hx⟩
    rw [ComposableArrows.totalArrow_def] at hx
    obtain ⟨rfl, hr, hh⟩ := Quiver.Total.ext_iff.1 hx
    dsimp only at hr hh
    exact ⟨_, σ_δ_castSucc_eq_self s (h := hr)
      (by simpa [comp_eqToHom_iff] using ((conj_eqToHom_iff_heq _ _ rfl hr).2 hh).symm)⟩

/-- The image of the `i`-th degeneracy is the set of strings whose `i`-th arrow is an identity
arrow: the `Set.range` form of `mem_range_σ_iff`. -/
theorem range_σ_eq_preimage {n : ℕ} (i : Fin (n + 1)) :
    Set.range ((nerve C).σ i) =
      (fun s : ComposableArrows C (n + 1) ↦ s.totalArrow i.castSucc i.succ i.castSucc_le_succ) ⁻¹'
        Set.range fun x : C ↦ (⟨x, x, 𝟙 x⟩ : Quiver.Total C) :=
  Set.ext fun s ↦ mem_range_σ_iff s i

end CategoryTheory.nerve
