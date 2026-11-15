/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import TauCeti.CategoryTheory.ComposableArrows.Postcomp

/-!
# Arrows and faces of simplices of the nerve, and the images of its degeneracies

An `n`-simplex of the nerve `CategoryTheory.nerve C` of a category is a string
`F : ComposableArrows C n` of composable arrows. For positions `i ≤ j` its arrow from the `i`-th
to the `j`-th object, viewed as a total arrow of `C`, is `F.totalArrow i j hij` (defined in
`TauCeti.CategoryTheory.ComposableArrows.Basic`), and the simplicial operators of the nerve
reindex these arrows (`CategoryTheory.ComposableArrows.totalArrow_whiskerLeft`, stated for the
nerve, together with its effect on objects and vertices, as `CategoryTheory.nerve.totalArrow_map`,
`CategoryTheory.nerve.map_obj` and `CategoryTheory.nerve.map_const`).

An `n + 1`-simplex of the nerve lies in the image of the `i`-th degeneracy exactly when its
`i`-th arrow is an identity arrow (`CategoryTheory.nerve.mem_range_σ_iff`, in `Set.range` form
`CategoryTheory.nerve.range_σ_eq_preimage`). This generalizes, and adapts the proof of, Mathlib's
`PartialOrder.mem_range_nerve_σ_iff` from partial orders to arbitrary categories.

Prepending an arrow `b` to a string commutes with deleting any vertex but the first two, and
deleting the second vertex composes `b` with the first arrow of the string
(`CategoryTheory.nerve.δ_succ_precomp`). Dually, appending an arrow `g` at the right end of a
string recovers the original string under the last face (`CategoryTheory.nerve.δ_last_postcomp`),
commutes with every non-last face when the target is terminal
(`CategoryTheory.nerve.δ_castSucc_postcomp_isTerminal`), and has zeroth face `mk₀ Y` on
`0`-simplices (`CategoryTheory.nerve.δ_zero_postcomp_zero`).

A `3`-simplex of the nerve is a sequence of three composable morphisms `ComposableArrows.mk₃ f g h`.
Its faces are the `2`-simplices obtained by dropping a vertex, whose arrows are composites of
consecutive arrows among `f`, `g` and `h`. This extends Mathlib's description of the faces of
`2`-simplices (`CategoryTheory.nerve.δ₀_mk₂_eq`, …).

## Main declarations

* `CategoryTheory.nerve.σ_δ_castSucc_eq_self`: a string whose `i`-th arrow is an identity is the
  `i`-th degeneracy of its `i`-th face.
* `CategoryTheory.nerve.mem_range_σ_iff`: the image of the `i`-th degeneracy consists of the
  strings whose `i`-th arrow is an identity.
* `CategoryTheory.nerve.δ_succ_precomp`, `CategoryTheory.nerve.δ_last_postcomp`,
  `CategoryTheory.nerve.δ_castSucc_postcomp_isTerminal`: the faces of strings with a prepended or
  appended arrow.
* `CategoryTheory.nerve.map_obj`, `CategoryTheory.nerve.totalArrow_map`,
  `CategoryTheory.nerve.map_const`: the objects, arrows and vertices of a reindexed simplex.
* `CategoryTheory.nerve.δ₀_mk₃_eq`, …, `CategoryTheory.nerve.δ₃_mk₃_eq`: the faces of the
  `3`-simplex of the nerve given by three composable morphisms.
-/

public section

open CategoryTheory Limits Simplicial

universe v u

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
arbitrary categories. -/
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
  · -- Adapting Mathlib's proof, exhibit the simplex as the degeneracy of its face
    -- (`σ_δ_castSucc_eq_self`).
    rintro ⟨x, hx⟩
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

/-- Deleting a vertex other than the first one from a string with a prepended arrow `b` deletes
the corresponding vertex of the original string. If that vertex was the first one, the prepended
arrow is composed with the deleted arrow, so in all cases `b` is followed by the arrow from the
first vertex to the new second vertex. -/
theorem δ_succ_precomp {n : ℕ} (j : Fin (n + 2)) (σ : ComposableArrows C (n + 1)) {y : C}
    (b : y ⟶ σ.left) :
    (nerve C).δ j.succ (σ.precomp b) =
      ((nerve C).δ j σ).precomp (b ≫ σ.map (homOfLE (Fin.zero_le (j.succAbove 0)))) := by
  refine ComposableArrows.ext_succ_of_totalArrow
    ((nerve C).δ_comp_δ_apply (Fin.zero_le j) (σ.precomp b)) ?_
  -- The face reindexes along `j.succ.succAbove`, which fixes `0` and sends `1` to the
  -- successor of `j.succAbove 0`.
  refine ((σ.precomp b).totalArrow_whiskerLeft _ 0 1 (Fin.zero_le _)).trans ?_
  -- The reindexing functor acts on objects by `j.succ.succAbove` by definition (as in
  -- `nerve.δ_obj`); `simp` only unfolds it into forgetful functors, so `change` states this.
  change (σ.precomp b).totalArrow (j.succ.succAbove 0) (j.succ.succAbove 1) _ = _
  simp only [Fin.succ_succAbove_zero, Fin.succ_succAbove_one,
    ComposableArrows.totalArrow_precomp_zero_succ]
  -- By definition of `precomp`, the first arrow of the right-hand side is the prepended one.
  rw [ComposableArrows.totalArrow_def]
  rfl

section Map

/-! The nerve reindexes a string along `f : ⦋m⦌ ⟶ ⦋n⦌` by whiskering with the functor
`SimplexCategory.toCat.map f`, which acts on objects by `f.toOrderHom`. The lemmas below state
this once, for objects, arrows and vertices. -/

/-- Reindexing a simplex of the nerve along `f` reindexes its objects along `f`. -/
lemma map_obj {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (s : ComposableArrows C n) (i : Fin (m + 1)) :
    ((nerve C).map f.op s).obj i = s.obj (f.toOrderHom i) :=
  rfl

/-- Reindexing a simplex of the nerve along `f` reindexes its arrows along `f`. -/
lemma totalArrow_map {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (s : ComposableArrows C n) (i j : Fin (m + 1))
    (hij : i ≤ j) :
    ((nerve C).map f.op s).totalArrow i j hij =
      s.totalArrow (f.toOrderHom i) (f.toOrderHom j) (f.toOrderHom.monotone hij) :=
  s.totalArrow_whiskerLeft _ i j hij

/-- The `i`-th vertex of a simplex `s` of the nerve is the `0`-simplex given by `s.obj i`. -/
lemma map_const {n : ℕ} (s : ComposableArrows C n) (i : Fin (n + 1)) :
    (nerve C).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op s = nerveEquiv.symm (s.obj i) :=
  ComposableArrows.ext₀ rfl

end Map

section Postcomp

private lemma totalArrow_δ {m : ℕ} (i : Fin (m + 2)) (F : ComposableArrows C (m + 1))
    (a b : Fin (m + 1)) (hab : a ≤ b) :
    ((nerve C).δ i F).totalArrow a b hab =
      F.totalArrow (i.succAbove a) (i.succAbove b) ((Fin.strictMono_succAbove i).monotone hab) :=
  totalArrow_map (SimplexCategory.δ i) F a b hab

private lemma totalArrow_congr_idx {m : ℕ} (F : ComposableArrows C m) {a a' b b' : Fin (m + 1)}
    (ha : a = a') (hb : b = b') (hab : a ≤ b) :
    F.totalArrow a b hab = F.totalArrow a' b' (ha ▸ hb ▸ hab) := by subst ha; subst hb; rfl

/-- The last face of `F.postcomp g` in `nerve C` is `F`. -/
@[simp] theorem δ_last_postcomp {n : ℕ} (F : ComposableArrows C n) {Y : C} (g : F.right ⟶ Y) :
    (nerve C).δ (Fin.last (n + 1)) (F.postcomp g) = F :=
  ComposableArrows.ext_of_totalArrow fun i j hij ↦ by
    rw [totalArrow_δ, totalArrow_congr_idx _ (Fin.succAbove_last_apply i)
      (Fin.succAbove_last_apply j)]
    exact F.totalArrow_postcomp_castSucc_castSucc g i j hij

/-- When `t` is terminal, every non-last face `δ k.castSucc` commutes with appending the unique
morphism to `t`. -/
theorem δ_castSucc_postcomp_isTerminal {n : ℕ} (F : ComposableArrows C (n + 1)) {t : C}
    (ht : IsTerminal t) (k : Fin (n + 2)) :
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
          (G.postcomp (ht.from G.right)).obj (Fin.last (n + 1)) :=
        (F.postcomp_obj_last _).trans (G.postcomp_obj_last _).symm
      exact Quiver.Total.ext hlast hlast ((conj_eqToHom_iff_heq _ _ hlast hlast).mp (by simp [G]))
    | cast i =>
      rw [totalArrow_congr_idx _ Fin.castSucc_succAbove_castSucc hl,
        ComposableArrows.totalArrow_postcomp_castSucc_last, G.totalArrow_postcomp_castSucc_last]
      exact Quiver.Total.ext rfl rfl ((conj_eqToHom_iff_heq _ _ rfl rfl).mp (ht.hom_ext _ _))
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
@[simp] theorem δ_zero_postcomp_zero (σ : ComposableArrows C 0) {Y : C} (g : σ.right ⟶ Y) :
    (nerve C).δ 0 (σ.postcomp g) = ComposableArrows.mk₀ Y :=
  ComposableArrows.ext₀ (σ.postcomp_obj_last g)

end Postcomp

section Faces

variable {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)

/-! The arrows of each face of `mk₃ f g h` are, by definition of `mk₃`, composites of consecutive
arrows among `f`, `g` and `h`, so the faces are determined by `ComposableArrows.ext₂_of_arrow`. -/

/-- The face of `mk₃ f g h` opposite to the vertex `0`. -/
@[simp]
theorem δ₀_mk₃_eq :
    (nerve C).δ 0 (ComposableArrows.mk₃ f g h) = ComposableArrows.mk₂ g h :=
  ComposableArrows.ext₂_of_arrow rfl rfl

/-- The face of `mk₃ f g h` opposite to the vertex `1`. -/
@[simp]
theorem δ₁_mk₃_eq :
    (nerve C).δ 1 (ComposableArrows.mk₃ f g h) = ComposableArrows.mk₂ (f ≫ g) h :=
  ComposableArrows.ext₂_of_arrow rfl rfl

/-- The face of `mk₃ f g h` opposite to the vertex `2`. -/
@[simp]
theorem δ₂_mk₃_eq :
    (nerve C).δ 2 (ComposableArrows.mk₃ f g h) = ComposableArrows.mk₂ f (g ≫ h) :=
  ComposableArrows.ext₂_of_arrow rfl rfl

/-- The face of `mk₃ f g h` opposite to the vertex `3`. -/
@[simp]
theorem δ₃_mk₃_eq :
    (nerve C).δ 3 (ComposableArrows.mk₃ f g h) = ComposableArrows.mk₂ f g :=
  ComposableArrows.ext₂_of_arrow rfl rfl

end Faces

end CategoryTheory.nerve
