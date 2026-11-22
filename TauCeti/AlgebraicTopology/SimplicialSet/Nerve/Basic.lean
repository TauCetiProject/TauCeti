/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Discrete.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.ULift
public import TauCeti.CategoryTheory.ComposableArrows.Basic

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
(`CategoryTheory.nerve.δ_succ_precomp`). Dually, appending an arrow `g : σ.right ⟶ Y` with
`CategoryTheory.ComposableArrows.postcomp` is retracted by the final face
(`CategoryTheory.nerve.δ_last_postcomp`), and on simplices of positive dimension (`n + 1`, strings
of at least one arrow) deleting any earlier vertex deletes that vertex of `σ` and composes `g` with
the arrow from the new final vertex of `(nerve C).δ k σ` to `σ.right`
(`CategoryTheory.nerve.δ_castSucc_postcomp`, `CategoryTheory.nerve.δ_zero_postcomp`).

A `3`-simplex of the nerve is a sequence of three composable morphisms `ComposableArrows.mk₃ f g h`.
Its faces are the `2`-simplices obtained by dropping a vertex, whose arrows are composites of
consecutive arrows among `f`, `g` and `h`. This extends Mathlib's description of the faces of
`2`-simplices (`CategoryTheory.nerve.δ₀_mk₂_eq`, …).

We also record basic functoriality and identifications of nerves: `TauCeti.nerveMap_injective` shows
that `nerveMap` is injective on functors (in arbitrary object and morphism universes),
`TauCeti.nerveMap_const` identifies the nerve map of a constant functor with `SSet.const`,
`CategoryTheory.nerve.asSmallIso` identifies `nerve (AsSmall C)` with
`SSet.uliftFunctor.obj (nerve C)`, and `CategoryTheory.nerve.isDiscreteIso` identifies the nerve of
a discrete category with a constant simplicial set.

## Main declarations

* `CategoryTheory.nerve.σ_δ_castSucc_eq_self`: a string whose `i`-th arrow is an identity is the
  `i`-th degeneracy of its `i`-th face.
* `CategoryTheory.nerve.mem_range_σ_iff`: the image of the `i`-th degeneracy consists of the
  strings whose `i`-th arrow is an identity.
* `CategoryTheory.nerve.δ_succ_precomp`: the faces of a string with a prepended arrow.
* `CategoryTheory.nerve.map_obj`, `CategoryTheory.nerve.totalArrow_map`,
  `CategoryTheory.nerve.map_const`: the objects, arrows and vertices of a reindexed simplex.
* `CategoryTheory.nerve.totalArrow_δ`, `CategoryTheory.nerve.δ_last_postcomp`,
  `CategoryTheory.nerve.δ_castSucc_postcomp`, `CategoryTheory.nerve.δ_zero_postcomp`: the arrows
  of a face and the faces of a string with an appended arrow.
* `CategoryTheory.nerve.δ₀_mk₃_eq`, …, `CategoryTheory.nerve.δ₃_mk₃_eq`: the faces of the
  `3`-simplex of the nerve given by three composable morphisms.
* `CategoryTheory.nerve.objEquiv`, `CategoryTheory.nerve.asSmallIso`,
  `CategoryTheory.nerve.isDiscreteIso`: simplex equivalence for `nerve C` and nerves of
  `AsSmall C` and discrete categories.
* `TauCeti.nerveMap_injective`, `TauCeti.nerveMap_const`: injectivity of `nerveMap` (extending
  `CategoryTheory.nerveFunctor.faithful` from `Cat.{u, u}` to `Cat.{v, u}`) and action on constant
  functors.
-/

public section

open CategoryTheory Opposite Simplicial

universe w v u

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

/-- The `k`-th face of a simplex of the nerve reindexes its arrows along `k.succAbove`. -/
@[simp]
theorem totalArrow_δ {n : ℕ} (k : Fin (n + 2)) (σ : ComposableArrows C (n + 1))
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    ((nerve C).δ k σ).totalArrow i j hij =
      σ.totalArrow (k.succAbove i) (k.succAbove j) ((Fin.strictMono_succAbove k).monotone hij) :=
  totalArrow_map (SimplexCategory.δ k) σ i j hij

/-- The `i`-th vertex of a simplex `s` of the nerve is the `0`-simplex given by `s.obj i`. -/
lemma map_const {n : ℕ} (s : ComposableArrows C n) (i : Fin (n + 1)) :
    (nerve C).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op s = nerveEquiv.symm (s.obj i) :=
  ComposableArrows.ext₀ rfl

end Map

/-- Deleting the last vertex of `σ.postcomp g` recovers `σ`. -/
@[simp] theorem δ_last_postcomp {n : ℕ} (σ : ComposableArrows C n) {Y : C} (g : σ.right ⟶ Y) :
    (nerve C).δ (Fin.last (n + 1)) (σ.postcomp g) = σ := by
  refine ComposableArrows.ext_of_totalArrow (n := n) fun i j hij ↦ ?_
  rw [totalArrow_δ]; simpa only [Fin.succAbove_last] using σ.totalArrow_postcomp_castSucc g i j hij

/-- On a positive-dimensional simplex `σ : ComposableArrows C (n + 1)` (at least one arrow), any
non-last face `δ k.castSucc` of `σ.postcomp g` deletes vertex `k` of `σ` and composes `g` with the
arrow of `σ` from `k.succAbove (Fin.last n)` to `σ.right`, dual to `δ_succ_precomp`. -/
@[simp] theorem δ_castSucc_postcomp {n : ℕ} (k : Fin (n + 2)) (σ : ComposableArrows C (n + 1))
    {Y : C} (g : σ.right ⟶ Y) : (nerve C).δ k.castSucc (σ.postcomp g) = ((nerve C).δ k σ).postcomp
      (σ.map (homOfLE (Fin.le_last (k.succAbove (Fin.last n)))) ≫ g) := by
  set τ : ComposableArrows C n := (nerve C).δ k σ
  set g' : τ.right ⟶ Y := σ.map (homOfLE (Fin.le_last (k.succAbove (Fin.last n)))) ≫ g
  refine ComposableArrows.ext_of_totalArrow (n := n + 1) fun i j hij ↦ ?_
  rw [totalArrow_δ]; cases j using Fin.lastCases with
  | cast j₀ =>
    cases i using Fin.lastCases with
    | last => exact absurd hij (not_le_of_gt (Fin.castSucc_lt_last j₀))
    | cast i₀ =>
      have hij₀ : i₀ ≤ j₀ := Fin.castSucc_le_castSucc_iff.mp hij
      simp only [Fin.castSucc_succAbove_castSucc]
      rw [σ.totalArrow_postcomp_castSucc g (k.succAbove i₀) (k.succAbove j₀)
        ((Fin.strictMono_succAbove k).monotone hij₀),
        τ.totalArrow_postcomp_castSucc g' i₀ j₀ hij₀, ← totalArrow_δ]
  | last =>
    have hkl : k.castSucc.succAbove (Fin.last (n + 1)) = Fin.last (n + 2) :=
      (Fin.succAbove_of_le_castSucc _ _
        (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last k))).trans (Fin.succ_last _)
    cases i using Fin.lastCases with
    | last =>
      simp only [hkl, ComposableArrows.totalArrow_self]
      exact congrArg (fun Z ↦ ({ left := Z, right := Z, hom := 𝟙 Z } : Quiver.Total C))
        ((σ.postcomp_obj_last g).trans (τ.postcomp_obj_last g').symm)
    | cast i₀ =>
      simp only [hkl, Fin.castSucc_succAbove_castSucc,
        ComposableArrows.totalArrow_postcomp_castSucc_last]
      rw [Subsingleton.elim hij (Fin.le_last _), τ.totalArrow_postcomp_castSucc_last g']
      refine Quiver.Total.ext rfl rfl (heq_of_eq ?_)
      have hτ : τ.map (homOfLE (Fin.le_last i₀)) =
          σ.map (homOfLE ((Fin.strictMono_succAbove k).monotone (Fin.le_last i₀))) :=
        congrArg σ.map (Subsingleton.elim _ _)
      exact ((congrArg (σ.map · ≫ g) (Subsingleton.elim _ _)).trans
        (σ.map_comp_assoc _ _ g)).trans (congrArg (· ≫ g') hτ.symm)

/-- On positive-dimensional `σ : ComposableArrows C (n + 1)`, `δ 0` commutes with `postcomp g`. -/
@[simp] theorem δ_zero_postcomp {n : ℕ} (σ : ComposableArrows C (n + 1)) {Y : C}
    (g : σ.right ⟶ Y) : (nerve C).δ 0 (σ.postcomp g) = ((nerve C).δ 0 σ).postcomp g := by
  have h := δ_castSucc_postcomp 0 σ g; rw [Fin.castSucc_zero] at h
  refine h.trans (congrArg (((nerve C).δ 0 σ).postcomp) ?_)
  have hid := (congrArg σ.map (Subsingleton.elim
    (homOfLE (Fin.le_last ((0 : Fin (n + 2)).succAbove (Fin.last n))))
    (𝟙 (Fin.last (n + 1))))).trans (σ.map_id _)
  exact (congrArg (· ≫ g) hid).trans (Category.id_comp g)

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

/-- Equivalence `(nerve C) _⦋n⦌ ≃ ComposableArrows C n` on `n`-simplices of `nerve C`, mirroring
`SSet.stdSimplex.objEquiv` under `implicit` transparency. -/
def objEquiv {C : Type u} [Category.{v} C] {n : ℕ} : (nerve C) _⦋n⦌ ≃ ComposableArrows C n :=
  Equiv.refl _

theorem objEquiv_eq {n : ℕ} (s : (nerve C) _⦋n⦌) : objEquiv s = (s : ComposableArrows C n) := (rfl)

theorem objEquiv_symm_eq {n : ℕ} (s : ComposableArrows C n) :
    objEquiv.symm s = (s : (nerve C) _⦋n⦌) := (rfl)

@[simp] theorem objEquiv_nerveMap_app {D : Type u} [Category.{v} D] (F : C ⥤ D) {n : ℕ}
    (s : (nerve C) _⦋n⦌) :
    objEquiv ((nerveMap F).app (op ⦋n⦌) s) = (F.mapComposableArrows n).obj (objEquiv s) := (rfl)

@[simp] theorem nerveMap_app_objEquiv_symm {D : Type u} [Category.{v} D] (F : C ⥤ D) {n : ℕ}
    (s : ComposableArrows C n) :
    (nerveMap F).app (op ⦋n⦌) (objEquiv.symm s) = objEquiv.symm ((F.mapComposableArrows n).obj s) :=
  (rfl)

@[simp] theorem objEquiv_map {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (s : (nerve C) _⦋n⦌) :
    objEquiv ((nerve C).map f.op s) =
      (objEquiv s).whiskerLeft (SimplexCategory.toCat.map f).toFunctor := (rfl)

@[simp] theorem map_objEquiv_symm {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (s : ComposableArrows C n) :
    (nerve C).map f.op (objEquiv.symm s) =
      objEquiv.symm (s.whiskerLeft (SimplexCategory.toCat.map f).toFunctor) := (rfl)

@[simp] theorem objEquiv_δ {n : ℕ} (i : Fin (n + 2)) (s : (nerve C) _⦋n + 1⦌) :
    objEquiv ((nerve C).δ i s) =
      (objEquiv s).whiskerLeft (Fin.strictMono_succAbove i).monotone.functor := (rfl)

@[simp] theorem δ_objEquiv_symm {n : ℕ} (i : Fin (n + 2)) (s : ComposableArrows C (n + 1)) :
    (nerve C).δ i (objEquiv.symm s) =
      objEquiv.symm (s.whiskerLeft (Fin.strictMono_succAbove i).monotone.functor) := (rfl)

@[simp] theorem objEquiv_σ {n : ℕ} (i : Fin (n + 1)) (s : (nerve C) _⦋n⦌) :
    objEquiv ((nerve C).σ i s) =
      (objEquiv s).whiskerLeft (Fin.predAbove_right_monotone i).functor := (rfl)

@[simp] theorem σ_objEquiv_symm {n : ℕ} (i : Fin (n + 1)) (s : ComposableArrows C n) :
    (nerve C).σ i (objEquiv.symm s) =
      objEquiv.symm (s.whiskerLeft (Fin.predAbove_right_monotone i).functor) := (rfl)

theorem _root_.CategoryTheory.nerveEquiv_symm_eq_mk₀ (X : C) :
    nerveEquiv.symm X = ComposableArrows.mk₀ X := (rfl)

theorem _root_.CategoryTheory.nerveEquiv_symm_eq_const (X : C) :
    nerveEquiv.symm X = (Functor.const (Fin 1)).obj X :=
  ComposableArrows.ext (fun _ ↦ rfl) (fun _ h ↦ (Nat.not_lt_zero _ h).elim)

@[simp] theorem _root_.CategoryTheory.nerveEquiv_symm_obj (X : C) (i : Fin 1) :
    (nerveEquiv.symm X).obj i = X := (rfl)

/-- Applying a functor `F` to the `0`-simplex `nerveEquiv.symm X` gives
`nerveEquiv.symm (F.obj X)`. -/
@[simp] theorem _root_.CategoryTheory.Functor.mapComposableArrows_obj_nerveEquiv_symm
    {D : Type*} [Category* D] (F : C ⥤ D) (X : C) :
    (F.mapComposableArrows 0).obj (nerveEquiv.symm X) = nerveEquiv.symm (F.obj X) := by
  rw [nerveEquiv_symm_eq_mk₀, Functor.mapComposableArrows_obj_mk₀, ← nerveEquiv_symm_eq_mk₀]

@[simp] theorem representableBy_homEquiv_const_zero {n : ℕ} {α : Type u} [Preorder α]
    (e : α ≃o Fin (n + 1)) (i : Fin (n + 1)) :
    (representableBy α e).homEquiv (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) =
      objEquiv.symm (nerveEquiv.symm (e.symm i)) :=
  objEquiv.injective <| ComposableArrows.ext (fun j ↦ by fin_cases j; rfl)
    (fun _ _ ↦ Subsingleton.elim _ _)

/-- The nerve of `AsSmall.{w} C` is isomorphic to the universe lift of `nerve C`. -/
def asSmallIso (C : Type u) [Category.{v} C] :
    nerve (AsSmall.{w} C) ≅ SSet.uliftFunctor.{w, max u v}.obj (nerve C) where
  hom := { app m := ↾fun s ↦ ULift.up ((AsSmall.down.mapComposableArrows m.unop.len).obj s) }
  inv := { app m := ↾fun s ↦ (AsSmall.up.mapComposableArrows m.unop.len).obj s.down }

@[simp] lemma asSmallIso_hom_app {C : Type u} [Category.{v} C] {n : ℕ}
    (s : (nerve (AsSmall.{w} C)) _⦋n⦌) :
    (asSmallIso.{w} C).hom.app (op ⦋n⦌) s =
      (nerve C).uliftFunctorObjEquiv (op ⦋n⦌)
        (objEquiv.symm ((AsSmall.down.mapComposableArrows n).obj (objEquiv s))) :=
  ULift.ext ((nerve C).uliftFunctorObjEquiv_down _ _).symm

@[simp] lemma asSmallIso_inv_app {C : Type u} [Category.{v} C] {n : ℕ}
    (s : (SSet.uliftFunctor.{w, max u v}.obj (nerve C)) _⦋n⦌) :
    (asSmallIso.{w} C).inv.app (op ⦋n⦌) s =
      objEquiv.symm ((AsSmall.up.mapComposableArrows n).obj
        (objEquiv (((nerve C).uliftFunctorObjEquiv (op ⦋n⦌)).symm s))) := by
  rw [SSet.uliftFunctorObjEquiv_symm_eq_down, objEquiv_eq, objEquiv_symm_eq]
  -- Unfolds `asSmallIso.inv` (`TypeCat.ofHom_apply`) to
  -- `(AsSmall.up.mapComposableArrows n).obj s.down`.
  rfl

/-- The nerve of any discrete category `C` (`[IsDiscrete C]`) is isomorphic to the constant
simplicial set on `ULift.{v} C`. -/
def isDiscreteIso (C : Type u) [Category.{v} C] [IsDiscrete C] :
    nerve C ≅ (Functor.const SimplexCategoryᵒᵖ).obj (ULift.{v} C) where
  hom :=
    { app _ := ↾fun F ↦ ULift.up (F.obj 0)
      naturality _ _ _ := ConcreteCategory.hom_ext _ _ fun F ↦ by
        dsimp [nerve, Functor.const]
        exact ULift.ext (IsDiscrete.eq_of_hom (F.map (homOfLE (Fin.zero_le _)))).symm }
  inv := { app m := ↾fun x ↦ (Functor.const (Fin (m.unop.len + 1))).obj x.down }
  hom_inv_id := by
    ext ⟨⟨n⟩⟩ F : 4
    exact ComposableArrows.ext (fun i ↦ IsDiscrete.eq_of_hom (F.map (homOfLE (Fin.zero_le i))))
      (fun _ _ ↦ Subsingleton.elim _ _)

@[simp] lemma isDiscreteIso_hom_app {C : Type u} [Category.{v} C] [IsDiscrete C] {n : ℕ}
    (s : (nerve C) _⦋n⦌) :
    dsimp% (isDiscreteIso C).hom.app (op ⦋n⦌) s = ULift.up ((objEquiv s).obj 0) := (rfl)

@[simp] lemma isDiscreteIso_inv_app {C : Type u} [Category.{v} C] [IsDiscrete C] {n : ℕ}
    (x : ULift.{v} C) :
    dsimp% (isDiscreteIso C).inv.app (op ⦋n⦌) x =
      objEquiv.symm ((Functor.const (Fin (n + 1))).obj x.down) := (rfl)

end CategoryTheory.nerve

namespace TauCeti

/-- `nerveMap` is injective on functors in arbitrary object and morphism universes, extending
`CategoryTheory.nerveFunctor.faithful` from `Cat.{u, u}` to `Cat.{v, u}`. -/
theorem nerveMap_injective {C D : Type u} [Category.{v} C] [Category.{v} D] :
    Function.Injective (nerveMap : (C ⥤ D) → (nerve C ⟶ nerve D)) := fun F G h ↦ by
  have h₁ {X Y : C} (f : X ⟶ Y) : Arrow.mk (F.map f) = Arrow.mk (G.map f) := by
    rw [← ComposableArrows.mk₁_eq_mk₁_iff, ← nerveMap_app_mk₁, ← nerveMap_app_mk₁, h]
  refine CategoryTheory.Functor.ext (fun X ↦ congr($(h₁ (𝟙 X)).left)) fun X Y f ↦ ?_
  obtain ⟨_, _, hf⟩ := (Arrow.mk_eq_mk_iff _ _).1 (h₁ f); exact hf

/-- `nerveFunctor` is faithful in arbitrary object and morphism universes. -/
instance : nerveFunctor.{v, u}.Faithful where
  map_injective h := Cat.Hom.ext (nerveMap_injective h)

/-- The nerve map of `(Functor.const C).obj Y` is the constant simplicial map at `Y`. -/
@[simp] theorem nerveMap_const (C D : Type u) [Category.{v} C] [Category.{v} D] (Y : D) :
    nerveMap ((Functor.const C).obj Y) = SSet.const (nerve.objEquiv.symm (nerveEquiv.symm Y)) :=
  SSet.hom_ext fun ⟨⟨n⟩⟩ ↦ ConcreteCategory.hom_ext _ _ fun s ↦
    nerve.objEquiv.injective <| ComposableArrows.ext_of_totalArrow fun _ _ _ ↦ by
      simp [SSet.const_app, nerveEquiv_symm_eq_mk₀, ComposableArrows.totalArrow_def,
        ComposableArrows.mk₀, ComposableArrows.whiskerLeft]

end TauCeti
