/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Category.ULift
public import TauCeti.CategoryTheory.Category.ULift
public import TauCeti.CategoryTheory.ComposableArrows.Basic

/-!
# Basic properties and structural isomorphisms of the nerve of a category

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
(`CategoryTheory.nerve.δ_succ_precomp`); it commutes with repeating any vertex but the first one
(`CategoryTheory.nerve.σ_succ_precomp`). Dually, appending an arrow `g : σ.right ⟶ Y` with
`CategoryTheory.ComposableArrows.postcomp` is retracted by the final face
(`CategoryTheory.nerve.δ_last_postcomp`), and on simplices of positive dimension (`n + 1`, strings
of at least one arrow) deleting any earlier vertex deletes that vertex of `σ` and composes `g` with
the arrow from the new final vertex of `(nerve C).δ k σ` to `σ.right`
(`CategoryTheory.nerve.δ_castSucc_postcomp`, `CategoryTheory.nerve.δ_zero_postcomp`).

A `3`-simplex of the nerve is a sequence of three composable morphisms `ComposableArrows.mk₃ f g h`.
Its faces are the `2`-simplices obtained by dropping a vertex, whose arrows are composites of
consecutive arrows among `f`, `g` and `h`. This extends Mathlib's description of the faces of
`2`-simplices (`CategoryTheory.nerve.δ₀_mk₂_eq`, …).

We also record basic functoriality of `nerveMap`, nonemptiness and subsingleton properties of
`nerve C`, and structural isomorphisms identifying the nerves of discrete categories
(`nerve.discreteIso`), product categories (`nerve.prodIso`), universe-lifted categories
(`nerve.asSmallIso`), and finite nonempty ordinals (`nerve.finSuccIsoStdSimplex`). These serve as
simplicial inputs to classifying spaces and nerve homotopies.

## Main declarations

* `CategoryTheory.nerve.σ_δ_castSucc_eq_self`: a string whose `i`-th arrow is an identity is the
  `i`-th degeneracy of its `i`-th face.
* `CategoryTheory.nerve.mem_range_σ_iff`: the image of the `i`-th degeneracy consists of the
  strings whose `i`-th arrow is an identity.
* `CategoryTheory.nerve.δ_succ_precomp`, `CategoryTheory.nerve.σ_succ_precomp`: the faces and
  degeneracies of a string with a prepended arrow.
* `CategoryTheory.nerve.map_obj`, `CategoryTheory.nerve.totalArrow_map`,
  `CategoryTheory.nerve.map_const`: the objects, arrows and vertices of a reindexed simplex.
* `CategoryTheory.nerve.totalArrow_δ`, `CategoryTheory.nerve.δ_last_postcomp`,
  `CategoryTheory.nerve.δ_castSucc_postcomp`, `CategoryTheory.nerve.δ_zero_postcomp`: the arrows
  of a face and the faces of a string with an appended arrow.
* `CategoryTheory.nerve.δ₀_mk₃_eq`, …, `CategoryTheory.nerve.δ₃_mk₃_eq`: the faces of the
  `3`-simplex of the nerve given by three composable morphisms.
* `CategoryTheory.nerve.discreteIso`, `CategoryTheory.nerve.prodIso`,
  `CategoryTheory.nerve.asSmallIso`, `CategoryTheory.nerve.finSuccIsoStdSimplex`: structural
  isomorphisms in `SSet`.
* `CategoryTheory.nerveMap_app_nerveEquiv_symm`: the map of nerves induced by a functor sends the
  vertex of an object to the vertex of its image.
-/

public section

open CategoryTheory MonoidalCategory Opposite Simplicial
universe w v u
namespace CategoryTheory
section Functoriality
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
@[simp] lemma nerveMap_id (C : Type u) [Category.{v} C] : nerveMap (𝟭 C) = 𝟙 (nerve C) :=
  nerveFunctor.map_id (Cat.of C)
@[simp, reassoc] lemma nerveMap_comp (F : C ⥤ D) (G : D ⥤ E) :
    nerveMap (F ⋙ G) = nerveMap F ≫ nerveMap G :=
  nerveFunctor.map_comp F.toCatHom G.toCatHom
@[simp] lemma nerveMap_const (C : Type u) [Category.{v} C] {D : Type u} [Category.{v} D] (d : D) :
    nerveMap ((Functor.const C).obj d) = SSet.const (nerveEquiv.symm d) := by
  ext ⟨n⟩ σ : 4
  induction n using SimplexCategory.rec with | _ n =>
  exact Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ .rfl
end Functoriality

namespace nerve
section BasicProperties
variable {C : Type u} [Category.{v} C]
/-- `nerve C` is nonempty as a simplicial set if and only if `C` is nonempty. -/
@[simp] lemma nonempty_iff (C : Type u) [Category.{v} C] : (nerve C).Nonempty ↔ Nonempty C :=
  nerveEquiv.nonempty_congr
instance [Nonempty C] : (nerve C).Nonempty := (nonempty_iff C).2 ‹_›
instance [Subsingleton C] [Quiver.IsThin C] (n : SimplexCategoryᵒᵖ) :
    Subsingleton ((nerve C).obj n) :=
  ⟨fun _ _ ↦ ext_of_isThin (funext fun _ ↦ Subsingleton.elim _ _)⟩

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

/-- Repeating a vertex other than the first one of a string with a prepended arrow `b` repeats the
corresponding vertex of the original string, keeping `b` as the first arrow. -/
theorem σ_succ_precomp {n : ℕ} (i : Fin (n + 1)) (σ : ComposableArrows C n) {y : C}
    (b : y ⟶ σ.left) :
    (nerve C).σ i.succ (σ.precomp b) = ((nerve C).σ i σ).precomp b := by
  refine ComposableArrows.ext_succ_of_totalArrow
    ((nerve C).δ_comp_σ_of_le_apply (Fin.zero_le _) (σ.precomp b)) ?_
  refine (totalArrow_map (SimplexCategory.σ i.succ) (σ.precomp b) 0 1 (Fin.zero_le _)).trans ?_
  -- The degeneracy `σ i.succ` fixes the vertices `0` and `1`; rewriting the indices changes the
  -- dependent proof of `0 ≤ 1`, so `key` transports along them by `subst`.
  have key (j k : Fin (n + 2)) (hjk : j ≤ k) (hj : j = 0) (hk : k = 1) :
      (σ.precomp b).totalArrow j k hjk = (σ.precomp b).totalArrow 0 1 (Fin.zero_le _) := by
    subst hj hk
    rfl
  refine (key _ _ _ (by simp [SimplexCategory.σ]) ?_).trans ?_
  · simp [SimplexCategory.σ, Fin.predAbove, Fin.lt_def]
  -- By definition of `precomp`, both first arrows are `b`.
  rw [ComposableArrows.totalArrow_def, ComposableArrows.totalArrow_def]
  rfl

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

end BasicProperties

section StructuralIsos
/-- The nerve of `Discrete ι` is isomorphic to the constant simplicial set on `ι`. -/
def discreteIso (ι : Type u) :
    nerve (Discrete ι) ≅ (Functor.const SimplexCategoryᵒᵖ : Type u ⥤ SSet.{u}).obj ι :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso
    { toFun σ := (σ.obj 0).as, invFun i := (Functor.const _).obj ⟨i⟩
      left_inv σ := ext_of_isThin <| funext fun k ↦
        Discrete.ext (Discrete.eq_of_hom (σ.map (homOfLE (Fin.zero_le k))))
      right_inv _ := rfl })
    fun _ ↦ by ext σ; exact (Discrete.eq_of_hom (σ.map (homOfLE (Fin.zero_le _)))).symm
@[simp] lemma discreteIso_hom_app_apply {ι : Type u} {n : SimplexCategoryᵒᵖ}
    (σ : (nerve (Discrete ι)).obj n) : dsimp% (discreteIso ι).hom.app n σ = (σ.obj 0).as := (rfl)
@[simp] lemma discreteIso_inv_app_obj {ι : Type u} {n : SimplexCategoryᵒᵖ} (i : ι)
    (k : Fin (n.unop.len + 1)) : dsimp% (((discreteIso ι).inv.app n i).obj k) = ⟨i⟩ := (rfl)
lemma discreteIso_hom_app_nerveEquiv_symm {ι : Type u} (i : Discrete ι) :
    (discreteIso ι).hom.app (op ⦋0⦌) (nerveEquiv.symm i) = i.as := (rfl)
@[simp] lemma discreteIso_inv_app_zero {ι : Type u} (i : ι) :
    dsimp% (discreteIso ι).inv.app (op ⦋0⦌) i = nerveEquiv.symm ⟨i⟩ := ComposableArrows.ext₀ rfl
@[reassoc] lemma discreteIso_hom_naturality {ι κ : Type u} (f : ι → κ) :
    nerveMap (Discrete.functor (Discrete.mk ∘ f)) ≫ (discreteIso κ).hom =
      (discreteIso ι).hom ≫ (Functor.const SimplexCategoryᵒᵖ).map (TypeCat.ofHom f) := by
  ext ⟨m⟩ σ : 4; rfl
/-- The nerve of a product category `C × D` is isomorphic to `nerve C ⊗ nerve D`. -/
def prodIso (C D : Type u) [Category.{v} C] [Category.{v} D] :
    nerve (C × D) ≅ (nerve C ⊗ nerve D : SSet.{max u v}) :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso
    { toFun σ := (σ ⋙ CategoryTheory.Prod.fst C D, σ ⋙ CategoryTheory.Prod.snd C D)
      invFun p := p.1.prod' p.2, left_inv _ := Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ .rfl
      right_inv _ := Prod.ext (Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ .rfl)
        (Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ .rfl) }) fun _ ↦ rfl
@[simp] lemma prodIso_hom_app_fst {C D : Type u} [Category.{v} C] [Category.{v} D]
    {n : SimplexCategoryᵒᵖ} (σ : (nerve (C × D)).obj n) :
    dsimp% ((prodIso C D).hom.app n σ).1 = σ ⋙ CategoryTheory.Prod.fst C D := (rfl)
@[simp] lemma prodIso_hom_app_snd {C D : Type u} [Category.{v} C] [Category.{v} D]
    {n : SimplexCategoryᵒᵖ} (σ : (nerve (C × D)).obj n) :
    dsimp% ((prodIso C D).hom.app n σ).2 = σ ⋙ CategoryTheory.Prod.snd C D := (rfl)
@[simp] lemma prodIso_inv_app_apply {C D : Type u} [Category.{v} C] [Category.{v} D]
    {n : SimplexCategoryᵒᵖ} (p : (nerve C ⊗ nerve D : SSet.{max u v}).obj n) :
    dsimp% (prodIso C D).inv.app n p = p.1.prod' p.2 := (rfl)
@[reassoc (attr := simp)] lemma prodIso_hom_fst {C D : Type u} [Category.{v} C] [Category.{v} D] :
    (prodIso C D).hom ≫ CartesianMonoidalCategory.fst (nerve C) (nerve D) =
      nerveMap (CategoryTheory.Prod.fst C D) := by
  ext ⟨m⟩ σ : 4; exact Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ .rfl
@[reassoc (attr := simp)] lemma prodIso_hom_snd {C D : Type u} [Category.{v} C] [Category.{v} D] :
    (prodIso C D).hom ≫ CartesianMonoidalCategory.snd (nerve C) (nerve D) =
      nerveMap (CategoryTheory.Prod.snd C D) := by
  ext ⟨m⟩ σ : 4; exact Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ .rfl
@[reassoc] lemma prodIso_hom_naturality {C₁ C₂ D₁ D₂ : Type u} [Category.{v} C₁] [Category.{v} C₂]
    [Category.{v} D₁] [Category.{v} D₂] (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) :
    nerveMap (F₁.prod F₂) ≫ (prodIso D₁ D₂).hom =
      (prodIso C₁ C₂).hom ≫ (nerveMap F₁ ⊗ₘ nerveMap F₂) := by
  refine CategoryTheory.NatTrans.ext (funext fun ⟨m⟩ ↦ ?_)
  ext σ; rfl
/-- The nerve of `AsSmall.{w} C` is isomorphic to `SSet.uliftFunctor.obj (nerve C)`. -/
def asSmallIso (C : Type u) [Category.{v} C] :
    nerve (AsSmall.{w} C) ≅ SSet.uliftFunctor.{w, max u v}.obj (nerve C) :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso
    { toFun σ := ULift.up ((AsSmall.down.mapComposableArrows _).obj σ)
      invFun τ := (AsSmall.up.mapComposableArrows _).obj τ.down
      left_inv _ := Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ .rfl
      right_inv _ := ULift.ext <| Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ .rfl }) fun _ ↦ rfl
@[simp] lemma asSmallIso_hom_app_down {C : Type u} [Category.{v} C] {n : SimplexCategoryᵒᵖ}
    (σ : ComposableArrows (AsSmall.{w} C) n.unop.len) :
    ((asSmallIso.{w} C).hom.app n σ).down = (AsSmall.down.mapComposableArrows n.unop.len).obj σ :=
  (rfl)
@[simp] lemma asSmallIso_inv_app_apply {C : Type u} [Category.{v} C] {n : SimplexCategoryᵒᵖ}
    (τ : ULift.{w} (ComposableArrows C n.unop.len)) :
    (asSmallIso.{w} C).inv.app n τ = (AsSmall.up.mapComposableArrows n.unop.len).obj τ.down := (rfl)
@[simp] lemma asSmallIso_hom_app_nerveEquiv_symm {C : Type u} [Category.{v} C] (c : AsSmall.{w} C) :
    (asSmallIso.{w} C).hom.app (op ⦋0⦌) (nerveEquiv.symm c) =
      ULift.up (nerveEquiv.symm (AsSmall.down.obj c)) := ULift.ext (ComposableArrows.ext₀ rfl)
@[simp] lemma asSmallIso_inv_app_nerveEquiv_symm {C : Type u} [Category.{v} C] (c : C) :
    (asSmallIso.{w} C).inv.app (op ⦋0⦌) (ULift.up (nerveEquiv.symm c)) =
      nerveEquiv.symm (AsSmall.up.obj c) := ComposableArrows.ext₀ rfl
@[reassoc] lemma asSmallIso_hom_naturality {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) :
    nerveMap (AsSmall.down ⋙ F ⋙ AsSmall.up : AsSmall.{w} C ⥤ AsSmall.{w} D) ≫
        (asSmallIso.{w} D).hom =
      (asSmallIso.{w} C).hom ≫ SSet.uliftFunctor.{w, max u v}.map (nerveMap F) := by
  ext ⟨m⟩ σ : 4; exact ULift.ext <| Functor.hext (fun _ ↦ rfl) fun _ _ _ ↦ .rfl
/-- The nerve of `Fin (n + 1)` is isomorphic to the standard `n`-simplex `Δ[n]` in `SSet.{0}`. -/
def finSuccIsoStdSimplex (n : ℕ) : nerve (Fin (n + 1)) ≅ (Δ[n] : SSet.{0}) :=
  (SSet.stdSimplex.isoOfRepresentableBy (representableBy (Fin (n + 1)) (.refl _))).symm
@[simp] lemma finSuccIsoStdSimplex_hom_app_apply {n d : ℕ} (σ : (nerve (Fin (n + 1))) _⦋d⦌)
    (i : Fin (d + 1)) : dsimp% (finSuccIsoStdSimplex n).hom.app _ σ i = σ.obj i := (rfl)
@[simp] lemma finSuccIsoStdSimplex_inv_app_obj {n d : ℕ} (s : (Δ[n] : SSet.{0}) _⦋d⦌)
    (i : Fin (d + 1)) : dsimp% ((finSuccIsoStdSimplex n).inv.app _ s).obj i = s i := (rfl)
@[simp] lemma finSuccIsoStdSimplex_hom_app_nerveEquiv_symm (n : ℕ) (i : Fin (n + 1)) :
    (finSuccIsoStdSimplex n).hom.app (op ⦋0⦌) (nerveEquiv.symm i) =
      SSet.stdSimplex.const n i (op ⦋0⦌) := by ext k : 3; fin_cases k; rfl
@[simp] lemma finSuccIsoStdSimplex_inv_app_const_zero (n : ℕ) (i : Fin (n + 1)) :
    (finSuccIsoStdSimplex n).inv.app (op ⦋0⦌) (SSet.stdSimplex.const n i (op ⦋0⦌)) =
      nerveEquiv.symm i := ComposableArrows.ext₀ rfl
end StructuralIsos
end nerve

/-- The map of nerves induced by a functor `F` sends the vertex of an object `X` to the vertex of
`F.obj X`: Mathlib's `nerveMap_app_mk₀`, stated for vertices written with `nerveEquiv`. -/
@[simp]
lemma nerveMap_app_nerveEquiv_symm {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D)
    (X : C) : (nerveMap F).app (Opposite.op ⦋0⦌) (nerveEquiv.symm X) = nerveEquiv.symm (F.obj X) :=
  nerveMap_app_mk₀ F X

end CategoryTheory
