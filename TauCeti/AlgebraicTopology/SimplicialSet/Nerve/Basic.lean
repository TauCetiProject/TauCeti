/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import TauCeti.CategoryTheory.ComposableArrows.Basic

/-!
# Arrows and faces of simplices of the nerve, and the images of its degeneracies

An `n`-simplex of the nerve `CategoryTheory.nerve C` of a category is a string
`F : ComposableArrows C n` of composable arrows. For positions `i ≤ j` its arrow from the `i`-th
to the `j`-th object, viewed as a total arrow of `C`, is `F.totalArrow i j hij` (defined in
`TauCeti.CategoryTheory.ComposableArrows.Basic`), and the simplicial operators of the nerve
reindex these arrows (`CategoryTheory.ComposableArrows.totalArrow_whiskerLeft`).

An `n + 1`-simplex of the nerve lies in the image of the `i`-th degeneracy exactly when its
`i`-th arrow is an identity arrow (`CategoryTheory.nerve.mem_range_σ_iff`, in `Set.range` form
`CategoryTheory.nerve.range_σ_eq_preimage`). This generalizes, and adapts the proof of, Mathlib's
`PartialOrder.mem_range_nerve_σ_iff` from partial orders to arbitrary categories.

Prepending an arrow `b` to a string commutes with deleting any vertex but the first two, and
deleting the second vertex composes `b` with the first arrow of the string
(`CategoryTheory.nerve.δ_succ_precomp`). Dually, appending a terminal object with
`CategoryTheory.ComposableArrows.snocTerminal` is retracted by the final face
(`CategoryTheory.nerve.δ_last_snocTerminal`) and commutes with all earlier faces
(`CategoryTheory.nerve.δ_castSucc_snocTerminal`).

A `3`-simplex of the nerve is a sequence of three composable morphisms `ComposableArrows.mk₃ f g h`.
Its faces are the `2`-simplices obtained by dropping a vertex, whose arrows are composites of
consecutive arrows among `f`, `g` and `h`. This extends Mathlib's description of the faces of
`2`-simplices (`CategoryTheory.nerve.δ₀_mk₂_eq`, …).

## Main declarations

* `CategoryTheory.nerve.σ_δ_castSucc_eq_self`: a string whose `i`-th arrow is an identity is the
  `i`-th degeneracy of its `i`-th face.
* `CategoryTheory.nerve.mem_range_σ_iff`: the image of the `i`-th degeneracy consists of the
  strings whose `i`-th arrow is an identity.
* `CategoryTheory.nerve.δ_succ_precomp`: the faces of a string with a prepended arrow.
* `CategoryTheory.nerve.δ_last_snocTerminal`, `CategoryTheory.nerve.δ_castSucc_snocTerminal`: the
  faces of a string with an appended terminal object.
* `CategoryTheory.nerve.δ₀_mk₃_eq`, …, `CategoryTheory.nerve.δ₃_mk₃_eq`: the faces of the
  `3`-simplex of the nerve given by three composable morphisms.
-/

public section

open CategoryTheory Simplicial

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

/-- The `k`-th face of a simplex of the nerve reindexes its arrows along `k.succAbove`. -/
@[simp]
theorem totalArrow_δ {n : ℕ} (k : Fin (n + 2)) (σ : ComposableArrows C (n + 1))
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    ((nerve C).δ k σ).totalArrow i j hij =
      σ.totalArrow (k.succAbove i) (k.succAbove j) ((Fin.strictMono_succAbove k).monotone hij) :=
  -- `(nerve C).δ k` whiskers `σ` by `SimplexCategory.toCat.map (SimplexCategory.δ k)`, which acts
  -- on objects by `k.succAbove` by definition (as in Mathlib's `nerve.δ_obj`).
  σ.totalArrow_whiskerLeft _ i j hij

/-- Deleting the last vertex of `σ.snocTerminal ht` recovers `σ`. -/
@[simp]
theorem δ_last_snocTerminal {n : ℕ} (σ : ComposableArrows C n) {t : C} (ht : Limits.IsTerminal t) :
    (nerve C).δ (Fin.last (n + 1)) (σ.snocTerminal ht) = σ := by
  refine ComposableArrows.ext_of_totalArrow (n := n) fun i j hij ↦ ?_
  rw [totalArrow_δ]
  simp only [Fin.succAbove_last]
  exact σ.totalArrow_snocTerminal_castSucc ht i j hij

/-- Any face map other than the last commutes with `snocTerminal`. -/
@[simp]
theorem δ_castSucc_snocTerminal {n : ℕ} (k : Fin (n + 2)) (σ : ComposableArrows C (n + 1))
    {t : C} (ht : Limits.IsTerminal t) :
    (nerve C).δ k.castSucc (σ.snocTerminal ht) = ((nerve C).δ k σ).snocTerminal ht := by
  set τ : ComposableArrows C n := (nerve C).δ k σ
  refine ComposableArrows.ext_of_totalArrow (n := n + 1) fun i j hij ↦ ?_
  rw [totalArrow_δ]
  cases j using Fin.lastCases with
  | cast j₀ =>
    cases i using Fin.lastCases with
    | last => exact absurd hij (not_le_of_gt (Fin.castSucc_lt_last j₀))
    | cast i₀ =>
      have hij₀ : i₀ ≤ j₀ := Fin.castSucc_le_castSucc_iff.mp hij
      simp only [Fin.castSucc_succAbove_castSucc]
      rw [σ.totalArrow_snocTerminal_castSucc ht (k.succAbove i₀) (k.succAbove j₀)
        ((Fin.strictMono_succAbove k).monotone hij₀),
        τ.totalArrow_snocTerminal_castSucc ht i₀ j₀ hij₀, ← totalArrow_δ]
  | last =>
    have hkl : k.castSucc.succAbove (Fin.last (n + 1)) = Fin.last (n + 2) :=
      (Fin.succAbove_of_le_castSucc _ _
        (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last k))).trans (Fin.succ_last _)
    have hobj : (σ.snocTerminal ht).obj (k.castSucc.succAbove i) = (τ.snocTerminal ht).obj i := by
      cases i using Fin.lastCases with
      | last => rw [hkl, σ.snocTerminal_obj_last, τ.snocTerminal_obj_last]
      | cast _ =>
        rw [Fin.castSucc_succAbove_castSucc, σ.snocTerminal_obj_castSucc,
          τ.snocTerminal_obj_castSucc, δ_obj]
    have hr : (σ.snocTerminal ht).obj (k.castSucc.succAbove (Fin.last (n + 1))) = t := by
      rw [hkl, σ.snocTerminal_obj_last]
    refine (ComposableArrows.totalArrow_def _ _ _ _).trans
      (Eq.trans ?_ (τ.totalArrow_snocTerminal_last ht i).symm)
    refine Quiver.Total.ext hobj hr ((conj_eqToHom_iff_heq _ _ hobj hr).mp ?_)
    rw [← cancel_mono (eqToHom hr)]; exact ht.hom_ext _ _

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
