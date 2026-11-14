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
(`CategoryTheory.nerve.δ_succ_precomp`).

A `3`-simplex of the nerve is a sequence of three composable morphisms `ComposableArrows.mk₃ f g h`.
Its faces are the `2`-simplices obtained by dropping a vertex, whose arrows are composites of
consecutive arrows among `f`, `g` and `h`. This extends Mathlib's description of the faces of
`2`-simplices (`CategoryTheory.nerve.δ₀_mk₂_eq`, …).

We also record basic functoriality and identifications of nerves: `TauCeti.nerveMap_injective` shows
that `nerveMap` is injective on functors (in arbitrary object and morphism universes),
`TauCeti.nerveMap_const` identifies the nerve map of a constant functor with `SSet.const`,
`CategoryTheory.nerve.asSmallIso` identifies `nerve (AsSmall C)` with
`SSet.uliftFunctor.obj (nerve C)`, and `CategoryTheory.nerve.discreteIso` identifies
`nerve (Discrete S)` with the constant simplicial set on `S`.

## Main declarations

* `CategoryTheory.nerve.σ_δ_castSucc_eq_self`: a string whose `i`-th arrow is an identity is the
  `i`-th degeneracy of its `i`-th face.
* `CategoryTheory.nerve.mem_range_σ_iff`: the image of the `i`-th degeneracy consists of the
  strings whose `i`-th arrow is an identity.
* `CategoryTheory.nerve.δ_succ_precomp`: the faces of a string with a prepended arrow.
* `CategoryTheory.nerve.δ₀_mk₃_eq`, …, `CategoryTheory.nerve.δ₃_mk₃_eq`: the faces of the
  `3`-simplex of the nerve given by three composable morphisms.
* `CategoryTheory.nerve.objEquiv`, `CategoryTheory.nerve.asSmallIso`,
  `CategoryTheory.nerve.discreteIso`: simplex equivalence for `nerve C` and nerves of `AsSmall C`
  and `Discrete S`.
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

/-- Equivalence `(nerve C) _⦋n⦌ ≃ ComposableArrows C n` on `n`-simplices of `nerve C`,
mirroring `SSet.stdSimplex.objEquiv` and `SSet.opObjEquiv` so simplices of `nerve C` retain their
syntactic type under `implicit` transparency. -/
def objEquiv {C : Type u} [Category.{v} C] {n : ℕ} :
    (nerve C) _⦋n⦌ ≃ ComposableArrows C n :=
  Equiv.refl _

@[simp]
theorem nerveMap_app_objEquiv_symm {D : Type u} [Category.{v} D] (F : C ⥤ D) {n : ℕ}
    (s : ComposableArrows C n) :
    (nerveMap F).app (op ⦋n⦌) (objEquiv.symm s) =
      objEquiv.symm ((F.mapComposableArrows n).obj s) :=
  (rfl)

theorem nerveMap_app_eq_objEquiv_symm {D : Type u} [Category.{v} D] (F : C ⥤ D) {n : ℕ}
    (s : (nerve C) _⦋n⦌) :
    (nerveMap F).app (op ⦋n⦌) s = objEquiv.symm ((F.mapComposableArrows n).obj (objEquiv s)) :=
  (rfl)

theorem objEquiv_symm_nerveEquiv_symm (X : C) :
    objEquiv.symm (nerveEquiv.symm X) = (nerveEquiv.symm X : (nerve C) _⦋0⦌) :=
  (rfl)

@[simp]
theorem representableBy_homEquiv_const_zero {n : ℕ} {α : Type u} [Preorder α]
    (e : α ≃o Fin (n + 1)) (i : Fin (n + 1)) :
    (representableBy α e).homEquiv (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) =
      objEquiv.symm (nerveEquiv.symm (e.symm i)) :=
  objEquiv.injective <| ComposableArrows.ext (fun j ↦ by fin_cases j; rfl)
    (fun _ _ ↦ Subsingleton.elim _ _)

/-- Applying `Φ.mapComposableArrows 0` to `nerveEquiv.symm X` gives `nerveEquiv.symm (Φ.obj X)`. -/
@[simp]
theorem _root_.CategoryTheory.Functor.mapComposableArrows_obj_nerveEquiv_symm
    {D : Type*} [Category D] (Φ : C ⥤ D) (X : C) :
    (Φ.mapComposableArrows 0).obj (nerveEquiv.symm X) = nerveEquiv.symm (Φ.obj X) :=
  ComposableArrows.ext₀ rfl

/-- The nerve of `AsSmall.{w} C` is naturally isomorphic to the universe lift of `nerve C`. -/
def asSmallIso (C : Type u) [Category.{v} C] :
    nerve (AsSmall.{w} C) ≅ SSet.uliftFunctor.{w, max u v}.obj (nerve C) where
  hom :=
    { app m := ↾fun s ↦ ULift.up ((AsSmall.down.mapComposableArrows m.unop.len).obj s)
      naturality _ _ _ := rfl }
  inv :=
    { app m := ↾fun s ↦ (AsSmall.up.mapComposableArrows m.unop.len).obj s.down
      naturality _ _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

@[simp]
lemma asSmallIso_hom_app_down {C : Type u} [Category.{v} C] {n : ℕ}
    (s : (nerve (AsSmall.{w} C)) _⦋n⦌) :
    ULift.down ((asSmallIso.{w} C).hom.app (op ⦋n⦌) s) =
      objEquiv.symm ((AsSmall.down.mapComposableArrows n).obj (objEquiv s)) :=
  (rfl)

@[simp]
lemma asSmallIso_inv_app {C : Type u} [Category.{v} C] {n : ℕ}
    (s : (SSet.uliftFunctor.{w, max u v}.obj (nerve C)) _⦋n⦌) :
    (asSmallIso.{w} C).inv.app (op ⦋n⦌) s =
      objEquiv.symm ((AsSmall.up.mapComposableArrows n).obj (objEquiv (ULift.down s))) :=
  (rfl)

/-- The nerve of a discrete category `Discrete S` is isomorphic to the constant simplicial set on
`S`. -/
def discreteIso (S : Type u) :
    nerve (Discrete S) ≅ (Functor.const SimplexCategoryᵒᵖ).obj S where
  hom :=
    { app _ := ↾fun F ↦ (F.obj 0).as
      naturality _ _ _ := ConcreteCategory.hom_ext _ _ fun F ↦ by
        dsimp [nerve, Functor.const]
        exact (Discrete.eq_of_hom (F.map (homOfLE (Fin.zero_le _)))).symm }
  inv :=
    { app m := ↾fun s ↦ (Functor.const (Fin (m.unop.len + 1))).obj (Discrete.mk s)
      naturality _ _ _ := rfl }
  hom_inv_id := by
    ext ⟨⟨n⟩⟩ F : 4
    exact ComposableArrows.ext
      (fun i ↦ Discrete.ext (Discrete.eq_of_hom (F.map (homOfLE (Fin.zero_le i)))))
      (fun _ _ ↦ Subsingleton.elim _ _)
  inv_hom_id := rfl

@[simp]
lemma discreteIso_hom_app_objEquiv_symm (S : Type u) (s : S) :
    ConcreteCategory.hom (X := (nerve (Discrete S)).obj (op ⦋0⦌)) (Y := S)
      ((discreteIso S).hom.app (op ⦋0⦌)) (objEquiv.symm (nerveEquiv.symm (Discrete.mk s))) = s :=
  (rfl)

end CategoryTheory.nerve

namespace TauCeti

/-- `nerveMap` is injective on functors in arbitrary object and morphism universes: the
`1`-simplices of the nerve recover the action of a functor on objects and morphisms. This extends
`CategoryTheory.nerveFunctor.faithful` (which requires `v = u`) to `Cat.{v, u}`. -/
theorem nerveMap_injective {C D : Type u} [Category.{v} C] [Category.{v} D] :
    Function.Injective (nerveMap : (C ⥤ D) → (nerve C ⟶ nerve D)) := by
  intro F G h
  have h₁ {X Y : C} (f : X ⟶ Y) : Arrow.mk (F.map f) = Arrow.mk (G.map f) := by
    rw [← ComposableArrows.mk₁_eq_mk₁_iff, ← nerveMap_app_mk₁, ← nerveMap_app_mk₁, h]
  refine CategoryTheory.Functor.ext (fun X ↦ congr($(h₁ (𝟙 X)).left)) fun X Y f ↦ ?_
  obtain ⟨_, _, hf⟩ := (Arrow.mk_eq_mk_iff _ _).1 (h₁ f)
  exact hf

instance : nerveFunctor.{v, u}.Faithful where
  map_injective h := Cat.Hom.ext (nerveMap_injective h)

/-- The nerve map of a constant functor `(Functor.const C).obj Y` is the constant simplicial map at
`nerve.objEquiv.symm (nerveEquiv.symm Y)`. -/
@[simp]
theorem nerveMap_const (C D : Type u) [Category.{v} C] [Category.{v} D] (Y : D) :
    nerveMap ((Functor.const C).obj Y) =
      SSet.const (nerve.objEquiv.symm (nerveEquiv.symm Y)) :=
  SSet.hom_ext fun ⟨⟨n⟩⟩ ↦ ConcreteCategory.hom_ext _ _ fun (s : ComposableArrows C n) ↦ by
    have h : (((Functor.const C).obj Y).mapComposableArrows n).obj s =
        (ComposableArrows.mk₀ Y).whiskerLeft
          (SimplexCategory.toCat.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0)).toFunctor :=
      ComposableArrows.ext_of_totalArrow fun _ _ _ ↦ by
        simp [ComposableArrows.totalArrow_def]; rfl
    exact h

end TauCeti
