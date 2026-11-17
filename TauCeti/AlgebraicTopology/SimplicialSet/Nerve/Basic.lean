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
public import TauCeti.CategoryTheory.ComposableArrows.Basic

/-!
# Basic properties and structural isomorphisms of the nerve of a category

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
* `CategoryTheory.nerve.δ_succ_precomp`: the faces of a string with a prepended arrow.
* `CategoryTheory.nerve.δ₀_mk₃_eq`, …, `CategoryTheory.nerve.δ₃_mk₃_eq`: the faces of the
  `3`-simplex of the nerve given by three composable morphisms.
* `CategoryTheory.nerve.discreteIso`, `CategoryTheory.nerve.prodIso`,
  `CategoryTheory.nerve.asSmallIso`, `CategoryTheory.nerve.finSuccIsoStdSimplex`: structural
  isomorphisms in `SSet`.
-/

public section

open CategoryTheory MonoidalCategory Opposite Simplicial
universe w v u
namespace CategoryTheory
local macro "functor_ext_rfl" : term =>
  `(CategoryTheory.Functor.ext (fun _ ↦ rfl)
    fun _ _ _ ↦ ((Category.id_comp _).trans (Category.comp_id _)).symm)
section Functoriality
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
@[simp] lemma nerveMap_id (C : Type u) [Category.{v} C] : nerveMap (𝟭 C) = 𝟙 (nerve C) := by
  ext n σ : 4; exact functor_ext_rfl
@[simp, reassoc] lemma nerveMap_comp (F : C ⥤ D) (G : D ⥤ E) :
    nerveMap (F ⋙ G) = nerveMap F ≫ nerveMap G := by ext n σ : 4; exact functor_ext_rfl
@[simp] lemma nerveMap_const (C : Type u) [Category.{v} C] {D : Type u} [Category.{v} D] (d : D) :
    nerveMap ((Functor.const C).obj d) = SSet.const (nerveEquiv.symm d) := by
  ext ⟨n⟩ σ : 4; induction n using SimplexCategory.rec with | _ n => exact functor_ext_rfl
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
/-- The nerve of a product category `C × D` is isomorphic to `nerve C ⊗ nerve D`. -/
def prodIso (C D : Type u) [Category.{v} C] [Category.{v} D] :
    nerve (C × D) ≅ (nerve C ⊗ nerve D : SSet.{max u v}) :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso
    { toFun σ := (σ ⋙ CategoryTheory.Prod.fst C D, σ ⋙ CategoryTheory.Prod.snd C D)
      invFun p := p.1.prod' p.2, left_inv _ := functor_ext_rfl
      right_inv _ := Prod.ext functor_ext_rfl functor_ext_rfl }) fun _ ↦ rfl
@[simp] lemma prodIso_hom_app_fst {C D : Type u} [Category.{v} C] [Category.{v} D]
    {n : SimplexCategoryᵒᵖ} (σ : (nerve (C × D)).obj n) :
    dsimp% ((prodIso C D).hom.app n σ).1 = σ ⋙ CategoryTheory.Prod.fst C D := (rfl)
@[simp] lemma prodIso_hom_app_snd {C D : Type u} [Category.{v} C] [Category.{v} D]
    {n : SimplexCategoryᵒᵖ} (σ : (nerve (C × D)).obj n) :
    dsimp% ((prodIso C D).hom.app n σ).2 = σ ⋙ CategoryTheory.Prod.snd C D := (rfl)
@[simp] lemma prodIso_inv_app_apply {C D : Type u} [Category.{v} C] [Category.{v} D]
    {n : SimplexCategoryᵒᵖ} (p : (nerve C ⊗ nerve D : SSet.{max u v}).obj n) :
    dsimp% (prodIso C D).inv.app n p = p.1.prod' p.2 := (rfl)
/-- The nerve of `AsSmall.{w} C` is isomorphic to `SSet.uliftFunctor.obj (nerve C)`. -/
def asSmallIso (C : Type u) [Category.{v} C] :
    nerve (AsSmall.{w} C) ≅ SSet.uliftFunctor.{w, max u v}.obj (nerve C) :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso
    { toFun σ := ULift.up ((AsSmall.down.mapComposableArrows _).obj σ)
      invFun τ := (AsSmall.up.mapComposableArrows _).obj τ.down
      left_inv _ := functor_ext_rfl, right_inv _ := ULift.ext functor_ext_rfl }) fun _ ↦ rfl
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
end CategoryTheory
