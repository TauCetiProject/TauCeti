/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Yoneda

/-!
# Consequences of the Yoneda lemma

## Isomorphism criteria through descriptions of morphisms out of an object

Let `f : A' ⟶ A` be a morphism. Suppose that for every object `F` the morphisms `A ⟶ F` are
described as the elements of some type `X F` satisfying a property `P F`, the morphisms `A' ⟶ F`
as the elements of `X' F` satisfying `P' F`, and that under these descriptions precomposition with
`f` is a map `r F : X F → X' F`. By the Yoneda lemma, `f` is an isomorphism if and only if every
element of `X' F` satisfying `P' F` is the image under `r F` of a unique element of `X F`
satisfying `P F`.

A typical instance is a map of relative free sheaves, where morphisms out of the relative free
sheaf of `i : U ⟶ V` are the sections over `V` that restrict to zero along `i`, and `r F` is a
restriction map of sections.

## Representations of presheaves

For representations `R : F.RepresentableBy Y` of presheaves `F : Cᵒᵖ ⥤ Type w`, this file records
how classifying elements behave under transport of `R` along an isomorphism of presheaves, under
the comparison isomorphism between two representing objects, and under postcomposition with a
morphism between representing objects.

## Main results

* `TauCeti.CategoryTheory.isIso_iff_existsUnique_of_homEquiv`: the isomorphism criterion.
* `CategoryTheory.Functor.RepresentableBy.ofIso_homEquiv_apply`: transporting a representation
  along an isomorphism `e` of presheaves applies `e` to its classifying elements.
* `CategoryTheory.Functor.RepresentableBy.homEquiv_uniqueUpToIso_hom`: the isomorphism between two
  representing objects classifies the universal element of the first.
* `CategoryTheory.Functor.RepresentableBy.homEquiv_homEquiv_symm_comp_naturality`: postcomposition
  with a morphism between representing objects, read through the two representations, commutes
  with the maps of the presheaves.
-/

public section

open CategoryTheory

universe w v u

namespace TauCeti.CategoryTheory

variable {D : Type u} [Category.{v} D]

/-- Let `f : A' ⟶ A`, and suppose that for every object `F`, morphisms `A ⟶ F` and `A' ⟶ F`
correspond to the elements of `X F` satisfying `P F` and of `X' F` satisfying `P' F`, in such a
way that precomposition with `f` becomes `r F : X F → X' F`. Then `f` is an isomorphism if and only
if every element of `X' F` satisfying `P' F` is `r F t` for a unique `t` satisfying `P F`. -/
theorem isIso_iff_existsUnique_of_homEquiv {A' A : D} (f : A' ⟶ A) {X X' : D → Type w}
    {P : ∀ F, X F → Prop} {P' : ∀ F, X' F → Prop} (r : ∀ F, X F → X' F)
    (e : ∀ F, (A ⟶ F) ≃ {t // P F t}) (e' : ∀ F, (A' ⟶ F) ≃ {s // P' F s})
    (he : ∀ F (g : A ⟶ F), (e' F (f ≫ g) : X' F) = r F (e F g)) :
    IsIso f ↔ ∀ F (s : X' F), P' F s → ∃! t : X F, P F t ∧ r F t = s := by
  -- both directions compare precomposition with `f` and `r` through `e` and `e'`
  have key (F : D) (g : A ⟶ F) (g' : A' ⟶ F) : f ≫ g = g' ↔ r F (e F g) = e' F g' := by
    rw [← he, Subtype.coe_inj, (e' F).injective.eq_iff]
  constructor
  · intro _ F s hs
    let g' := (e' F).symm ⟨s, hs⟩
    refine ⟨e F (inv f ≫ g'), ⟨(e F _).property, ?_⟩, ?_⟩
    · simpa [g'] using (key F (inv f ≫ g') g').1 (IsIso.hom_inv_id_assoc f g')
    · rintro t ⟨ht, hts⟩
      have h : f ≫ (e F).symm ⟨t, ht⟩ = g' := (key F _ g').2 (by simpa [g'] using hts)
      rw [← h, IsIso.inv_hom_id_assoc, Equiv.apply_symm_apply]
  · intro h
    refine isIso_of_coyoneda_map_bijective f fun F ↦ ⟨fun g₁ g₂ hg ↦ ?_, fun g' ↦ ?_⟩
    · set s := e' F (f ≫ g₂)
      apply (e F).injective
      exact Subtype.ext <| (h F s s.property).unique ⟨(e F g₁).property, (key F g₁ _).1 hg⟩
        ⟨(e F g₂).property, (key F g₂ _).1 rfl⟩
    · obtain ⟨t, ⟨ht, hts⟩, -⟩ := h F _ (e' F g').property
      refine ⟨(e F).symm ⟨t, ht⟩, (key F _ g').2 ?_⟩
      rw [Equiv.apply_symm_apply]
      exact hts

end TauCeti.CategoryTheory

namespace CategoryTheory.Functor.RepresentableBy

open Opposite

variable {C : Type u} [Category.{v} C] {F : Cᵒᵖ ⥤ Type w} {Y : C} (R : F.RepresentableBy Y)

/-- Transporting a representation along a presheaf isomorphism applies that isomorphism to
its classifying element. -/
@[simp]
theorem ofIso_homEquiv_apply {G : Cᵒᵖ ⥤ Type w} (e : F ≅ G) {X : C} (f : X ⟶ Y) :
    (R.ofIso e).homEquiv f = e.hom.app (op X) (R.homEquiv f) :=
  rfl

/-- The isomorphism between two representing objects of `F` classifies, under the second
representation, the universal element of the first. -/
theorem homEquiv_uniqueUpToIso_hom {Y' : C} (R' : F.RepresentableBy Y') :
    R'.homEquiv (R.uniqueUpToIso R').hom = R.homEquiv (𝟙 Y) := by
  rw [uniqueUpToIso_hom, Yoneda.fullyFaithful_preimage]
  -- the preimage under Yoneda is the image of `𝟙 Y` under `R'.homEquiv.symm ∘ R.homEquiv`
  exact R'.homEquiv.apply_symm_apply _

/-- Postcomposition with a morphism `s : Y ⟶ Y'` between representing objects, read through the
representations `R` of `F` and `R'` of `G`, commutes with the maps of `F` and `G`. -/
theorem homEquiv_homEquiv_symm_comp_naturality {G : Cᵒᵖ ⥤ Type w} {Y' : C}
    (R' : G.RepresentableBy Y') (s : Y ⟶ Y') {X X' : C} (f : X ⟶ X') (x : F.obj (op X')) :
    R'.homEquiv (R.homEquiv.symm (F.map f.op x) ≫ s) =
      G.map f.op (R'.homEquiv (R.homEquiv.symm x ≫ s)) := by
  rw [← comp_homEquiv_symm, Category.assoc, homEquiv_comp]

end CategoryTheory.Functor.RepresentableBy
