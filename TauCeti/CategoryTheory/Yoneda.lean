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

## Corepresentations of functors to types

For a functor `Y : C ⥤ Type w` corepresented by `A`, natural transformations from `Y` to any
functor `G` are the elements of `G(A)`
(`CategoryTheory.Functor.CorepresentableBy.natTransEquiv`). Mathlib states this only for the
standard corepresentable functors `coyoneda.obj (op A)` and their universe lifts.

## Main results

* `TauCeti.CategoryTheory.isIso_iff_existsUnique_of_homEquiv`: the isomorphism criterion.
* `CategoryTheory.Functor.RepresentableBy.ofIso_homEquiv_apply`: transporting a representation
  along an isomorphism `e` of presheaves applies `e` to its classifying elements.
* `CategoryTheory.Functor.RepresentableBy.homEquiv_uniqueUpToIso_hom`: the isomorphism between two
  representing objects classifies the universal element of the first.
* `CategoryTheory.Functor.RepresentableBy.homEquiv_comp_uniqueUpToIso_inv`: postcomposition
  with the inverse comparison identifies the two representations on every point.
* `CategoryTheory.Functor.RepresentableBy.homEquiv_homEquiv_symm_comp_naturality`: postcomposition
  with a morphism between representing objects, read through the two representations, commutes
  with the maps of the presheaves.
* `CategoryTheory.Functor.CorepresentableBy.natTransEquiv`: the Yoneda lemma for an arbitrary
  corepresentation of a functor to types.

## References

* [ShortProof]: `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/Cohomology/Etale/Basic.lean` (declaration `New.Variety.homReprEquiv`, the free abelian
  group adjunction followed by Mathlib's `uliftCoyonedaEquiv`); Apache 2.0, Copyright 2026
  Anthropic, PBC. `CategoryTheory.Functor.CorepresentableBy.natTransEquiv` generalises its Yoneda
  step to an arbitrary corepresentation.
-/

public section

open CategoryTheory

universe w w' v u

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
-- top-down (`↓`): bottom-up, `simp` first rewrites the comparison isomorphism by
-- `uniqueUpToIso_hom` into a Yoneda preimage, after which this lemma no longer matches
@[simp↓]
theorem homEquiv_uniqueUpToIso_hom {Y' : C} (R' : F.RepresentableBy Y') :
    R'.homEquiv (R.uniqueUpToIso R').hom = R.homEquiv (𝟙 Y) := by
  rw [uniqueUpToIso_hom, Yoneda.fullyFaithful_preimage]
  -- the preimage under Yoneda is the image of `𝟙 Y` under `R'.homEquiv.symm ∘ R.homEquiv`
  exact R'.homEquiv.apply_symm_apply _

/-- The comparison `uniqueUpToIso` of two representing objects carries the representation `e'` to
the representation `e`. -/
lemma homEquiv_comp_uniqueUpToIso_inv
    {C : Type*} [Category C] {F : Cᵒᵖ ⥤ Type*} {Y Y' : C} (e : F.RepresentableBy Y)
    (e' : F.RepresentableBy Y') {T : C} (x : T ⟶ Y') :
    e.homEquiv (x ≫ (e.uniqueUpToIso e').inv) = e'.homEquiv x := by
  have h : e.homEquiv (e.uniqueUpToIso e').inv = e'.homEquiv (𝟙 Y') :=
    e.homEquiv.apply_symm_apply _
  rw [e.homEquiv_comp, h, ← e'.homEquiv_comp, Category.comp_id]

/-- Postcomposition with a morphism `s : Y ⟶ Y'` between representing objects, read through the
representations `R` of `F` and `R'` of `G`, commutes with the maps of `F` and `G`. -/
theorem homEquiv_homEquiv_symm_comp_naturality {G : Cᵒᵖ ⥤ Type w'} {Y' : C}
    (R' : G.RepresentableBy Y') (s : Y ⟶ Y') {X X' : C} (f : X ⟶ X') (x : F.obj (op X')) :
    R'.homEquiv (R.homEquiv.symm (F.map f.op x) ≫ s) =
      G.map f.op (R'.homEquiv (R.homEquiv.symm x ≫ s)) := by
  rw [← comp_homEquiv_symm, Category.assoc, homEquiv_comp]

end CategoryTheory.Functor.RepresentableBy

namespace CategoryTheory.Functor.CorepresentableBy

variable {C : Type u} [Category.{v} C] {Y : C ⥤ Type w} {A : C} (e : Y.CorepresentableBy A)

/-- **Yoneda lemma** for a functor `Y : C ⥤ Type w` corepresented by `A`: natural transformations
from `Y` to a functor `G` are the elements of `G(A)`, by evaluation at the universal element. -/
def natTransEquiv (G : C ⥤ Type w) : (Y ⟶ G) ≃ G.obj A where
  toFun φ := φ.app A (e.homEquiv (𝟙 A))
  invFun g :=
    { app _ := ↾fun y ↦ G.map (e.homEquiv.symm y) g
      naturality _ _ f := by
        ext y
        simp [← e.homEquiv_symm_comp] }
  left_inv φ := by
    ext c y
    obtain ⟨f, rfl⟩ := e.homEquiv.surjective y
    simp [← NatTrans.naturality_apply, ← e.homEquiv_comp]
  right_inv g := by simp

/-- The Yoneda bijection evaluates a natural transformation at the universal element. -/
@[simp]
lemma natTransEquiv_apply (G : C ⥤ Type w) (φ : Y ⟶ G) :
    e.natTransEquiv G φ = φ.app A (e.homEquiv (𝟙 A)) :=
  (rfl)

/-- The natural transformation corresponding to `g ∈ G(A)` sends `y ∈ Y(c)`, the image of a
morphism `A ⟶ c`, to the image of `g` under that morphism. -/
@[simp]
lemma natTransEquiv_symm_apply_app (G : C ⥤ Type w) (g : G.obj A) {c : C} (y : Y.obj c) :
    ((e.natTransEquiv G).symm g).app c y = G.map (e.homEquiv.symm y) g :=
  (rfl)

end CategoryTheory.Functor.CorepresentableBy
