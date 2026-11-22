/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack

import Mathlib.CategoryTheory.Sites.Descent.Precoverage
import TauCeti.CategoryTheory.Sites.Descent.DescentData
import TauCeti.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Transitivity and base-change locality of effective descent

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor and `J` a Grothendieck topology on `C`.
This file establishes closure properties for stacks and the local effective-descent condition
`F.IsStackFor`.

## Main results

* `CategoryTheory.Pseudofunctor.IsStack.of_le`: a stack for a finer Grothendieck topology is a
  stack for any coarser topology.
* `CategoryTheory.Pseudofunctor.isStackFor_top`: every pseudofunctor has effective descent for
  the maximal presieve `⊤`.
* `CategoryTheory.Pseudofunctor.IsStackFor.comp`: transitivity of effective descent along
  `J`-covering compositions when `F` is a `J`-prestack.
* `CategoryTheory.Pseudofunctor.IsStackFor.of_pullback'`,
  `CategoryTheory.Pseudofunctor.IsStackFor.of_pullback`: base-change locality of effective
  descent for a `J`-covering sieve (resp. family with pointwise pullbacks) along a `J`-covering
  family `v` for which `F` has effective descent, when `F` is a `J`-prestack, deduced from
  `IsStackFor.comp` and Mathlib's `IsStackFor.of_le'`.

## References

* Jean Giraud, *Cohomologie non abélienne*, Chapter II, §1.2.
* The Stacks Project, Section 8.4, *Stacks*, Tag 026F.
-/

public section

universe t t' v' v u' u

open CategoryTheory Limits Opposite Bicategory

namespace CategoryTheory.Pseudofunctor

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

/-- A stack for a Grothendieck topology `J₂` is a stack for any coarser topology `J₁ ≤ J₂`. -/
lemma IsStack.of_le {J₁ J₂ : GrothendieckTopology C} (h : J₁ ≤ J₂) [F.IsStack J₂] :
    F.IsStack J₁ :=
  .of_isStackFor fun _ R hR ↦ F.isStackFor' R (h _ hR)

variable (F) in
/-- Every pseudofunctor has effective descent for the maximal presieve `⊤`. -/
@[simp]
lemma isStackFor_top (S : C) : F.IsStackFor (⊤ : Presieve S) := by
  have hsieve : Sieve.generate (⊤ : Presieve S) =
      Sieve.ofArrows (fun _ : PUnit.{1} ↦ S) (fun _ ↦ 𝟙 S) := by
    ext Z g
    simpa using ⟨S, g, 𝟙 S, Presieve.ofArrows.mk PUnit.unit, Category.comp_id g⟩
  rw [F.isStackFor_iff_of_sieve_eq hsieve, isStackFor_ofArrows_iff]
  have hpre : F.IsPrestackFor (Presieve.ofArrows (fun _ : PUnit.{1} ↦ S) (fun _ ↦ 𝟙 S)) :=
    (F.isPrestackFor_iff_of_sieve_eq hsieve).1 (F.isPrestackFor_top S)
  obtain ⟨hff⟩ := (F.isPrestackFor_ofArrows_iff _).1 hpre
  have := hff.full
  have := hff.faithful
  have : (F.toDescentData (fun _ : PUnit.{1} ↦ 𝟙 S)).EssSurj := ⟨fun D ↦ ⟨D.obj PUnit.unit,
    ⟨DescentData.isoMk (fun _ ↦ F.idIso (D.obj PUnit.unit))
      fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
        cases i₁; cases i₂
        simp only [Category.comp_id] at hf₁ hf₂
        subst hf₁ hf₂
        rw [D.hom_self f₂ f₂ (Category.comp_id f₂),
          ((F.toDescentData (fun _ : PUnit.{1} ↦ 𝟙 S)).obj (D.obj PUnit.unit)).hom_self
            f₂ f₂ (Category.comp_id f₂),
          Category.comp_id, Category.id_comp]⟩⟩⟩
  exact {}

namespace Comp

variable {J : GrothendieckTopology C} [F.IsPrestack J]
  {S : C} {κ : Type t} {Y : κ → C} {p : ∀ j, Y j ⟶ S}
  {ι : κ → Type t'} {X : ∀ j, ι j → C} {u : ∀ j k, X j k ⟶ Y j}

/-- Restrict a descent datum along the composite family `u j k ≫ p j` to the covering `u j` of
`Y j` via Mathlib's `DescentData.pullFunctor`. -/
private abbrev restrictDatum (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (j : κ) : F.DescentData (u j) :=
  (DescentData.pullFunctor F (p := p j) (α := fun k ↦ ⟨j, k⟩) (p' := fun _ ↦ 𝟙 _)
    (by simp)).obj D

private lemma restrictDatum_hom (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    {W Z : C} {q : W ⟶ S} {j : κ} {a : W ⟶ Y j} (ha : a ≫ p j = q) (r : Z ⟶ W)
    {k₁ k₂ : ι j} (b₁ : Z ⟶ X j k₁) (b₂ : Z ⟶ X j k₂)
    (hb₁ : b₁ ≫ u j k₁ = r ≫ a) (hb₂ : b₂ ≫ u j k₂ = r ≫ a) :
    (restrictDatum D j).hom (r ≫ a) b₁ b₂ hb₁ hb₂ =
      (F.map b₁.op.toLoc).toFunctor.map (F.idIso (D.obj ⟨j, k₁⟩)).hom ≫
        D.hom (r ≫ q) (i₁ := ⟨j, k₁⟩) (i₂ := ⟨j, k₂⟩) b₁ b₂
          (by rw [← Category.assoc, hb₁, Category.assoc, ha])
          (by rw [← Category.assoc, hb₂, Category.assoc, ha]) ≫
        (F.map b₂.op.toLoc).toFunctor.map (F.idIso (D.obj ⟨j, k₂⟩)).inv := by
  simpa only [op_id, compIso_id_comp_inv, compIso_id_comp_hom] using
    DescentData.pullFunctor_obj_hom_eq (F := F) (p := p j)
      (α := fun k ↦ (⟨j, k⟩ : Σ j, ι j)) (p' := fun _ ↦ 𝟙 _) (by simp) D (r ≫ a) b₁ b₂
      (r ≫ q) b₁ b₂ hb₁ hb₂ (by rw [Category.assoc, ha]) (Category.comp_id b₁)
      (Category.comp_id b₂)

/-- Component isomorphism `(u j k)^* (M j) ≅ (𝟙 (X j k))^* (D.obj ⟨j, k⟩)` extracted from
`α j`. -/
private def αAppIso (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j) (j : κ) (k : ι j) :
    (F.map (u j k).op.toLoc).toFunctor.obj (M j) ≅
      (F.map (𝟙 (X j k)).op.toLoc).toFunctor.obj (D.obj ⟨j, k⟩) :=
  DescentData.isoApp (α j) k

private lemma αAppIso_hom (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j) (j : κ) (k : ι j) :
    (αAppIso D M α j k).hom = (α j).hom.hom k :=
  DescentData.isoApp_hom (α j) k

/-- The component isomorphism `(u j k)^* (M j) ≅ D.obj ⟨j, k⟩` obtained from `αAppIso` and
`F.idIso`. -/
private def αIso (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j) (j : κ) (k : ι j) :
    (F.map (u j k).op.toLoc).toFunctor.obj (M j) ≅ D.obj ⟨j, k⟩ :=
  αAppIso D M α j k ≪≫ F.idIso (D.obj ⟨j, k⟩)

private lemma αIso_hom (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j) (j : κ) (k : ι j) :
    (αIso D M α j k).hom =
      (αAppIso D M α j k).hom ≫ (F.idIso (D.obj ⟨j, k⟩)).hom :=
  rfl

private lemma αIso_inv (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j) (j : κ) (k : ι j) :
    (αIso D M α j k).inv =
      (F.idIso (D.obj ⟨j, k⟩)).inv ≫ (αAppIso D M α j k).inv :=
  rfl

/-- The conjugated transition map `ra₁^* (M j₁) ⟶ ra₂^* (M j₂)` over `Z` induced by
factorizations `b₁ ≫ u j₁ k₁ = ra₁` and `b₂ ≫ u j₂ k₂ = ra₂`. -/
private def localTrans (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {Z : C} {rq : Z ⟶ S} {j₁ j₂ : κ} {ra₁ : Z ⟶ Y j₁} {ra₂ : Z ⟶ Y j₂}
    (hra₁ : ra₁ ≫ p j₁ = rq) (hra₂ : ra₂ ≫ p j₂ = rq)
    {k₁ : ι j₁} {k₂ : ι j₂} (b₁ : Z ⟶ X j₁ k₁) (b₂ : Z ⟶ X j₂ k₂)
    (hb₁ : b₁ ≫ u j₁ k₁ = ra₁) (hb₂ : b₂ ≫ u j₂ k₂ = ra₂) :
    (F.map ra₁.op.toLoc).toFunctor.obj (M j₁) ⟶ (F.map ra₂.op.toLoc).toFunctor.obj (M j₂) :=
  pullHom (F := F) (X₁ := Y j₁) (X₂ := X j₁ k₁) (M₁ := M j₁) (M₂ := D.obj ⟨j₁, k₁⟩)
      (f₁ := u j₁ k₁) (f₂ := 𝟙 (X j₁ k₁))
      (αAppIso D M α j₁ k₁).hom b₁ ra₁ b₁ hb₁ (Category.comp_id b₁) ≫
    D.hom rq (i₁ := ⟨j₁, k₁⟩) (i₂ := ⟨j₂, k₂⟩) b₁ b₂
      (by rw [← Category.assoc, hb₁, hra₁]) (by rw [← Category.assoc, hb₂, hra₂]) ≫
    pullHom (F := F) (X₁ := X j₂ k₂) (X₂ := Y j₂) (M₁ := D.obj ⟨j₂, k₂⟩) (M₂ := M j₂)
      (f₁ := 𝟙 (X j₂ k₂)) (f₂ := u j₂ k₂)
      (αAppIso D M α j₂ k₂).inv b₂ b₂ ra₂ (Category.comp_id b₂) hb₂

private lemma localTrans_eq (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {Z : C} {rq : Z ⟶ S} {j₁ j₂ : κ} {ra₁ : Z ⟶ Y j₁} {ra₂ : Z ⟶ Y j₂}
    (hra₁ : ra₁ ≫ p j₁ = rq) (hra₂ : ra₂ ≫ p j₂ = rq)
    {k₁ : ι j₁} {k₂ : ι j₂} (b₁ : Z ⟶ X j₁ k₁) (b₂ : Z ⟶ X j₂ k₂)
    (hb₁ : b₁ ≫ u j₁ k₁ = ra₁) (hb₂ : b₂ ≫ u j₂ k₂ = ra₂) :
    localTrans D M α hra₁ hra₂ b₁ b₂ hb₁ hb₂ =
      (F.compIso (u j₁ k₁).op b₁.op ra₁.op (by rw [← op_comp, hb₁]) (M j₁)).hom ≫
        (F.map b₁.op.toLoc).toFunctor.map (αIso D M α j₁ k₁).hom ≫
        D.hom rq (i₁ := ⟨j₁, k₁⟩) (i₂ := ⟨j₂, k₂⟩) b₁ b₂
          (by rw [← Category.assoc, hb₁, hra₁]) (by rw [← Category.assoc, hb₂, hra₂]) ≫
        (F.map b₂.op.toLoc).toFunctor.map (αIso D M α j₂ k₂).inv ≫
        (F.compIso (u j₂ k₂).op b₂.op ra₂.op (by rw [← op_comp, hb₂]) (M j₂)).inv := by
  rw [localTrans, pullHom_eq_compIso, pullHom_eq_compIso]
  simp only [op_id, compIso_id_comp_inv, compIso_id_comp_hom, αIso_hom, αIso_inv,
    Functor.map_comp, Category.assoc]

@[reassoc]
private lemma localTrans_comp_αIso
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {Z : C} {rq : Z ⟶ S} {j₁ j₂ : κ} {ra₁ : Z ⟶ Y j₁} {ra₂ : Z ⟶ Y j₂}
    (hra₁ : ra₁ ≫ p j₁ = rq) (hra₂ : ra₂ ≫ p j₂ = rq)
    {k₁ : ι j₁} {k₂ : ι j₂} (b₁ : Z ⟶ X j₁ k₁) (b₂ : Z ⟶ X j₂ k₂)
    (hb₁ : b₁ ≫ u j₁ k₁ = ra₁) (hb₂ : b₂ ≫ u j₂ k₂ = ra₂) :
    localTrans D M α hra₁ hra₂ b₁ b₂ hb₁ hb₂ ≫
        (F.compIso (u j₂ k₂).op b₂.op ra₂.op (by rw [← op_comp, hb₂]) (M j₂)).hom ≫
        (F.map b₂.op.toLoc).toFunctor.map (αIso D M α j₂ k₂).hom =
      (F.compIso (u j₁ k₁).op b₁.op ra₁.op (by rw [← op_comp, hb₁]) (M j₁)).hom ≫
        (F.map b₁.op.toLoc).toFunctor.map (αIso D M α j₁ k₁).hom ≫
        D.hom rq (i₁ := ⟨j₁, k₁⟩) (i₂ := ⟨j₂, k₂⟩) b₁ b₂
          (by rw [← Category.assoc, hb₁, hra₁]) (by rw [← Category.assoc, hb₂, hra₂]) := by
  rw [localTrans_eq]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp, Iso.inv_hom_id,
    Functor.map_id, Category.comp_id]

/-- Pulling back `localTrans` along `g : Z' ⟶ Z` corresponds to precomposing the factorizations
`b₁` and `b₂` with `g`. -/
private lemma pullHom_localTrans (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {Z Z' : C} {rq : Z ⟶ S} {j₁ j₂ : κ} {ra₁ : Z ⟶ Y j₁} {ra₂ : Z ⟶ Y j₂}
    (hra₁ : ra₁ ≫ p j₁ = rq) (hra₂ : ra₂ ≫ p j₂ = rq) (g : Z' ⟶ Z)
    {k₁ : ι j₁} {k₂ : ι j₂} (b₁ : Z ⟶ X j₁ k₁) (b₂ : Z ⟶ X j₂ k₂)
    (hb₁ : b₁ ≫ u j₁ k₁ = ra₁) (hb₂ : b₂ ≫ u j₂ k₂ = ra₂)
    (ra₁' : Z' ⟶ Y j₁) (ra₂' : Z' ⟶ Y j₂) (rq' : Z' ⟶ S)
    (hra₁' : g ≫ ra₁ = ra₁') (hra₂' : g ≫ ra₂ = ra₂') (hrq' : g ≫ rq = rq') :
    pullHom (localTrans D M α hra₁ hra₂ b₁ b₂ hb₁ hb₂) g ra₁' ra₂' hra₁' hra₂' =
      localTrans D M α (by rw [← hra₁', Category.assoc, hra₁, hrq'])
        (by rw [← hra₂', Category.assoc, hra₂, hrq']) (g ≫ b₁) (g ≫ b₂)
        (by rw [Category.assoc, hb₁, hra₁']) (by rw [Category.assoc, hb₂, hra₂']) := by
  subst hra₁' hra₂' hrq'
  dsimp only [localTrans]
  rw [pullHom_comp _ _ g (g ≫ ra₁) (g ≫ b₁) (g ≫ ra₂),
    pullHom_comp _ _ g (g ≫ b₁) (g ≫ b₂) (g ≫ ra₂)]
  erw [pullHom_pullHom, pullHom_pullHom]
  congr 2
  exact D.pullHom_hom g rq (g ≫ rq) rfl (i₁ := ⟨j₁, k₁⟩) (i₂ := ⟨j₂, k₂⟩)
    b₁ b₂ (by rw [← Category.assoc, hb₁, hra₁]) (by rw [← Category.assoc, hb₂, hra₂])
    (g ≫ b₁) (g ≫ b₂) rfl rfl

private lemma localTrans_self (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {Z : C} {rq : Z ⟶ S} {j : κ} {ra : Z ⟶ Y j} (hra : ra ≫ p j = rq)
    {k : ι j} (b : Z ⟶ X j k) (hb : b ≫ u j k = ra) :
    localTrans D M α hra hra b b hb hb = 𝟙 _ := by
  rw [localTrans_eq, D.hom_self _ (i := ⟨j, k⟩) _ (by rw [← Category.assoc, hb, hra])]
  simp only [Category.id_comp, ← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id]

private lemma localTrans_comp (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {Z : C} {rq : Z ⟶ S} {j₁ j₂ j₃ : κ}
    {ra₁ : Z ⟶ Y j₁} {ra₂ : Z ⟶ Y j₂} {ra₃ : Z ⟶ Y j₃}
    (hra₁ : ra₁ ≫ p j₁ = rq) (hra₂ : ra₂ ≫ p j₂ = rq) (hra₃ : ra₃ ≫ p j₃ = rq)
    {k₁ : ι j₁} {k₂ : ι j₂} {k₃ : ι j₃}
    (b₁ : Z ⟶ X j₁ k₁) (b₂ : Z ⟶ X j₂ k₂) (b₃ : Z ⟶ X j₃ k₃)
    (hb₁ : b₁ ≫ u j₁ k₁ = ra₁) (hb₂ : b₂ ≫ u j₂ k₂ = ra₂) (hb₃ : b₃ ≫ u j₃ k₃ = ra₃) :
    localTrans D M α hra₁ hra₂ b₁ b₂ hb₁ hb₂ ≫ localTrans D M α hra₂ hra₃ b₂ b₃ hb₂ hb₃ =
      localTrans D M α hra₁ hra₃ b₁ b₃ hb₁ hb₃ := by
  simp only [localTrans_eq, Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id, Functor.map_id, Category.id_comp, D.hom_comp_assoc]

@[reassoc]
private lemma αIso_comm (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W Z : C} {q : W ⟶ S} {j : κ} {a : W ⟶ Y j} (ha : a ≫ p j = q) (r : Z ⟶ W)
    {k₁ k₂ : ι j} (b₁ : Z ⟶ X j k₁) (b₂ : Z ⟶ X j k₂)
    (hb₁ : b₁ ≫ u j k₁ = r ≫ a) (hb₂ : b₂ ≫ u j k₂ = r ≫ a) :
    (F.compIso (u j k₁).op b₁.op (r ≫ a).op (by rw [← op_comp, hb₁]) (M j)).hom ≫
      (F.map b₁.op.toLoc).toFunctor.map (αIso D M α j k₁).hom ≫
      D.hom (r ≫ q) (i₁ := ⟨j, k₁⟩) (i₂ := ⟨j, k₂⟩) b₁ b₂
        (by rw [← Category.assoc, hb₁, Category.assoc, ha])
        (by rw [← Category.assoc, hb₂, Category.assoc, ha]) =
      (F.compIso (u j k₂).op b₂.op (r ≫ a).op (by rw [← op_comp, hb₂]) (M j)).hom ≫
        (F.map b₂.op.toLoc).toFunctor.map (αIso D M α j k₂).hom := by
  have hcomm :
      (F.compIso (u j k₁).op b₁.op (r ≫ a).op (by rw [← op_comp, hb₁]) (M j)).hom ≫
        (F.map b₁.op.toLoc).toFunctor.map (αAppIso D M α j k₁).hom ≫
        (restrictDatum D j).hom (r ≫ a) b₁ b₂ hb₁ hb₂ =
      (F.compIso (u j k₂).op b₂.op (r ≫ a).op (by rw [← op_comp, hb₂]) (M j)).hom ≫
        (F.map b₂.op.toLoc).toFunctor.map (αAppIso D M α j k₂).hom :=
    (DescentData.hom_toDescentData_obj_iff (F := F) (f := u j) (r ≫ a) b₁ b₂ hb₁ hb₂
      _ _ _).1 (by
        have h := (α j).hom.comm (r ≫ a) b₁ b₂ hb₁ hb₂
        rw [← αAppIso_hom, ← αAppIso_hom] at h
        exact h)
  rw [restrictDatum_hom D ha r b₁ b₂ hb₁ hb₂] at hcomm
  rw [αIso_hom, αIso_hom, Functor.map_comp, Functor.map_comp, Category.assoc,
    ← cancel_mono ((F.map b₂.op.toLoc).toFunctor.map (F.idIso (D.obj ⟨j, k₂⟩)).inv)]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, Category.comp_id]
  exact hcomm

private lemma localTrans_lift_eq_id (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W Z : C} {q : W ⟶ S} {j : κ} {a : W ⟶ Y j} (ha : a ≫ p j = q) (r : Z ⟶ W)
    {k₁ k₂ : ι j} (b₁ : Z ⟶ X j k₁) (b₂ : Z ⟶ X j k₂)
    (hb₁ : b₁ ≫ u j k₁ = r ≫ a) (hb₂ : b₂ ≫ u j k₂ = r ≫ a) :
    localTrans D M α (by rw [Category.assoc, ha]) (by rw [Category.assoc, ha]) b₁ b₂ hb₁ hb₂ =
      𝟙 _ := by
  rw [← cancel_mono ((F.compIso (u j k₂).op b₂.op (r ≫ a).op (by rw [← op_comp, hb₂]) (M j)).hom ≫
      (F.map b₂.op.toLoc).toFunctor.map (αIso D M α j k₂).hom),
    localTrans_comp_αIso, αIso_comm D M α ha r b₁ b₂ hb₁ hb₂, Category.id_comp]

private lemma localTrans_unique (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W Z : C} {q : W ⟶ S} {j₁ j₂ : κ} {a₁ : W ⟶ Y j₁} {a₂ : W ⟶ Y j₂}
    (ha₁ : a₁ ≫ p j₁ = q) (ha₂ : a₂ ≫ p j₂ = q) (r : Z ⟶ W)
    {k₁ k₁' : ι j₁} {k₂ k₂' : ι j₂}
    (b₁ : Z ⟶ X j₁ k₁) (b₁' : Z ⟶ X j₁ k₁') (b₂ : Z ⟶ X j₂ k₂) (b₂' : Z ⟶ X j₂ k₂')
    (hb₁ : b₁ ≫ u j₁ k₁ = r ≫ a₁) (hb₁' : b₁' ≫ u j₁ k₁' = r ≫ a₁)
    (hb₂ : b₂ ≫ u j₂ k₂ = r ≫ a₂) (hb₂' : b₂' ≫ u j₂ k₂' = r ≫ a₂) :
    localTrans D M α (by rw [Category.assoc, ha₁]) (by rw [Category.assoc, ha₂]) b₁ b₂ hb₁ hb₂ =
      localTrans D M α (by rw [Category.assoc, ha₁]) (by rw [Category.assoc, ha₂])
        b₁' b₂' hb₁' hb₂' := by
  rw [← localTrans_comp D M α (by rw [Category.assoc, ha₁]) (by rw [Category.assoc, ha₁])
      (by rw [Category.assoc, ha₂]) b₁ b₁' b₂ hb₁ hb₁' hb₂,
    localTrans_lift_eq_id D M α ha₁ r b₁ b₁' hb₁ hb₁', Category.id_comp,
    ← localTrans_comp D M α (by rw [Category.assoc, ha₁]) (by rw [Category.assoc, ha₂])
      (by rw [Category.assoc, ha₂]) b₁' b₂' b₂ hb₁' hb₂' hb₂,
    localTrans_lift_eq_id D M α ha₂ r b₂' b₂ hb₂' hb₂, Category.comp_id]

/-- The glued transition morphism `a₁^* (M j₁) ⟶ a₂^* (M j₂)` on `W`, obtained by gluing
`localTrans` along the covering intersection sieve of `a₁^* (u j₁)` and `a₂^* (u j₂)`. -/
private noncomputable def gluedHom (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j))
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W : C} (q : W ⟶ S) {j₁ j₂ : κ} (a₁ : W ⟶ Y j₁) (a₂ : W ⟶ Y j₂)
    (ha₁ : a₁ ≫ p j₁ = q) (ha₂ : a₂ ≫ p j₂ = q) :
    (F.map a₁.op.toLoc).toFunctor.obj (M j₁) ⟶ (F.map a₂.op.toLoc).toFunctor.obj (M j₂) :=
  IsPrestack.glue (F := F) (J := J)
    (R := Sieve.pullback a₁ (Sieve.ofArrows (X j₁) (u j₁)) ⊓
      Sieve.pullback a₂ (Sieve.ofArrows (X j₂) (u j₂)))
    (J.intersection_covering (J.pullback_stable a₁ (hu j₁)) (J.pullback_stable a₂ (hu j₂)))
    (fun _ r ra₁ ra₂ hra₁ hra₂ hr ↦
      have h₁ : ∃ k : ι j₁, ∃ b₁ : _ ⟶ X j₁ k, b₁ ≫ u j₁ k = r ≫ a₁ := by
        obtain ⟨_, b₁, _, ⟨k₁⟩, hb₁⟩ := hr.1; exact ⟨k₁, b₁, hb₁⟩
      have h₂ : ∃ k : ι j₂, ∃ b₂ : _ ⟶ X j₂ k, b₂ ≫ u j₂ k = r ≫ a₂ := by
        obtain ⟨_, b₂, _, ⟨k₂⟩, hb₂⟩ := hr.2; exact ⟨k₂, b₂, hb₂⟩
      localTrans D M α (rq := r ≫ q) (ra₁ := ra₁) (ra₂ := ra₂)
        (hra₁ ▸ by rw [Category.assoc, ha₁]) (hra₂ ▸ by rw [Category.assoc, ha₂])
        h₁.choose_spec.choose h₂.choose_spec.choose
        (h₁.choose_spec.choose_spec.trans hra₁) (h₂.choose_spec.choose_spec.trans hra₂))
    (fun T r ra₁ ra₂ hra₁ hra₂ hr T' h r' r'a₁ r'a₂ hr'a₁ hr'a₂ hr' e ↦ by
      subst e hra₁ hra₂ hr'a₁ hr'a₂
      rw [pullHom_localTrans D M α (by rw [Category.assoc, ha₁]) (by rw [Category.assoc, ha₂])
        h _ _ _ _ _ _ _ (Category.assoc h r a₁).symm (Category.assoc h r a₂).symm
        (Category.assoc h r q).symm]
      exact localTrans_unique D M α ha₁ ha₂ (h ≫ r) _ _ _ _ _ _ _ _)

/-- Pulling back `gluedHom` along a morphism `r : Z ⟶ W` gives `localTrans`. -/
private lemma pullHom_gluedHom_eq_localTrans
    (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j))
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W Z : C} (q : W ⟶ S) {j₁ j₂ : κ} (a₁ : W ⟶ Y j₁) (a₂ : W ⟶ Y j₂)
    (ha₁ : a₁ ≫ p j₁ = q) (ha₂ : a₂ ≫ p j₂ = q) (r : Z ⟶ W)
    (ra₁ : Z ⟶ Y j₁) (ra₂ : Z ⟶ Y j₂) (rq : Z ⟶ S)
    {k₁ : ι j₁} {k₂ : ι j₂} (b₁ : Z ⟶ X j₁ k₁) (b₂ : Z ⟶ X j₂ k₂)
    (hb₁ : b₁ ≫ u j₁ k₁ = r ≫ a₁) (hb₂ : b₂ ≫ u j₂ k₂ = r ≫ a₂)
    (hra₁ : r ≫ a₁ = ra₁) (hra₂ : r ≫ a₂ = ra₂) (hrq : r ≫ q = rq) :
    pullHom (gluedHom hu D M α q a₁ a₂ ha₁ ha₂) r ra₁ ra₂ hra₁ hra₂ =
      localTrans D M α (by rw [← hra₁, Category.assoc, ha₁, hrq])
        (by rw [← hra₂, Category.assoc, ha₂, hrq]) b₁ b₂ (hb₁.trans hra₁) (hb₂.trans hra₂) := by
  subst hra₁ hra₂ hrq
  have hr : (Sieve.pullback a₁ (Sieve.ofArrows (X j₁) (u j₁)) ⊓
      Sieve.pullback a₂ (Sieve.ofArrows (X j₂) (u j₂))) r :=
    ⟨⟨_, b₁, _, ⟨k₁⟩, hb₁⟩, ⟨_, b₂, _, ⟨k₂⟩, hb₂⟩⟩
  rw [gluedHom, IsPrestack.pullHom_glue _ _ _ r (r ≫ a₁) (r ≫ a₂) rfl rfl hr]
  exact localTrans_unique D M α ha₁ ha₂ r _ b₁ _ b₂ _ hb₁ _ hb₂

/-- Compatibility of `gluedHom` with pullback along `g : W' ⟶ W`. -/
private lemma pullHom_gluedHom (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j))
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W' W : C} (g : W' ⟶ W) (q : W ⟶ S) (q' : W' ⟶ S) (hq : g ≫ q = q')
    {j₁ j₂ : κ} (a₁ : W ⟶ Y j₁) (a₂ : W ⟶ Y j₂)
    (ha₁ : a₁ ≫ p j₁ = q) (ha₂ : a₂ ≫ p j₂ = q)
    (ga₁ : W' ⟶ Y j₁) (ga₂ : W' ⟶ Y j₂) (hga₁ : g ≫ a₁ = ga₁) (hga₂ : g ≫ a₂ = ga₂) :
    pullHom (gluedHom hu D M α q a₁ a₂ ha₁ ha₂) g ga₁ ga₂ hga₁ hga₂ =
      gluedHom hu D M α q' ga₁ ga₂ (by rw [← hga₁, Category.assoc, ha₁, hq])
        (by rw [← hga₂, Category.assoc, ha₂, hq]) := by
  subst hga₁ hga₂ hq
  let R : Sieve W' :=
    Sieve.pullback (g ≫ a₁) (Sieve.ofArrows (X j₁) (u j₁)) ⊓
      Sieve.pullback (g ≫ a₂) (Sieve.ofArrows (X j₂) (u j₂))
  have hR : R ∈ J W' := J.intersection_covering (J.pullback_stable _ (hu j₁))
    (J.pullback_stable _ (hu j₂))
  refine IsPrestack.pullHom_ext (F := F) (J := J) hR fun Z r hr ↦ ?_
  obtain ⟨_, b₁, _, ⟨k₁⟩, hb₁⟩ := hr.1
  obtain ⟨_, b₂, _, ⟨k₂⟩, hb₂⟩ := hr.2
  rw [pullHom_pullHom,
    pullHom_gluedHom_eq_localTrans hu D M α q a₁ a₂ ha₁ ha₂ (r ≫ g) _ _ _
      b₁ b₂ (by rw [hb₁, Category.assoc]) (by rw [hb₂, Category.assoc])
      (Category.assoc r g a₁) (Category.assoc r g a₂) (Category.assoc r g q),
    pullHom_gluedHom_eq_localTrans hu D M α (g ≫ q) (g ≫ a₁) (g ≫ a₂) _ _ r _ _ _
      b₁ b₂ hb₁ hb₂ rfl rfl rfl]

/-- The descent datum along `p` assembled from the descended objects `M j` and transition
isomorphisms `gluedHom`. -/
@[simps]
private noncomputable def gluedDatum (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j))
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j) :
    F.DescentData p where
  obj := M
  hom _ q _ _ a₁ a₂ ha₁ ha₂ := gluedHom hu D M α q a₁ a₂ ha₁ ha₂
  pullHom_hom _ _ g q q' hq _ _ a₁ a₂ ha₁ ha₂ ga₁ ga₂ hga₁ hga₂ :=
    pullHom_gluedHom hu D M α g q q' hq a₁ a₂ ha₁ ha₂ ga₁ ga₂ hga₁ hga₂
  hom_self W q j a ha := by
    have hR : Sieve.pullback a (Sieve.ofArrows (X j) (u j)) ∈ J W :=
      J.pullback_stable a (hu j)
    refine IsPrestack.pullHom_ext (F := F) (J := J) hR fun Z r hr ↦ ?_
    obtain ⟨_, b, _, ⟨k⟩, hb⟩ := hr
    rw [pullHom_id_self, pullHom_gluedHom_eq_localTrans hu D M α q a a ha ha r _ _ _ b b
      hb hb rfl rfl rfl, localTrans_self]
  hom_comp W q j₁ j₂ j₃ a₁ a₂ a₃ ha₁ ha₂ ha₃ := by
    let R : Sieve W :=
      Sieve.pullback a₁ (Sieve.ofArrows (X j₁) (u j₁)) ⊓
        (Sieve.pullback a₂ (Sieve.ofArrows (X j₂) (u j₂)) ⊓
          Sieve.pullback a₃ (Sieve.ofArrows (X j₃) (u j₃)))
    have hR : R ∈ J W := J.intersection_covering (J.pullback_stable a₁ (hu j₁))
      (J.intersection_covering (J.pullback_stable a₂ (hu j₂)) (J.pullback_stable a₃ (hu j₃)))
    refine IsPrestack.pullHom_ext (F := F) (J := J) hR fun Z r hr ↦ ?_
    obtain ⟨_, b₁, _, ⟨k₁⟩, hb₁⟩ := hr.1
    obtain ⟨_, b₂, _, ⟨k₂⟩, hb₂⟩ := hr.2.1
    obtain ⟨_, b₃, _, ⟨k₃⟩, hb₃⟩ := hr.2.2
    rw [pullHom_comp _ _ r (r ≫ a₁) (r ≫ a₂) (r ≫ a₃) rfl rfl rfl,
      pullHom_gluedHom_eq_localTrans hu D M α q a₁ a₂ ha₁ ha₂ r _ _ _ b₁ b₂ hb₁ hb₂ rfl rfl rfl,
      pullHom_gluedHom_eq_localTrans hu D M α q a₂ a₃ ha₂ ha₃ r _ _ _ b₂ b₃ hb₂ hb₃ rfl rfl rfl,
      pullHom_gluedHom_eq_localTrans hu D M α q a₁ a₃ ha₁ ha₃ r _ _ _ b₁ b₃ hb₁ hb₃ rfl rfl rfl,
      localTrans_comp]

/-- Explicit formula for `gluedHom` evaluated on morphisms already factored as `f₁ ≫ u j₁ k₁` and
`f₂ ≫ u j₂ k₂`. -/
private lemma gluedHom_comp (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j))
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W : C} (q : W ⟶ S) {jk₁ jk₂ : Σ j, ι j}
    (f₁ : W ⟶ X jk₁.1 jk₁.2) (f₂ : W ⟶ X jk₂.1 jk₂.2)
    (hf₁ : f₁ ≫ u jk₁.1 jk₁.2 ≫ p jk₁.1 = q) (hf₂ : f₂ ≫ u jk₂.1 jk₂.2 ≫ p jk₂.1 = q) :
    gluedHom hu D M α q (f₁ ≫ u jk₁.1 jk₁.2) (f₂ ≫ u jk₂.1 jk₂.2)
        (by rw [Category.assoc, hf₁]) (by rw [Category.assoc, hf₂]) =
      localTrans D M α (by rw [Category.assoc, hf₁]) (by rw [Category.assoc, hf₂])
        f₁ f₂ rfl rfl := by
  rw [← pullHom_id (gluedHom hu D M α q (f₁ ≫ u jk₁.1 jk₁.2) (f₂ ≫ u jk₂.1 jk₂.2)
      (by rw [Category.assoc, hf₁]) (by rw [Category.assoc, hf₂])),
    pullHom_gluedHom_eq_localTrans hu D M α q (f₁ ≫ u jk₁.1 jk₁.2) (f₂ ≫ u jk₂.1 jk₂.2)
      _ _ (𝟙 W) _ _ _ f₁ f₂ (by simp) (by simp)
      (Category.id_comp _) (Category.id_comp _) (Category.id_comp _)]

/-- The component isomorphism `(p j)^* N ≅ M j` extracted from `β`. -/
private noncomputable def βIso (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j))
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    (N : F.obj (.mk (op S)))
    (β : (F.toDescentData p).obj N ≅ gluedDatum hu D M α) (j : κ) :
    (F.map (p j).op.toLoc).toFunctor.obj N ≅ M j :=
  DescentData.isoApp β j

private lemma βIso_hom (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j))
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    (N : F.obj (.mk (op S)))
    (β : (F.toDescentData p).obj N ≅ gluedDatum hu D M α) (j : κ) :
    (βIso hu D M α N β j).hom = β.hom.hom j :=
  DescentData.isoApp_hom β j

/-- The component isomorphism `(u ≫ p)^* N ≅ D.obj jk` for `descendIso`. -/
private noncomputable def descendComponentIso
    (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j))
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    (N : F.obj (.mk (op S)))
    (β : (F.toDescentData p).obj N ≅ gluedDatum hu D M α)
    (jk : Σ j, ι j) :
    (F.map (u jk.1 jk.2 ≫ p jk.1).op.toLoc).toFunctor.obj N ≅ D.obj jk :=
  F.compIso (p jk.1).op (u jk.1 jk.2).op (u jk.1 jk.2 ≫ p jk.1).op op_comp.symm N ≪≫
    (F.map (u jk.1 jk.2).op.toLoc).toFunctor.mapIso (βIso hu D M α N β jk.1) ≪≫
    αIso D M α jk.1 jk.2

/-- Reassociate the `descendIso` component along a single factorization `f ≫ u ≫ p = q` from
`f^* (u ≫ p)^* N ⟶ f^* (D.obj jk)` to `(f ≫ u)^* p^* N ⟶ f^* (D.obj jk)`. -/
@[reassoc]
private lemma descendIso_component_eq (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j))
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    (N : F.obj (.mk (op S)))
    (β : (F.toDescentData p).obj N ≅ gluedDatum hu D M α)
    {W : C} (q : W ⟶ S) (jk : Σ j, ι j)
    (f : W ⟶ X jk.1 jk.2) (hf : f ≫ u jk.1 jk.2 ≫ p jk.1 = q) :
    (F.compIso (u jk.1 jk.2 ≫ p jk.1).op f.op q.op (by rw [← op_comp, hf]) N).hom ≫
      (F.map f.op.toLoc).toFunctor.map (descendComponentIso hu D M α N β jk).hom =
      (F.compIso (p jk.1).op (f ≫ u jk.1 jk.2).op q.op
          (by rw [← op_comp, Category.assoc, hf]) N).hom ≫
        (F.map (f ≫ u jk.1 jk.2).op.toLoc).toFunctor.map (βIso hu D M α N β jk.1).hom ≫
        (F.compIso (u jk.1 jk.2).op f.op (f ≫ u jk.1 jk.2).op op_comp.symm (M jk.1)).hom ≫
        (F.map f.op.toLoc).toFunctor.map (αIso D M α jk.1 jk.2).hom := by
  dsimp only [descendComponentIso, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp]
  rw [F.compIso_hom_comp_map_compIso_hom_assoc (p jk.1).op (u jk.1 jk.2).op f.op
      (u jk.1 jk.2 ≫ p jk.1).op (f ≫ u jk.1 jk.2).op q.op op_comp.symm op_comp.symm
      (by rw [← op_comp, hf]) (by rw [← op_comp, Category.assoc, hf]) N,
    ← F.compIso_hom_naturality_assoc (u jk.1 jk.2).op f.op (f ≫ u jk.1 jk.2).op
      op_comp.symm (βIso hu D M α N β jk.1).hom]

/-- Component-wise transition compatibility for `descendIso`. -/
private lemma descendIso_comm (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j))
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    (N : F.obj (.mk (op S)))
    (β : (F.toDescentData p).obj N ≅ gluedDatum hu D M α)
    {W : C} (q : W ⟶ S) {jk₁ jk₂ : Σ j, ι j}
    (f₁ : W ⟶ X jk₁.1 jk₁.2) (f₂ : W ⟶ X jk₂.1 jk₂.2)
    (hf₁ : f₁ ≫ u jk₁.1 jk₁.2 ≫ p jk₁.1 = q) (hf₂ : f₂ ≫ u jk₂.1 jk₂.2 ≫ p jk₂.1 = q) :
    (F.map f₁.op.toLoc).toFunctor.map (descendComponentIso hu D M α N β jk₁).hom ≫
      D.hom q (i₁ := jk₁) (i₂ := jk₂) f₁ f₂ hf₁ hf₂ =
    ((F.toDescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1)).obj N).hom q f₁ f₂ hf₁ hf₂ ≫
      (F.map f₂.op.toLoc).toFunctor.map (descendComponentIso hu D M α N β jk₂).hom := by
  have ha₁ : (f₁ ≫ u jk₁.1 jk₁.2) ≫ p jk₁.1 = q := by rw [Category.assoc, hf₁]
  have ha₂ : (f₂ ≫ u jk₂.1 jk₂.2) ≫ p jk₂.1 = q := by rw [Category.assoc, hf₂]
  have hβ : (F.compIso (p jk₁.1).op (f₁ ≫ u jk₁.1 jk₁.2).op q.op
          (by rw [← op_comp, ha₁]) N).hom ≫
        (F.map (f₁ ≫ u jk₁.1 jk₁.2).op.toLoc).toFunctor.map (βIso hu D M α N β jk₁.1).hom ≫
        localTrans D M α ha₁ ha₂ f₁ f₂ rfl rfl =
      (F.compIso (p jk₂.1).op (f₂ ≫ u jk₂.1 jk₂.2).op q.op
          (by rw [← op_comp, ha₂]) N).hom ≫
        (F.map (f₂ ≫ u jk₂.1 jk₂.2).op.toLoc).toFunctor.map (βIso hu D M α N β jk₂.1).hom := by
    refine (DescentData.hom_toDescentData_obj_iff (F := F) (f := p) q
      (f₁ ≫ u jk₁.1 jk₁.2) (f₂ ≫ u jk₂.1 jk₂.2) ha₁ ha₂ _ _ _).1 ?_
    have h := β.hom.comm q (f₁ ≫ u jk₁.1 jk₁.2) (f₂ ≫ u jk₂.1 jk₂.2) ha₁ ha₂
    rw [gluedDatum_hom, gluedHom_comp hu D M α q f₁ f₂ hf₁ hf₂, ← βIso_hom, ← βIso_hom] at h
    exact h
  have hgoal : (F.compIso (u jk₁.1 jk₁.2 ≫ p jk₁.1).op f₁.op q.op
          (by rw [← op_comp, hf₁]) N).hom ≫
        (F.map f₁.op.toLoc).toFunctor.map (descendComponentIso hu D M α N β jk₁).hom ≫
        D.hom q (i₁ := jk₁) (i₂ := jk₂) f₁ f₂ hf₁ hf₂ =
      (F.compIso (u jk₂.1 jk₂.2 ≫ p jk₂.1).op f₂.op q.op
          (by rw [← op_comp, hf₂]) N).hom ≫
        (F.map f₂.op.toLoc).toFunctor.map (descendComponentIso hu D M α N β jk₂).hom := by
    rw [descendIso_component_eq_assoc hu D M α N β q jk₁ f₁ hf₁,
      descendIso_component_eq hu D M α N β q jk₂ f₂ hf₂,
      ← localTrans_comp_αIso D M α ha₁ ha₂ f₁ f₂ rfl rfl,
      ← Category.assoc _ (localTrans D M α ha₁ ha₂ f₁ f₂ rfl rfl),
      ← Category.assoc _ (_ ≫ localTrans D M α ha₁ ha₂ f₁ f₂ rfl rfl), hβ]
    simp only [Category.assoc]
  exact (DescentData.hom_toDescentData_obj_iff (F := F)
    (f := fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1) q f₁ f₂ hf₁ hf₂ _ _ _).2 hgoal

/-- Combining the descent isomorphism `β : toDescentData p N ≅ gluedDatum ...` with the local
isomorphisms `α j : toDescentData (u j) (M j) ≅ restrictDatum D j` produces an isomorphism
`(toDescentData (u j k ≫ p j)).obj N ≅ D`. -/
private noncomputable def descendIso (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j))
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    (N : F.obj (.mk (op S)))
    (β : (F.toDescentData p).obj N ≅ gluedDatum hu D M α) :
    (F.toDescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1)).obj N ≅ D :=
  DescentData.isoMk
    (fun jk ↦ descendComponentIso hu D M α N β jk)
    (fun _ q _ _ f₁ f₂ hf₁ hf₂ ↦ descendIso_comm hu D M α N β q f₁ f₂ hf₁ hf₂)

end Comp

/-- **Transitivity of effective descent (`IsStackFor`) along `J`-covering compositions.** If `F`
is a prestack for `J`, `F` has effective descent for `p : ∀ j, Y j ⟶ S`, and each
`u j : ∀ k, X j k ⟶ Y j` is a `J`-covering family for which `F` has effective descent, then `F`
has effective descent for the composite family `u j k ≫ p j`. -/
theorem IsStackFor.comp {J : GrothendieckTopology C} [F.IsPrestack J]
    {S : C} {κ : Type t} {Y : κ → C} {p : ∀ j, Y j ⟶ S} (hp : F.IsStackFor (.ofArrows Y p))
    {ι : κ → Type t'} {X : ∀ j, ι j → C} (u : ∀ j k, X j k ⟶ Y j)
    (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j))
    (hu_stack : ∀ j, F.IsStackFor (.ofArrows (X j) (u j))) :
    F.IsStackFor (.ofArrows (fun jk : Σ j, ι j ↦ X jk.1 jk.2) (fun jk ↦ u jk.1 jk.2 ≫ p jk.1)) := by
  have hpre := hp.isPrestackFor.comp u hu
  rw [isPrestackFor_ofArrows_iff] at hpre
  obtain ⟨hff⟩ := hpre
  have := hff.full
  have := hff.faithful
  rw [isStackFor_ofArrows_iff] at hp ⊢
  have hu_eqv (j : κ) : (F.toDescentData (u j)).IsEquivalence :=
    (isStackFor_ofArrows_iff F (u j)).1 (hu_stack j)
  have : (F.toDescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1)).EssSurj := ⟨fun D ↦ by
    let M (j : κ) := (F.toDescentData (u j)).objPreimage (Comp.restrictDatum D j)
    let α (j : κ) := (F.toDescentData (u j)).objObjPreimageIso (Comp.restrictDatum D j)
    let Dp := Comp.gluedDatum hu D M α
    let N := (F.toDescentData p).objPreimage Dp
    let β := (F.toDescentData p).objObjPreimageIso Dp
    exact ⟨N, ⟨Comp.descendIso hu D M α N β⟩⟩⟩
  exact {}

/-- **Base-change locality of effective descent (sieve form).** If `F` is a prestack for `J`, `R`
is a `J`-covering sieve on `S`, `v` is a `J`-covering family of `S` for which `F` has effective
descent, and `F` has effective descent for `R.pullback (v a)` for every `a`, then `F` has
effective descent for `R`. -/
theorem IsStackFor.of_pullback' {J : GrothendieckTopology C} [F.IsPrestack J]
    {S : C} {R : Sieve S} (hR : R ∈ J S)
    {κ : Type t} {V : κ → C} {v : ∀ a, V a ⟶ S} (hv : Sieve.ofArrows V v ∈ J S)
    (hv_stack : F.IsStackFor (.ofArrows V v))
    (hR' : ∀ a, F.IsStackFor (R.pullback (v a)).arrows) :
    F.IsStackFor R.arrows := by
  let u (a : κ) (g : (R.pullback (v a)).arrows.category) : g.obj.left ⟶ V a := g.obj.hom
  have hu (a : κ) : Sieve.ofArrows _ (u a) ∈ J (V a) := by
    rw [Sieve.ofArrows_category]
    exact J.pullback_stable (v a) hR
  have hcomp := hv_stack.comp u hu fun a ↦ by
    rw [Presieve.ofArrows_category]
    exact hR' a
  have hmem : Sieve.ofArrows _ (fun ag : Σ a, (R.pullback (v a)).arrows.category ↦
      u ag.1 ag.2 ≫ v ag.1) ∈ J S := by
    rw [Sieve.ofArrows, ← Presieve.bindOfArrows_ofArrows v u]
    exact J.bindOfArrows hv hu
  have hle : Sieve.ofArrows _ (fun ag : Σ a, (R.pullback (v a)).arrows.category ↦
      u ag.1 ag.2 ≫ v ag.1) ≤ R :=
    (Sieve.generate_le_iff _ _).2 (Presieve.ofArrows_le_iff.2 fun ag ↦ ag.2.property)
  rw [← IsStackFor_generate_iff] at hcomp
  exact hcomp.of_le' F hmem hle

/-- **Base-change locality of effective descent.** If `F` is a prestack for `J`, `f` and `v` are
`J`-covering families of `S` whose pointwise pullbacks exist, `F` has effective descent for `v`,
and `F` has effective descent for the pullback of `f` along every `v a`, then `F` has effective
descent for `f`. -/
theorem IsStackFor.of_pullback {J : GrothendieckTopology C} [F.IsPrestack J]
    {S : C} {ι : Type t} {X : ι → C} {f : ∀ i, X i ⟶ S} (hf : Sieve.ofArrows X f ∈ J S)
    {κ : Type t'} {V : κ → C} {v : ∀ a, V a ⟶ S} (hv : Sieve.ofArrows V v ∈ J S)
    [∀ i a, HasPullback (f i) (v a)]
    (hv_stack : F.IsStackFor (.ofArrows V v))
    (hf' : ∀ a, F.IsStackFor (.ofArrows (fun i ↦ pullback (f i) (v a))
      (fun i ↦ pullback.snd (f i) (v a)))) :
    F.IsStackFor (.ofArrows X f) := by
  rw [← IsStackFor_generate_iff]
  refine IsStackFor.of_pullback' hf hv hv_stack fun a ↦ ?_
  have : ∀ i, HasPullback (f i) (v a) := fun i ↦ inferInstance
  rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback, IsStackFor_generate_iff]
  exact hf' a

end CategoryTheory.Pseudofunctor
