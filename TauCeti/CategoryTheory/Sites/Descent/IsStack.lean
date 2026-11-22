/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack

import Mathlib.CategoryTheory.Sites.Descent.Precoverage
import TauCeti.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Transitivity and base-change locality of effective descent

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor and `J` a Grothendieck topology on `C`.
This file establishes closure properties for stacks and the local effective-descent condition
`F.IsStackFor`.

## Main results

* `CategoryTheory.Pseudofunctor.DescentData.isoApp`: extract component isomorphisms from an
  isomorphism of descent data.
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

namespace DescentData

/-- Extract the component isomorphism `D₁.obj i ≅ D₂.obj i` from an isomorphism of descent data
`e : D₁ ≅ D₂`. -/
-- Exposed: the generated `@[simps]` field lemmas are `rfl`-proofs about this body.
@[expose, simps]
def isoApp {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {D₁ D₂ : F.DescentData f} (e : D₁ ≅ D₂) (i : ι) :
    D₁.obj i ≅ D₂.obj i where
  hom := e.hom.hom i
  inv := e.inv.hom i
  hom_inv_id := congrArg (fun φ : D₁ ⟶ D₁ ↦ φ.hom i) e.hom_inv_id
  inv_hom_id := congrArg (fun φ : D₂ ⟶ D₂ ↦ φ.hom i) e.inv_hom_id

end DescentData

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
    ⟨DescentData.isoMk (fun _ ↦ (Cat.Hom.toNatIso (F.mapId (.mk (op S)))).app (D.obj PUnit.unit))
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

/-- The component isomorphism `(u j k)^* (M j) ≅ D.obj ⟨j, k⟩` obtained from `DescentData.isoApp`
and `F.mapId`. -/
private def αIso (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j) (j : κ) (k : ι j) :
    (F.map (u j k).op.toLoc).toFunctor.obj (M j) ≅ D.obj ⟨j, k⟩ :=
  DescentData.isoApp (α j) k ≪≫ (Cat.Hom.toNatIso (F.mapId (.mk (op (X j k))))).app (D.obj ⟨j, k⟩)

private lemma map_αIso_hom (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {Z : C} {j : κ} {k : ι j} (b : Z ⟶ X j k) :
    (F.map b.op.toLoc).toFunctor.map (αIso D M α j k).hom =
      (F.map b.op.toLoc).toFunctor.map (DescentData.isoApp (α j) k).hom ≫
        (F.map b.op.toLoc).toFunctor.map
          ((F.mapId (.mk (op (X j k)))).hom.toNatTrans.app (D.obj ⟨j, k⟩)) := by
  dsimp [αIso]; erw [Functor.map_comp]; rfl

private lemma map_αIso_inv (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {Z : C} {j : κ} {k : ι j} (b : Z ⟶ X j k) :
    (F.map b.op.toLoc).toFunctor.map (αIso D M α j k).inv =
      (F.map b.op.toLoc).toFunctor.map
          ((F.mapId (.mk (op (X j k)))).inv.toNatTrans.app (D.obj ⟨j, k⟩)) ≫
        (F.map b.op.toLoc).toFunctor.map (DescentData.isoApp (α j) k).inv := by
  dsimp [αIso]; erw [Functor.map_comp]; rfl

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
      (DescentData.isoApp (α j₁) k₁).hom b₁ ra₁ b₁ hb₁ (Category.comp_id b₁) ≫
    D.hom rq (i₁ := ⟨j₁, k₁⟩) (i₂ := ⟨j₂, k₂⟩) b₁ b₂
      (by rw [← Category.assoc, hb₁, hra₁]) (by rw [← Category.assoc, hb₂, hra₂]) ≫
    pullHom (F := F) (X₁ := X j₂ k₂) (X₂ := Y j₂) (M₁ := D.obj ⟨j₂, k₂⟩) (M₂ := M j₂)
      (f₁ := 𝟙 (X j₂ k₂)) (f₂ := u j₂ k₂)
      (DescentData.isoApp (α j₂) k₂).inv b₂ b₂ ra₂ (Category.comp_id b₂) hb₂

private lemma localTrans_eq (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {Z : C} {rq : Z ⟶ S} {j₁ j₂ : κ} {ra₁ : Z ⟶ Y j₁} {ra₂ : Z ⟶ Y j₂}
    (hra₁ : ra₁ ≫ p j₁ = rq) (hra₂ : ra₂ ≫ p j₂ = rq)
    {k₁ : ι j₁} {k₂ : ι j₂} (b₁ : Z ⟶ X j₁ k₁) (b₂ : Z ⟶ X j₂ k₂)
    (hb₁ : b₁ ≫ u j₁ k₁ = ra₁) (hb₂ : b₂ ≫ u j₂ k₂ = ra₂) :
    localTrans D M α hra₁ hra₂ b₁ b₂ hb₁ hb₂ =
      (F.mapComp' (u j₁ k₁).op.toLoc b₁.op.toLoc ra₁.op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, hb₁])).hom.toNatTrans.app (M j₁) ≫
        (F.map b₁.op.toLoc).toFunctor.map (αIso D M α j₁ k₁).hom ≫
        D.hom rq (i₁ := ⟨j₁, k₁⟩) (i₂ := ⟨j₂, k₂⟩) b₁ b₂
          (by rw [← Category.assoc, hb₁, hra₁]) (by rw [← Category.assoc, hb₂, hra₂]) ≫
        (F.map b₂.op.toLoc).toFunctor.map (αIso D M α j₂ k₂).inv ≫
        (F.mapComp' (u j₂ k₂).op.toLoc b₂.op.toLoc ra₂.op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, hb₂])).inv.toNatTrans.app (M j₂) := by
  simp only [localTrans, pullHom, op_id, Quiver.Hom.id_toLoc,
    F.mapComp'_id_comp_inv_app, F.mapComp'_id_comp_hom_app]
  erw [map_αIso_hom, map_αIso_inv]
  refine Eq.trans (Category.assoc ((F.mapComp' (u j₁ k₁).op.toLoc b₁.op.toLoc ra₁.op.toLoc
    (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, hb₁])).hom.toNatTrans.app (M j₁)) _ _) ?_
  refine congrArg₂ (· ≫ ·) rfl (congrArg₂ (· ≫ ·) rfl (congrArg₂ (· ≫ ·) rfl ?_))
  exact (Category.assoc ((F.map b₂.op.toLoc).toFunctor.map
    ((F.mapId (.mk (op (X j₂ k₂)))).inv.toNatTrans.app (D.obj ⟨j₂, k₂⟩))) _ _).symm

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
  refine congrArg (_ ≫ ·) (congrArg (· ≫ _) ?_)
  exact D.pullHom_hom g rq (g ≫ rq) rfl (i₁ := ⟨j₁, k₁⟩) (i₂ := ⟨j₂, k₂⟩)
    b₁ b₂ (by rw [← Category.assoc, hb₁, hra₁]) (by rw [← Category.assoc, hb₂, hra₂])
    (g ≫ b₁) (g ≫ b₂) rfl rfl

/-- Given a descent datum `D` for `u j k ≫ p j`, objects `M j` on `Y j`, and isomorphisms
`α j : (toDescentData (u j)).obj (M j) ≅ restrictDatum D j`, this is the local transition map
`r^* a₁^* M j₁ ⟶ r^* a₂^* M j₂` obtained from factorizations `b₁ ≫ u j₁ k₁ = r ≫ a₁` and
`b₂ ≫ u j₂ k₂ = r ≫ a₂`. -/
private def localHom (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W Z : C} {q : W ⟶ S} {j₁ j₂ : κ} {a₁ : W ⟶ Y j₁} {a₂ : W ⟶ Y j₂}
    (ha₁ : a₁ ≫ p j₁ = q) (ha₂ : a₂ ≫ p j₂ = q) (r : Z ⟶ W)
    {k₁ : ι j₁} {k₂ : ι j₂} (b₁ : Z ⟶ X j₁ k₁) (b₂ : Z ⟶ X j₂ k₂)
    (hb₁ : b₁ ≫ u j₁ k₁ = r ≫ a₁) (hb₂ : b₂ ≫ u j₂ k₂ = r ≫ a₂) :
    (F.map r.op.toLoc).toFunctor.obj ((F.map a₁.op.toLoc).toFunctor.obj (M j₁)) ⟶
      (F.map r.op.toLoc).toFunctor.obj ((F.map a₂.op.toLoc).toFunctor.obj (M j₂)) :=
  (F.mapComp' a₁.op.toLoc r.op.toLoc (r ≫ a₁).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app (M j₁) ≫
    localTrans D M α (by rw [Category.assoc, ha₁]) (by rw [Category.assoc, ha₂]) b₁ b₂ hb₁ hb₂ ≫
    (F.mapComp' a₂.op.toLoc r.op.toLoc (r ≫ a₂).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app (M j₂)

/-- Conjugate `localHom` by `F.mapComp'` to cancel its outer `mapComp' a r` factors across
arbitrary equal arrow representatives `ra₁ = r ≫ a₁`, `ra₂ = r ≫ a₂`, and `rq = r ≫ q`. -/
private lemma mapComp'_hom_localHom_mapComp'_inv
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W Z : C} {q : W ⟶ S} {j₁ j₂ : κ} {a₁ : W ⟶ Y j₁} {a₂ : W ⟶ Y j₂}
    (ha₁ : a₁ ≫ p j₁ = q) (ha₂ : a₂ ≫ p j₂ = q) (r : Z ⟶ W)
    {k₁ : ι j₁} {k₂ : ι j₂} (b₁ : Z ⟶ X j₁ k₁) (b₂ : Z ⟶ X j₂ k₂)
    (hb₁ : b₁ ≫ u j₁ k₁ = r ≫ a₁) (hb₂ : b₂ ≫ u j₂ k₂ = r ≫ a₂)
    (ra₁ : Z ⟶ Y j₁) (ra₂ : Z ⟶ Y j₂) (rq : Z ⟶ S)
    (hra₁ : r ≫ a₁ = ra₁) (hra₂ : r ≫ a₂ = ra₂) (hrq : r ≫ q = rq) :
    (F.mapComp' a₁.op.toLoc r.op.toLoc ra₁.op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, hra₁])).hom.toNatTrans.app (M j₁) ≫
      localHom D M α ha₁ ha₂ r b₁ b₂ hb₁ hb₂ ≫
      (F.mapComp' a₂.op.toLoc r.op.toLoc ra₂.op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, hra₂])).inv.toNatTrans.app (M j₂) =
      localTrans D M α (by rw [← hra₁, Category.assoc, ha₁, hrq])
        (by rw [← hra₂, Category.assoc, ha₂, hrq]) b₁ b₂ (hb₁.trans hra₁) (hb₂.trans hra₂) := by
  subst hra₁ hra₂ hrq
  simp only [localHom, Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc,
    Cat.Hom.hom_inv_id_toNatTrans_app, Category.comp_id]

private lemma αIso_comm (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W Z : C} {q : W ⟶ S} {j : κ} {a : W ⟶ Y j} (ha : a ≫ p j = q) (r : Z ⟶ W)
    {k₁ k₂ : ι j} (b₁ : Z ⟶ X j k₁) (b₂ : Z ⟶ X j k₂)
    (hb₁ : b₁ ≫ u j k₁ = r ≫ a) (hb₂ : b₂ ≫ u j k₂ = r ≫ a) :
    (F.map b₁.op.toLoc).toFunctor.map (αIso D M α j k₁).hom ≫
      D.hom (r ≫ q) (i₁ := ⟨j, k₁⟩) (i₂ := ⟨j, k₂⟩) b₁ b₂
        (by rw [← Category.assoc, hb₁, Category.assoc, ha])
        (by rw [← Category.assoc, hb₂, Category.assoc, ha]) =
      ((F.mapComp' (u j k₁).op.toLoc b₁.op.toLoc (r ≫ a).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, hb₁])).inv.toNatTrans.app (M j) ≫
        (F.mapComp' (u j k₂).op.toLoc b₂.op.toLoc (r ≫ a).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, hb₂])).hom.toNatTrans.app (M j)) ≫
      (F.map b₂.op.toLoc).toFunctor.map (αIso D M α j k₂).hom := by
  have h : (F.map b₁.op.toLoc).toFunctor.map (DescentData.isoApp (α j) k₁).hom ≫
      DescentData.pullFunctorObjHom (p := p j) (α := fun k ↦ ⟨j, k⟩) (p' := fun _ ↦ 𝟙 _)
        (by simp) D (b₁ ≫ u j k₁) b₁ b₂ rfl (hb₂.trans hb₁.symm) =
      ((F.mapComp' (u j k₁).op.toLoc b₁.op.toLoc (r ≫ a).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, hb₁])).inv.toNatTrans.app (M j) ≫
        (F.mapComp' (u j k₂).op.toLoc b₂.op.toLoc (r ≫ a).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, hb₂])).hom.toNatTrans.app (M j)) ≫
      (F.map b₂.op.toLoc).toFunctor.map (DescentData.isoApp (α j) k₂).hom := by
    have h₀ := (α j).hom.comm (r ≫ a) b₁ b₂ hb₁ hb₂
    dsimp only [toDescentData, DescentData.ofObj, restrictDatum, DescentData.pullFunctor,
      DescentData.pullFunctorObj] at h₀
    exact h₀
  rw [DescentData.pullFunctorObjHom_eq (p := p j) (α := fun k ↦ ⟨j, k⟩) (p' := fun _ ↦ 𝟙 _)
    (by simp) D (b₁ ≫ u j k₁) b₁ b₂ (r ≫ q) b₁ b₂ rfl (hb₂.trans hb₁.symm)
    (by rw [hb₁, Category.assoc, ha]) (Category.comp_id _) (Category.comp_id _)] at h
  simp only [op_id, Quiver.Hom.id_toLoc, F.mapComp'_id_comp_inv_app_assoc,
    F.mapComp'_id_comp_hom_app] at h
  have hcancel : (F.map b₂.op.toLoc).toFunctor.map
      ((F.mapId (.mk (op (X j k₂)))).inv.toNatTrans.app (D.obj ⟨j, k₂⟩)) ≫
      (F.map b₂.op.toLoc).toFunctor.map
        ((F.mapId (.mk (op (X j k₂)))).hom.toNatTrans.app (D.obj ⟨j, k₂⟩)) = 𝟙 _ := by
    rw [← Functor.map_comp, Cat.Hom.inv_hom_id_toNatTrans_app, Functor.map_id]
  have h' := congrArg (· ≫ (F.map b₂.op.toLoc).toFunctor.map
    ((F.mapId (.mk (op (X j k₂)))).hom.toNatTrans.app (D.obj ⟨j, k₂⟩))) h
  conv_lhs at h' =>
    erw [Category.assoc, Category.assoc, Category.assoc, hcancel, Category.comp_id]
  conv_rhs at h' => erw [Category.assoc]
  erw [map_αIso_hom, map_αIso_hom, Category.assoc]
  exact h'

private lemma localHom_unique (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W Z : C} {q : W ⟶ S} {j₁ j₂ : κ} {a₁ : W ⟶ Y j₁} {a₂ : W ⟶ Y j₂}
    (ha₁ : a₁ ≫ p j₁ = q) (ha₂ : a₂ ≫ p j₂ = q) (r : Z ⟶ W)
    {k₁ k₁' : ι j₁} {k₂ k₂' : ι j₂}
    (b₁ : Z ⟶ X j₁ k₁) (b₁' : Z ⟶ X j₁ k₁') (b₂ : Z ⟶ X j₂ k₂) (b₂' : Z ⟶ X j₂ k₂')
    (hb₁ : b₁ ≫ u j₁ k₁ = r ≫ a₁) (hb₁' : b₁' ≫ u j₁ k₁' = r ≫ a₁)
    (hb₂ : b₂ ≫ u j₂ k₂ = r ≫ a₂) (hb₂' : b₂' ≫ u j₂ k₂' = r ≫ a₂) :
    localHom D M α ha₁ ha₂ r b₁ b₂ hb₁ hb₂ = localHom D M α ha₁ ha₂ r b₁' b₂' hb₁' hb₂' := by
  have h1 := αIso_comm D M α ha₁ r b₁ b₁' hb₁ hb₁'
  have h2 : (F.map b₂'.op.toLoc).toFunctor.map (αIso D M α j₂ k₂').inv ≫
      ((F.mapComp' (u j₂ k₂').op.toLoc b₂'.op.toLoc (r ≫ a₂).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, hb₂'])).inv.toNatTrans.app (M j₂) ≫
        (F.mapComp' (u j₂ k₂).op.toLoc b₂.op.toLoc (r ≫ a₂).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, hb₂])).hom.toNatTrans.app (M j₂)) =
      D.hom (r ≫ q) (i₁ := ⟨j₂, k₂'⟩) (i₂ := ⟨j₂, k₂⟩) b₂' b₂
        (by rw [← Category.assoc, hb₂', Category.assoc, ha₂])
        (by rw [← Category.assoc, hb₂, Category.assoc, ha₂]) ≫
      (F.map b₂.op.toLoc).toFunctor.map (αIso D M α j₂ k₂).inv := by
    rw [← cancel_epi ((F.map b₂'.op.toLoc).toFunctor.map (αIso D M α j₂ k₂').hom),
      ← cancel_mono ((F.map b₂.op.toLoc).toFunctor.map (αIso D M α j₂ k₂).hom)]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id,
      Category.id_comp, ← Functor.map_comp, Iso.inv_hom_id, Category.comp_id]
    simpa only [Category.assoc] using (αIso_comm D M α ha₂ r b₂' b₂ hb₂' hb₂).symm
  have hD : D.hom (r ≫ q) (i₁ := ⟨j₁, k₁⟩) (i₂ := ⟨j₂, k₂⟩) b₁ b₂
      (by rw [← Category.assoc, hb₁, Category.assoc, ha₁])
      (by rw [← Category.assoc, hb₂, Category.assoc, ha₂]) =
      D.hom (r ≫ q) (i₁ := ⟨j₁, k₁⟩) (i₂ := ⟨j₁, k₁'⟩) b₁ b₁'
        (by rw [← Category.assoc, hb₁, Category.assoc, ha₁])
        (by rw [← Category.assoc, hb₁', Category.assoc, ha₁]) ≫
      D.hom (r ≫ q) (i₁ := ⟨j₁, k₁'⟩) (i₂ := ⟨j₂, k₂'⟩) b₁' b₂'
        (by rw [← Category.assoc, hb₁', Category.assoc, ha₁])
        (by rw [← Category.assoc, hb₂', Category.assoc, ha₂]) ≫
      D.hom (r ≫ q) (i₁ := ⟨j₂, k₂'⟩) (i₂ := ⟨j₂, k₂⟩) b₂' b₂
        (by rw [← Category.assoc, hb₂', Category.assoc, ha₂])
        (by rw [← Category.assoc, hb₂, Category.assoc, ha₂]) := by
    simp [DescentData.hom_comp]
  unfold localHom
  rw [localTrans_eq, localTrans_eq, hD]
  simp only [Category.assoc]
  rw [reassoc_of% h1, Cat.Hom.hom_inv_id_toNatTrans_app_assoc, ← reassoc_of% h2,
    Cat.Hom.hom_inv_id_toNatTrans_app_assoc]

private lemma localHom_self (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W Z : C} {q : W ⟶ S} {j : κ} {a : W ⟶ Y j} (ha : a ≫ p j = q) (r : Z ⟶ W)
    {k : ι j} (b : Z ⟶ X j k) (hb : b ≫ u j k = r ≫ a) :
    localHom D M α ha ha r b b hb hb = 𝟙 _ := by
  unfold localHom localTrans
  rw [D.hom_self _ (i := ⟨j, k⟩) _ (by rw [← Category.assoc, hb, Category.assoc, ha]),
    Category.id_comp]
  erw [← pullHom_comp, Iso.hom_inv_id, pullHom_id_self]
  simp only [Category.id_comp, Cat.Hom.inv_hom_id_toNatTrans_app]
  rfl

private lemma localHom_comp (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W Z : C} {q : W ⟶ S} {j₁ j₂ j₃ : κ} {a₁ : W ⟶ Y j₁} {a₂ : W ⟶ Y j₂} {a₃ : W ⟶ Y j₃}
    (ha₁ : a₁ ≫ p j₁ = q) (ha₂ : a₂ ≫ p j₂ = q) (ha₃ : a₃ ≫ p j₃ = q) (r : Z ⟶ W)
    {k₁ : ι j₁} {k₂ : ι j₂} {k₃ : ι j₃}
    (b₁ : Z ⟶ X j₁ k₁) (b₂ : Z ⟶ X j₂ k₂) (b₃ : Z ⟶ X j₃ k₃)
    (hb₁ : b₁ ≫ u j₁ k₁ = r ≫ a₁) (hb₂ : b₂ ≫ u j₂ k₂ = r ≫ a₂)
    (hb₃ : b₃ ≫ u j₃ k₃ = r ≫ a₃) :
    localHom D M α ha₁ ha₂ r b₁ b₂ hb₁ hb₂ ≫ localHom D M α ha₂ ha₃ r b₂ b₃ hb₂ hb₃ =
      localHom D M α ha₁ ha₃ r b₁ b₃ hb₁ hb₃ := by
  unfold localHom localTrans
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  erw [← pullHom_comp_assoc, Iso.inv_hom_id, pullHom_id_self]
  rw [Category.id_comp, D.hom_comp_assoc]

private lemma localHom_precomp (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W Z Z' : C} {q : W ⟶ S} {j₁ j₂ : κ} {a₁ : W ⟶ Y j₁} {a₂ : W ⟶ Y j₂}
    (ha₁ : a₁ ≫ p j₁ = q) (ha₂ : a₂ ≫ p j₂ = q) (g : Z' ⟶ Z) (r : Z ⟶ W)
    {k₁ : ι j₁} {k₂ : ι j₂} (b₁ : Z ⟶ X j₁ k₁) (b₂ : Z ⟶ X j₂ k₂)
    (hb₁ : b₁ ≫ u j₁ k₁ = r ≫ a₁) (hb₂ : b₂ ≫ u j₂ k₂ = r ≫ a₂) :
    localHom D M α ha₁ ha₂ (g ≫ r) (g ≫ b₁) (g ≫ b₂)
        (by rw [Category.assoc, hb₁, Category.assoc])
        (by rw [Category.assoc, hb₂, Category.assoc]) =
      pullHom (localHom D M α ha₁ ha₂ r b₁ b₂ hb₁ hb₂) g (g ≫ r) (g ≫ r) rfl rfl := by
  symm
  dsimp only [localHom]
  rw [pullHom_comp _ _ g (g ≫ r) ((g ≫ r) ≫ a₁) (g ≫ r) rfl (Category.assoc g r a₁).symm rfl,
    pullHom_comp _ _ g ((g ≫ r) ≫ a₁) ((g ≫ r) ≫ a₂) (g ≫ r)
      (Category.assoc g r a₁).symm (Category.assoc g r a₂).symm rfl,
    pullHom_mapComp'_inv a₁ (M j₁) r (r ≫ a₁) rfl g (g ≫ r) ((g ≫ r) ≫ a₁) rfl
      (Category.assoc g r a₁).symm,
    pullHom_localTrans D M α _ _ g b₁ b₂ hb₁ hb₂ ((g ≫ r) ≫ a₁) ((g ≫ r) ≫ a₂) ((g ≫ r) ≫ q)
      (Category.assoc g r a₁).symm (Category.assoc g r a₂).symm (Category.assoc g r q).symm,
    pullHom_mapComp'_hom a₂ (M j₂) r (r ≫ a₂) rfl g (g ≫ r) ((g ≫ r) ≫ a₂) rfl
      (Category.assoc g r a₂).symm]

/-- Existence and uniqueness of the glued transition morphism `a₁^* (M j₁) ⟶ a₂^* (M j₂)` on `W`
matching `localHom` over the covering intersection sieve of `a₁^* (u j₁)` and `a₂^* (u j₂)`. -/
private lemma existsUnique_gluedHom (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j))
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W : C} (q : W ⟶ S) {j₁ j₂ : κ} (a₁ : W ⟶ Y j₁) (a₂ : W ⟶ Y j₂)
    (ha₁ : a₁ ≫ p j₁ = q) (ha₂ : a₂ ≫ p j₂ = q) :
    ∃! φ : (F.map a₁.op.toLoc).toFunctor.obj (M j₁) ⟶ (F.map a₂.op.toLoc).toFunctor.obj (M j₂),
      ∀ ⦃Z : C⦄ (r : Z ⟶ W) {k₁ : ι j₁} {k₂ : ι j₂}
        (b₁ : Z ⟶ X j₁ k₁) (b₂ : Z ⟶ X j₂ k₂)
        (hb₁ : b₁ ≫ u j₁ k₁ = r ≫ a₁) (hb₂ : b₂ ≫ u j₂ k₂ = r ≫ a₂),
        (F.map r.op.toLoc).toFunctor.map φ = localHom D M α ha₁ ha₂ r b₁ b₂ hb₁ hb₂ := by
  let R : Sieve W :=
    Sieve.pullback a₁ (Sieve.ofArrows (X j₁) (u j₁)) ⊓
      Sieve.pullback a₂ (Sieve.ofArrows (X j₂) (u j₂))
  have hR : R ∈ J W := J.intersection_covering (J.pullback_stable a₁ (hu j₁))
    (J.pullback_stable a₂ (hu j₂))
  have fac₁ {Z : C} {r : Z ⟶ W} (hr : R r) : ∃ k₁ b₁, b₁ ≫ u j₁ k₁ = r ≫ a₁ := by
    obtain ⟨_, b₁, _, ⟨k₁⟩, hb₁⟩ := hr.1
    exact ⟨k₁, b₁, hb₁⟩
  have fac₂ {Z : C} {r : Z ⟶ W} (hr : R r) : ∃ k₂ b₂, b₂ ≫ u j₂ k₂ = r ≫ a₂ := by
    obtain ⟨_, b₂, _, ⟨k₂⟩, hb₂⟩ := hr.2
    exact ⟨k₂, b₂, hb₂⟩
  obtain ⟨φ, hφ, huniq⟩ := (F.isPrestackFor' R hR).existsUnique_map_eq
    (fun Z r hr ↦ localHom D M α ha₁ ha₂ r (fac₁ hr).choose_spec.choose
      (fac₂ hr).choose_spec.choose (fac₁ hr).choose_spec.choose_spec
      (fac₂ hr).choose_spec.choose_spec)
    (fun Z' Z g r hr ↦ by
      rw [← localHom_precomp D M α ha₁ ha₂ g r (fac₁ hr).choose_spec.choose
        (fac₂ hr).choose_spec.choose (fac₁ hr).choose_spec.choose_spec
        (fac₂ hr).choose_spec.choose_spec]
      exact localHom_unique D M α ha₁ ha₂ (g ≫ r) _ _ _ _ _ _ _ _)
  refine ⟨φ, fun Z r k₁ k₂ b₁ b₂ hb₁ hb₂ ↦ ?_, fun ψ hψ ↦ huniq ψ fun Z r hr ↦
    hψ r _ _ (fac₁ hr).choose_spec.choose_spec (fac₂ hr).choose_spec.choose_spec⟩
  have hr : R r := ⟨⟨_, b₁, _, ⟨k₁⟩, hb₁⟩, ⟨_, b₂, _, ⟨k₂⟩, hb₂⟩⟩
  exact (hφ r hr).trans (localHom_unique D M α ha₁ ha₂ r _ b₁ _ b₂ _ hb₁ _ hb₂)

/-- The glued transition morphism `a₁^* (M j₁) ⟶ a₂^* (M j₂)` on `W`. -/
private noncomputable def gluedHom (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j))
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W : C} (q : W ⟶ S) {j₁ j₂ : κ} (a₁ : W ⟶ Y j₁) (a₂ : W ⟶ Y j₂)
    (ha₁ : a₁ ≫ p j₁ = q) (ha₂ : a₂ ≫ p j₂ = q) :
    (F.map a₁.op.toLoc).toFunctor.obj (M j₁) ⟶ (F.map a₂.op.toLoc).toFunctor.obj (M j₂) :=
  (existsUnique_gluedHom hu D M α q a₁ a₂ ha₁ ha₂).choose

private lemma map_gluedHom (hu : ∀ j, Sieve.ofArrows (X j) (u j) ∈ J (Y j))
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    {W Z : C} (q : W ⟶ S) {j₁ j₂ : κ} (a₁ : W ⟶ Y j₁) (a₂ : W ⟶ Y j₂)
    (ha₁ : a₁ ≫ p j₁ = q) (ha₂ : a₂ ≫ p j₂ = q) (r : Z ⟶ W)
    {k₁ : ι j₁} {k₂ : ι j₂} (b₁ : Z ⟶ X j₁ k₁) (b₂ : Z ⟶ X j₂ k₂)
    (hb₁ : b₁ ≫ u j₁ k₁ = r ≫ a₁) (hb₂ : b₂ ≫ u j₂ k₂ = r ≫ a₂) :
    (F.map r.op.toLoc).toFunctor.map (gluedHom hu D M α q a₁ a₂ ha₁ ha₂) =
      localHom D M α ha₁ ha₂ r b₁ b₂ hb₁ hb₂ :=
  (existsUnique_gluedHom hu D M α q a₁ a₂ ha₁ ha₂).choose_spec.1 r b₁ b₂ hb₁ hb₂

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
  dsimp only [pullHom]
  rw [map_gluedHom hu D M α q a₁ a₂ ha₁ ha₂ r b₁ b₂ hb₁ hb₂]
  exact mapComp'_hom_localHom_mapComp'_inv D M α ha₁ ha₂ r b₁ b₂ hb₁ hb₂ _ _ _ rfl rfl rfl

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
  refine (F.isPrestackFor' R hR).hom_ext fun Z r hr ↦ ?_
  obtain ⟨_, b₁, _, ⟨k₁⟩, hb₁⟩ := hr.1
  obtain ⟨_, b₂, _, ⟨k₂⟩, hb₂⟩ := hr.2
  rw [map_eq_pullHom _ r (r ≫ g ≫ a₁) (r ≫ g ≫ a₂) rfl rfl,
    map_eq_pullHom _ r (r ≫ g ≫ a₁) (r ≫ g ≫ a₂) rfl rfl,
    pullHom_pullHom,
    pullHom_gluedHom_eq_localTrans hu D M α q a₁ a₂ ha₁ ha₂ (r ≫ g) _ _ _
      b₁ b₂ (by rw [hb₁, Category.assoc]) (by rw [hb₂, Category.assoc])
      (Category.assoc r g a₁) (Category.assoc r g a₂) (Category.assoc r g q),
    pullHom_gluedHom_eq_localTrans hu D M α (g ≫ q) (g ≫ a₁) (g ≫ a₂) _ _ r _ _ _
      b₁ b₂ hb₁ hb₂ rfl rfl rfl]

/-- The descent datum along `p` assembled from the descended objects `M j` and transition
isomorphisms `gluedHom`. -/
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
    refine (F.isPrestackFor' _ hR).hom_ext fun Z r hr ↦ ?_
    obtain ⟨_, b, _, ⟨k⟩, hb⟩ := hr
    rw [Functor.map_id, map_gluedHom hu D M α q a a ha ha r b b hb hb,
      localHom_self D M α ha r b hb]
  hom_comp W q j₁ j₂ j₃ a₁ a₂ a₃ ha₁ ha₂ ha₃ := by
    let R : Sieve W :=
      Sieve.pullback a₁ (Sieve.ofArrows (X j₁) (u j₁)) ⊓
        (Sieve.pullback a₂ (Sieve.ofArrows (X j₂) (u j₂)) ⊓
          Sieve.pullback a₃ (Sieve.ofArrows (X j₃) (u j₃)))
    have hR : R ∈ J W := J.intersection_covering (J.pullback_stable a₁ (hu j₁))
      (J.intersection_covering (J.pullback_stable a₂ (hu j₂)) (J.pullback_stable a₃ (hu j₃)))
    refine (F.isPrestackFor' R hR).hom_ext fun Z r hr ↦ ?_
    obtain ⟨_, b₁, _, ⟨k₁⟩, hb₁⟩ := hr.1
    obtain ⟨_, b₂, _, ⟨k₂⟩, hb₂⟩ := hr.2.1
    obtain ⟨_, b₃, _, ⟨k₃⟩, hb₃⟩ := hr.2.2
    rw [Functor.map_comp,
      map_gluedHom hu D M α q a₁ a₂ ha₁ ha₂ r b₁ b₂ hb₁ hb₂,
      map_gluedHom hu D M α q a₂ a₃ ha₂ ha₃ r b₂ b₃ hb₂ hb₃,
      map_gluedHom hu D M α q a₁ a₃ ha₁ ha₃ r b₁ b₃ hb₁ hb₃,
      localHom_comp D M α ha₁ ha₂ ha₃ r b₁ b₂ b₃ hb₁ hb₂ hb₃]

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

/-- Reassociate the `descendIso` component along a single factorization `f ≫ u ≫ p = q` from
`f^* (u ≫ p)^* N ⟶ f^* (D.obj jk)` to `(f ≫ u)^* p^* N ⟶ f^* (D.obj jk)`. -/
private lemma descendIso_component_eq
    (D : F.DescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1))
    (M : ∀ j, F.obj (.mk (op (Y j))))
    (α : ∀ j, (F.toDescentData (u j)).obj (M j) ≅ restrictDatum D j)
    (N : F.obj (.mk (op S)))
    {W : C} (q : W ⟶ S) (jk : Σ j, ι j)
    (f : W ⟶ X jk.1 jk.2) (hf : f ≫ u jk.1 jk.2 ≫ p jk.1 = q)
    (φ : (F.map (p jk.1).op.toLoc).toFunctor.obj N ⟶ M jk.1) :
    (F.mapComp' (u jk.1 jk.2 ≫ p jk.1).op.toLoc f.op.toLoc q.op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, hf])).hom.toNatTrans.app N ≫
      (F.map f.op.toLoc).toFunctor.map
        ((F.mapComp' (p jk.1).op.toLoc (u jk.1 jk.2).op.toLoc
            (u jk.1 jk.2 ≫ p jk.1).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app N ≫
          (F.map (u jk.1 jk.2).op.toLoc).toFunctor.map φ ≫
          (αIso D M α jk.1 jk.2).hom) =
      (F.mapComp' (p jk.1).op.toLoc (f ≫ u jk.1 jk.2).op.toLoc q.op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, Category.assoc, hf])).hom.toNatTrans.app N ≫
        (F.map (f ≫ u jk.1 jk.2).op.toLoc).toFunctor.map φ ≫
        (F.mapComp' (u jk.1 jk.2).op.toLoc f.op.toLoc (f ≫ u jk.1 jk.2).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app (M jk.1) ≫
        (F.map f.op.toLoc).toFunctor.map (αIso D M α jk.1 jk.2).hom := by
  simp only [Functor.map_comp]
  rw [← F.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app_assoc (p jk.1).op.toLoc
      (u jk.1 jk.2).op.toLoc f.op.toLoc (u jk.1 jk.2 ≫ p jk.1).op.toLoc
      (f ≫ u jk.1 jk.2).op.toLoc q.op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, Category.assoc, hf]) N,
    ← F.mapComp'_naturality_1_assoc (u jk.1 jk.2).op.toLoc f.op.toLoc
      (f ≫ u jk.1 jk.2).op.toLoc (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]) φ,
    Cat.Hom.hom_inv_id_toNatTrans_app_assoc]

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
    (F.map f₁.op.toLoc).toFunctor.map
        ((F.mapComp' (p jk₁.1).op.toLoc (u jk₁.1 jk₁.2).op.toLoc
            (u jk₁.1 jk₁.2 ≫ p jk₁.1).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app N ≫
          (F.map (u jk₁.1 jk₁.2).op.toLoc).toFunctor.map (DescentData.isoApp β jk₁.1).hom ≫
          (αIso D M α jk₁.1 jk₁.2).hom) ≫
      D.hom q (i₁ := jk₁) (i₂ := jk₂) f₁ f₂ hf₁ hf₂ =
    ((F.toDescentData (fun jk : Σ j, ι j ↦ u jk.1 jk.2 ≫ p jk.1)).obj N).hom q f₁ f₂ hf₁ hf₂ ≫
      (F.map f₂.op.toLoc).toFunctor.map
        ((F.mapComp' (p jk₂.1).op.toLoc (u jk₂.1 jk₂.2).op.toLoc
            (u jk₂.1 jk₂.2 ≫ p jk₂.1).op.toLoc
            (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app N ≫
          (F.map (u jk₂.1 jk₂.2).op.toLoc).toFunctor.map (DescentData.isoApp β jk₂.1).hom ≫
          (αIso D M α jk₂.1 jk₂.2).hom) := by
  have ha₁ : (f₁ ≫ u jk₁.1 jk₁.2) ≫ p jk₁.1 = q := by rw [Category.assoc, hf₁]
  have ha₂ : (f₂ ≫ u jk₂.1 jk₂.2) ≫ p jk₂.1 = q := by rw [Category.assoc, hf₂]
  have hβ : (F.map (f₁ ≫ u jk₁.1 jk₁.2).op.toLoc).toFunctor.map (DescentData.isoApp β jk₁.1).hom ≫
      localTrans D M α ha₁ ha₂ f₁ f₂ rfl rfl =
      ((F.mapComp' (p jk₁.1).op.toLoc (f₁ ≫ u jk₁.1 jk₁.2).op.toLoc q.op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, ha₁])).inv.toNatTrans.app N ≫
        (F.mapComp' (p jk₂.1).op.toLoc (f₂ ≫ u jk₂.1 jk₂.2).op.toLoc q.op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, ha₂])).hom.toNatTrans.app N) ≫
      (F.map (f₂ ≫ u jk₂.1 jk₂.2).op.toLoc).toFunctor.map (DescentData.isoApp β jk₂.1).hom := by
    rw [← gluedHom_comp hu D M α q f₁ f₂ hf₁ hf₂]
    exact β.hom.comm q (f₁ ≫ u jk₁.1 jk₁.2) (f₂ ≫ u jk₂.1 jk₂.2) ha₁ ha₂
  dsimp only [toDescentData, DescentData.ofObj]
  rw [← cancel_epi ((F.mapComp' (u jk₁.1 jk₁.2 ≫ p jk₁.1).op.toLoc f₁.op.toLoc q.op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, hf₁])).hom.toNatTrans.app N)]
  simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  erw [reassoc_of% (descendIso_component_eq D M α N q jk₁ f₁ hf₁ (DescentData.isoApp β jk₁.1).hom),
    descendIso_component_eq D M α N q jk₂ f₂ hf₂ (DescentData.isoApp β jk₂.1).hom]
  have hβ₁ : (F.mapComp' (p jk₁.1).op.toLoc (f₁ ≫ u jk₁.1 jk₁.2).op.toLoc q.op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, ha₁])).hom.toNatTrans.app N ≫
      (F.map (f₁ ≫ u jk₁.1 jk₁.2).op.toLoc).toFunctor.map (DescentData.isoApp β jk₁.1).hom ≫
      (F.mapComp' (u jk₁.1 jk₁.2).op.toLoc f₁.op.toLoc (f₁ ≫ u jk₁.1 jk₁.2).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app (M jk₁.1) ≫
        (F.map f₁.op.toLoc).toFunctor.map (αIso D M α jk₁.1 jk₁.2).hom ≫
        D.hom q (i₁ := jk₁) (i₂ := jk₂) f₁ f₂ hf₁ hf₂ ≫
        (F.map f₂.op.toLoc).toFunctor.map (αIso D M α jk₂.1 jk₂.2).inv ≫
        (F.mapComp' (u jk₂.1 jk₂.2).op.toLoc f₂.op.toLoc (f₂ ≫ u jk₂.1 jk₂.2).op.toLoc
          (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app (M jk₂.1) =
      (F.mapComp' (p jk₂.1).op.toLoc (f₂ ≫ u jk₂.1 jk₂.2).op.toLoc q.op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, ha₂])).hom.toNatTrans.app N ≫
      (F.map (f₂ ≫ u jk₂.1 jk₂.2).op.toLoc).toFunctor.map (DescentData.isoApp β jk₂.1).hom := by
    have hβ₀ := congrArg (((F.mapComp' (p jk₁.1).op.toLoc (f₁ ≫ u jk₁.1 jk₁.2).op.toLoc q.op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp, ha₁])).hom.toNatTrans.app N) ≫ ·) hβ
    erw [localTrans_eq] at hβ₀
    conv_rhs at hβ₀ =>
      erw [← Category.assoc, ← Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app, Category.id_comp]
    exact hβ₀
  have hcancel₂ : ((F.mapComp' (u jk₂.1 jk₂.2).op.toLoc f₂.op.toLoc (f₂ ≫ u jk₂.1 jk₂.2).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).hom.toNatTrans.app (M jk₂.1) ≫
      (F.map f₂.op.toLoc).toFunctor.map (αIso D M α jk₂.1 jk₂.2).hom) ≫
      ((F.map f₂.op.toLoc).toFunctor.map (αIso D M α jk₂.1 jk₂.2).inv ≫
      (F.mapComp' (u jk₂.1 jk₂.2).op.toLoc f₂.op.toLoc (f₂ ≫ u jk₂.1 jk₂.2).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app (M jk₂.1)) = 𝟙 _ := by
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id, Functor.map_id,
      Category.id_comp, Cat.Hom.hom_inv_id_toNatTrans_app]
  refine (cancel_mono ((F.map f₂.op.toLoc).toFunctor.map (αIso D M α jk₂.1 jk₂.2).inv ≫
    (F.mapComp' (u jk₂.1 jk₂.2).op.toLoc f₂.op.toLoc (f₂ ≫ u jk₂.1 jk₂.2).op.toLoc
      (by simp [← Quiver.Hom.comp_toLoc, ← op_comp])).inv.toNatTrans.app (M jk₂.1))).1 ?_
  refine Eq.trans ?_ (hβ₁.trans ?_)
  · refine Eq.trans (Category.assoc _ _ _) (congrArg (_ ≫ ·) ?_)
    refine Eq.trans (Category.assoc _ _ _) (congrArg (_ ≫ ·) ?_)
    refine Eq.trans (Category.assoc _ _ _) (congrArg (_ ≫ ·) ?_)
    exact Category.assoc _ _ _
  · refine Eq.symm ?_
    refine Eq.trans (Category.assoc _ _ _) (congrArg₂ (· ≫ ·) rfl ?_)
    exact Eq.trans (Category.assoc _ _ _)
      (Eq.trans (congrArg₂ (· ≫ ·) rfl hcancel₂) (Category.comp_id _))

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
    (fun jk ↦ (Cat.Hom.toNatIso (F.mapComp' (p jk.1).op.toLoc (u jk.1 jk.2).op.toLoc
        (u jk.1 jk.2 ≫ p jk.1).op.toLoc
        (by simp [← Quiver.Hom.comp_toLoc, ← op_comp]))).app N ≪≫
      (F.map (u jk.1 jk.2).op.toLoc).toFunctor.mapIso (DescentData.isoApp β jk.1) ≪≫
      αIso D M α jk.1 jk.2)
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
