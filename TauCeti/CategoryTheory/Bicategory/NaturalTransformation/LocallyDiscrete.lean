/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import TauCeti.CategoryTheory.Bicategory.Strict.Pseudofunctor

/-!
# Pulling back pseudofunctors along naturally isomorphic functors

Let `F : LocallyDiscrete Λ ⥤ᵖ B` be a pseudofunctor, for instance a family of categories indexed
by a groupoid `Λ`. A functor `f : Γ ⥤ Λ` pulls `F` back to `f.toPseudofunctor.comp F`. This file
shows that the pullback depends on `f` in a two-functorial way: a natural transformation
`α : f ⟶ g` induces a strong transformation

`F.mapNatTrans α : f.toPseudofunctor.comp F ⟶ g.toPseudofunctor.comp F`

with components `F (α x)`, whose naturality isomorphism at `φ : x ⟶ y` is the isomorphism
`F (f φ) ≫ F (α y) ≅ F (α x) ≫ F (g φ)` of the naturality square of `α`. The construction sends
identities and composites of natural transformations to the identity and composites of strong
transformations, up to the invertible modifications `F.mapNatTransId` and `F.mapNatTransComp`
given by the unit and composition comparisons of `F`. Consequently a natural isomorphism
`α : f ≅ g` induces an adjoint equivalence `F.mapNatIso α` between the two pullbacks in the
bicategory of pseudofunctors.

This is the input needed to invert the pullback along an equivalence of parameter groupoids
`e : Γ ≌ Λ`: the unit and counit isomorphisms of `e` give equivalences between the pullbacks
along `𝟭 Γ` and `e.functor ⋙ e.inverse`, and along `e.inverse ⋙ e.functor` and `𝟭 Λ`, as in the
descent of families of local categories from the groupoid of opers to the groupoid of local
systems.

## Main definitions

* `CategoryTheory.Pseudofunctor.mapNatTrans`: the strong transformation induced by a natural
  transformation of functors into the indexing category;
* `CategoryTheory.Pseudofunctor.mapNatTransId`, `CategoryTheory.Pseudofunctor.mapNatTransComp`:
  its compatibility with identities and composites;
* `CategoryTheory.Pseudofunctor.mapNatIso`: the equivalence of pullbacks induced by a natural
  isomorphism.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055), for pseudofunctors, strong
  transformations and modifications.
* Edward Frenkel,
  [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  Cambridge Studies in Advanced Mathematics 103 (2007): the families of local categories over
  the groupoid of local Langlands parameters, and their descent to local systems.
-/

public section

universe w₃ v₃ u₃ v₂ u₂ v₁ u₁

namespace CategoryTheory.Pseudofunctor

open Bicategory StrongTrans

variable {Γ : Type u₁} [Category.{v₁} Γ] {Λ : Type u₂} [Category.{v₂} Λ]
  {B : Type u₃} [Bicategory.{w₃, v₃} B] (F : LocallyDiscrete Λ ⥤ᵖ B)

/-- The strong transformation `f.toPseudofunctor.comp F ⟶ g.toPseudofunctor.comp F` induced by a
natural transformation `α : f ⟶ g`. Its component at `x` is `F (α x)`, and its naturality
isomorphism at `φ : x ⟶ y` is the isomorphism `F (f φ) ≫ F (α y) ≅ F (α x) ≫ F (g φ)` of the
naturality square of `α`. -/
-- The body is exposed so that the naturality isomorphisms can be stated in terms of the
-- components, as in `mapNatTrans_naturality`.
@[expose] def mapNatTrans {f g : Γ ⥤ Λ} (α : f ⟶ g) :
    f.toPseudofunctor.comp F ⟶ g.toPseudofunctor.comp F where
  app x := F.map (α.app x.as).toLoc
  naturality φ := F.isoMapOfCommSq (CommSq.mk (α.naturality φ.as)).toLoc
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    rw [Subsingleton.elim η (𝟙 _), PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]
    -- The objects in the goal are values of `Functor.toPseudofunctor`, which the `simp` lemmas
    -- about whiskering do not match at reducible transparency. The statement is proved for
    -- arbitrary objects and then unified with the goal.
    have key {X Y Y' Z : B} (u : X ⟶ Y) (v : Y ⟶ Z) (u' : X ⟶ Y') (v' : Y' ⟶ Z)
        (θ : u ≫ v ≅ u' ≫ v') : 𝟙 u ▷ v ≫ θ.hom = θ.hom ≫ u' ◁ 𝟙 v' := by
      simp
    exact key _ _ _ _ _
  naturality_id x := by
    rw [comp_mapId_eq_mapId', comp_mapId_eq_mapId']
    exact F.isoMapOfCommSq_hom_whiskerLeft_mapId' _ _ _
  naturality_comp φ ψ := by
    rw [comp_mapComp_eq_mapComp', comp_mapComp_eq_mapComp']
    exact F.isoMapOfCommSq_hom_whiskerLeft_mapComp' _ _ _ _ _

@[simp]
lemma mapNatTrans_app {f g : Γ ⥤ Λ} (α : f ⟶ g) (x : LocallyDiscrete Γ) :
    (F.mapNatTrans α).app x = F.map (α.app x.as).toLoc :=
  (rfl)

@[simp]
lemma mapNatTrans_naturality {f g : Γ ⥤ Λ} (α : f ⟶ g) {x y : LocallyDiscrete Γ} (φ : x ⟶ y) :
    (F.mapNatTrans α).naturality φ = F.isoMapOfCommSq (CommSq.mk (α.naturality φ.as)).toLoc :=
  (rfl)

/-- The strong transformation induced by the identity natural transformation of `f` is
isomorphic to the identity strong transformation, by the unit comparisons of `F`. -/
def mapNatTransId (f : Γ ⥤ Λ) : F.mapNatTrans (𝟙 f) ≅ 𝟙 (f.toPseudofunctor.comp F) :=
  isoMk (fun x ↦ F.mapId' ((𝟙 f : f ⟶ f).app x.as).toLoc (by simp))
    (fun φ ↦ (F.isoMapOfCommSq_hom_whiskerRight_mapId'
      (CommSq.mk ((𝟙 f : f ⟶ f).naturality φ.as)).toLoc _ _).symm)

@[simp]
lemma mapNatTransId_hom_as_app (f : Γ ⥤ Λ) (x : LocallyDiscrete Γ) :
    (F.mapNatTransId f).hom.as.app x =
      (F.mapId' ((𝟙 f : f ⟶ f).app x.as).toLoc (by simp)).hom :=
  (rfl)

@[simp]
lemma mapNatTransId_inv_as_app (f : Γ ⥤ Λ) (x : LocallyDiscrete Γ) :
    (F.mapNatTransId f).inv.as.app x =
      (F.mapId' ((𝟙 f : f ⟶ f).app x.as).toLoc (by simp)).inv :=
  (rfl)

/-- The strong transformation induced by a composite `α ≫ β` of natural transformations is
isomorphic to the composite of the strong transformations induced by `α` and `β`, by the
composition comparisons of `F`. -/
def mapNatTransComp {f g h : Γ ⥤ Λ} (α : f ⟶ g) (β : g ⟶ h) :
    F.mapNatTrans (α ≫ β) ≅ F.mapNatTrans α ≫ F.mapNatTrans β :=
  isoMk (fun x ↦ F.mapComp' (α.app x.as).toLoc (β.app x.as).toLoc ((α ≫ β).app x.as).toLoc
      (by simp [← Quiver.Hom.comp_toLoc]))
    (fun φ ↦ (F.isoMapOfCommSq_hom_whiskerRight_mapComp' (CommSq.mk (α.naturality φ.as)).toLoc
      (CommSq.mk (β.naturality φ.as)).toLoc (CommSq.mk ((α ≫ β).naturality φ.as)).toLoc
      _ _).symm)

@[simp]
lemma mapNatTransComp_hom_as_app {f g h : Γ ⥤ Λ} (α : f ⟶ g) (β : g ⟶ h)
    (x : LocallyDiscrete Γ) :
    (F.mapNatTransComp α β).hom.as.app x =
      (F.mapComp' (α.app x.as).toLoc (β.app x.as).toLoc ((α ≫ β).app x.as).toLoc
        (by simp [← Quiver.Hom.comp_toLoc])).hom :=
  (rfl)

@[simp]
lemma mapNatTransComp_inv_as_app {f g h : Γ ⥤ Λ} (α : f ⟶ g) (β : g ⟶ h)
    (x : LocallyDiscrete Γ) :
    (F.mapNatTransComp α β).inv.as.app x =
      (F.mapComp' (α.app x.as).toLoc (β.app x.as).toLoc ((α ≫ β).app x.as).toLoc
        (by simp [← Quiver.Hom.comp_toLoc])).inv :=
  (rfl)

/-- A natural isomorphism `α : f ≅ g` induces an adjoint equivalence between the pullbacks
`f.toPseudofunctor.comp F` and `g.toPseudofunctor.comp F` in the bicategory of pseudofunctors,
with `1`-morphisms the strong transformations induced by `α.hom` and `α.inv`. -/
def mapNatIso {f g : Γ ⥤ Λ} (α : f ≅ g) :
    Bicategory.Equivalence (f.toPseudofunctor.comp F) (g.toPseudofunctor.comp F) :=
  Equivalence.mkOfAdjointifyCounit
    ((F.mapNatTransId f).symm ≪≫ eqToIso (congrArg F.mapNatTrans α.hom_inv_id.symm) ≪≫
      F.mapNatTransComp α.hom α.inv)
    ((F.mapNatTransComp α.inv α.hom).symm ≪≫ eqToIso (congrArg F.mapNatTrans α.inv_hom_id) ≪≫
      F.mapNatTransId g)

@[simp]
lemma mapNatIso_hom {f g : Γ ⥤ Λ} (α : f ≅ g) : (F.mapNatIso α).hom = F.mapNatTrans α.hom := by
  rw [mapNatIso, Equivalence.mkOfAdjointifyCounit]

@[simp]
lemma mapNatIso_inv {f g : Γ ⥤ Λ} (α : f ≅ g) : (F.mapNatIso α).inv = F.mapNatTrans α.inv := by
  rw [mapNatIso, Equivalence.mkOfAdjointifyCounit]

end CategoryTheory.Pseudofunctor
