/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.LocallyDiscrete
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Precomposition as a pseudofunctor between bicategories of pseudofunctors

For a pseudofunctor `P : B ⥤ᵖ B'`, precomposition with `P` is a pseudofunctor

`Pseudofunctor.precomp C P : (B' ⥤ᵖ C) ⥤ᵖ (B ⥤ᵖ C)`

between the bicategories of pseudofunctors, strong transformations and modifications. It acts
on strong transformations by the whiskering `P.whiskerLeft`, and on modifications by restricting
their components along `P`. Its unit and composition comparisons have identity components.

For a functor `f : Γ ⥤ Λ` of categories, `precomp B f.toPseudofunctor` pulls families
`F : LocallyDiscrete Λ ⥤ᵖ B` back along `f`. A natural transformation `α : f ⟶ g` induces a
strong transformation

`precompNatTrans B α : precomp B f.toPseudofunctor ⟶ precomp B g.toPseudofunctor`

whose component at `F` is `F.mapNatTrans α`; its naturality isomorphisms express that these
pullback transformations are pseudonatural in `F`. The construction respects identities and
composites of natural transformations up to the invertible modifications `precompNatTransId` and
`precompNatTransComp`, whose components are `F.mapNatTransId` and `F.mapNatTransComp`. Hence a
natural isomorphism `α : f ≅ g` induces an adjoint equivalence `precompNatIso B α` between the
two precomposition pseudofunctors.

Applied to the unit and counit of an equivalence `e : Γ ≌ Λ` of parameter groupoids, these
equivalences relate precomposition along `e.functor ⋙ e.inverse` and `e.inverse ⋙ e.functor` to
precomposition along the identities, which is how families of categories indexed by `Λ` are
compared with families indexed by `Γ`.

## Main definitions

* `CategoryTheory.Pseudofunctor.precomp`: precomposition with a pseudofunctor;
* `CategoryTheory.Pseudofunctor.precompNatTrans`: the strong transformation between
  precompositions induced by a natural transformation;
* `CategoryTheory.Pseudofunctor.precompNatTransId`,
  `CategoryTheory.Pseudofunctor.precompNatTransComp`: its compatibility with identities and
  composites;
* `CategoryTheory.Pseudofunctor.precompNatIso`: the equivalence of precompositions induced by a
  natural isomorphism.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055): pseudofunctors, strong transformations,
  modifications, and the whiskering of strong transformations by pseudofunctors.
* Edward Frenkel,
  [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  Cambridge Studies in Advanced Mathematics 103 (2007): families of local categories over the
  groupoid of local Langlands parameters, and their descent to local systems.
-/

public section

namespace CategoryTheory.Pseudofunctor

open Bicategory StrongTrans

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

section

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {B' : Type u₂} [Bicategory.{w₂, v₂} B']
  (C : Type u₃) [Bicategory.{w₃, v₃} C]

/-- Precomposition with a pseudofunctor `P : B ⥤ᵖ B'`, as a pseudofunctor between the bicategories
of pseudofunctors into `C`. It sends `F` to `P.comp F`, a strong transformation `η` to the
whiskering `P.whiskerLeft η`, and a modification to its restriction along `P`; its unit and
composition comparisons `P.whiskerLeftId` and `P.whiskerLeftComp` have identity components. -/
-- The body is exposed and reducible so that `(precomp C P).obj F` is `P.comp F` up to reducible
-- unfolding: the components of strong transformations and modifications between precompositions
-- are then morphisms between the composites, which `simp` can rewrite.
@[expose, reducible, simps obj map map₂_as_app mapId mapComp]
def precomp (P : B ⥤ᵖ B') : (B' ⥤ᵖ C) ⥤ᵖ (B ⥤ᵖ C) where
  obj F := P.comp F
  map η := P.whiskerLeft η
  map₂ Γ := ⟨{ app a := Γ.as.app (P.obj a), naturality f := Γ.as.naturality (P.map f) }⟩
  map₂_id η := by ext; rfl
  map₂_comp Γ Δ := by ext; rfl
  mapId F := P.whiskerLeftId F
  mapComp η θ := P.whiskerLeftComp η θ
  -- The structure cells `mapId` and `mapComp` have identity components, but their sources and
  -- targets agree with those of the other side only up to unfolding `whiskerLeft`, so each
  -- component equation is stated with the unfolded types and closed by `simp`.
  map₂_whisker_left η θ θ' Γ := by
    ext a
    simp only [whiskerLeft_as_app, homCategory_comp_as_app, comp_app, whiskerLeftComp_hom_as_app,
      whiskerLeftComp_inv_as_app]
    exact (show η.app (P.obj a) ◁ Γ.as.app (P.obj a) = 𝟙 (η.app (P.obj a) ≫ θ.app (P.obj a)) ≫
      η.app (P.obj a) ◁ Γ.as.app (P.obj a) ≫ 𝟙 (η.app (P.obj a) ≫ θ'.app (P.obj a)) by simp)
  map₂_whisker_right {F G H η θ} Γ ι := by
    ext a
    simp only [whiskerRight_as_app, homCategory_comp_as_app, comp_app, whiskerLeftComp_hom_as_app,
      whiskerLeftComp_inv_as_app]
    exact (show Γ.as.app (P.obj a) ▷ ι.app (P.obj a) = 𝟙 (η.app (P.obj a) ≫ ι.app (P.obj a)) ≫
      Γ.as.app (P.obj a) ▷ ι.app (P.obj a) ≫ 𝟙 (θ.app (P.obj a) ≫ ι.app (P.obj a)) by simp)
  map₂_associator η θ ι := by
    ext a
    simp only [associator_hom_as_app, homCategory_comp_as_app, comp_app,
      whiskerLeftComp_hom_as_app, whiskerRight_as_app, whiskerLeft_as_app,
      whiskerLeftComp_inv_as_app]
    exact (show (α_ (η.app (P.obj a)) (θ.app (P.obj a)) (ι.app (P.obj a))).hom =
      𝟙 _ ≫ 𝟙 (η.app (P.obj a) ≫ θ.app (P.obj a)) ▷ ι.app (P.obj a) ≫
        (α_ (η.app (P.obj a)) (θ.app (P.obj a)) (ι.app (P.obj a))).hom ≫
          η.app (P.obj a) ◁ 𝟙 (θ.app (P.obj a) ≫ ι.app (P.obj a)) ≫ 𝟙 _ by simp)
  map₂_left_unitor η := by
    ext a
    simp only [leftUnitor_hom_as_app, homCategory_comp_as_app, comp_app,
      whiskerLeftComp_hom_as_app, whiskerRight_as_app, whiskerLeftId_hom_as_app]
    exact (show (λ_ (η.app (P.obj a))).hom =
      𝟙 _ ≫ 𝟙 (𝟙 _) ▷ η.app (P.obj a) ≫ (λ_ (η.app (P.obj a))).hom by simp)
  map₂_right_unitor η := by
    ext a
    simp only [rightUnitor_hom_as_app, homCategory_comp_as_app, comp_app,
      whiskerLeftComp_hom_as_app, whiskerLeft_as_app, whiskerLeftId_hom_as_app]
    exact (show (ρ_ (η.app (P.obj a))).hom =
      𝟙 _ ≫ η.app (P.obj a) ◁ 𝟙 (𝟙 _) ≫ (ρ_ (η.app (P.obj a))).hom by simp)

end

section LocallyDiscrete

variable {Γ : Type u₁} [Category.{v₁} Γ] {Λ : Type u₂} [Category.{v₂} Λ]
  (B : Type u₃) [Bicategory.{w₃, v₃} B]

/-- The strong transformation `precomp B f ⟶ precomp B g` induced by a natural transformation
`α : f ⟶ g`. Its component at `F` is the strong transformation
`F.mapNatTrans α : f.toPseudofunctor.comp F ⟶ g.toPseudofunctor.comp F`, and its naturality
isomorphism at `η : F ⟶ G` is the invertible modification whose component at `x` is the inverse
of the naturality isomorphism `F (α x) ≫ η (g x) ≅ η (f x) ≫ G (α x)` of `η` at `α x`. So the
pullback strong transformations `F.mapNatTrans α` are pseudonatural in `F`. -/
-- The body is exposed so that the components of the naturality isomorphisms can be stated in
-- terms of those of `η`, as in `precompNatTrans_naturality_hom_as_app`.
@[expose] def precompNatTrans {f g : Γ ⥤ Λ} (α : f ⟶ g) :
    precomp B f.toPseudofunctor ⟶ precomp B g.toPseudofunctor where
  app F := F.mapNatTrans α
  naturality {F G} η := (isoMk (η := F.mapNatTrans α ≫ g.toPseudofunctor.whiskerLeft η)
    (θ := f.toPseudofunctor.whiskerLeft η ≫ G.mapNatTrans α)
    (fun x => η.naturality (α.app x.as).toLoc) (fun {x y} φ => by
    simp only [comp_app, categoryStruct_comp_naturality_hom, whiskerLeft_naturality,
      mapNatTrans_naturality]
    exact η.naturality_isoMapOfCommSq (CommSq.mk (α.naturality φ.as)).toLoc)).symm
  naturality_naturality {F G η θ} Θ := by
    ext x
    have key : Θ.as.app ⟨f.obj x.as⟩ ▷ G.map (α.app x.as).toLoc ≫
        (θ.naturality (α.app x.as).toLoc).inv =
          (η.naturality (α.app x.as).toLoc).inv ≫
            F.map (α.app x.as).toLoc ◁ Θ.as.app ⟨g.obj x.as⟩ := by
      rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
      exact (Θ.as.naturality _).symm
    simp only [Iso.symm_hom, homCategory_comp_as_app, whiskerLeft_as_app, whiskerRight_as_app]
    exact key
  naturality_id F := by
    ext x
    -- The component of the naturality isomorphism of `𝟙 F` is `ρ_ _ ≪≫ (λ_ _).symm`.
    have key : ((λ_ (F.map (α.app x.as).toLoc)).hom ≫ (ρ_ (F.map (α.app x.as).toLoc)).inv) ≫
        F.map (α.app x.as).toLoc ◁ 𝟙 (𝟙 (F.obj ⟨g.obj x.as⟩)) =
          𝟙 (𝟙 (F.obj ⟨f.obj x.as⟩)) ▷ F.map (α.app x.as).toLoc ≫ (λ_ _).hom ≫ (ρ_ _).inv := by
      simp
    simp only [Iso.symm_hom, homCategory_comp_as_app, whiskerLeft_as_app,
      whiskerRight_as_app, whiskerLeftId_hom_as_app, leftUnitor_hom_as_app,
      rightUnitor_inv_as_app]
    exact key
  naturality_comp {F G H} η θ := by
    ext x
    -- The inverse of the naturality isomorphism of `η ≫ θ`, unfolded with the association of
    -- `Iso.trans`.
    have key : (((((α_ (η.app ⟨f.obj x.as⟩) (θ.app ⟨f.obj x.as⟩) (H.map (α.app x.as).toLoc)).hom ≫
        η.app ⟨f.obj x.as⟩ ◁ (θ.naturality (α.app x.as).toLoc).inv) ≫
          (α_ (η.app ⟨f.obj x.as⟩) (G.map (α.app x.as).toLoc) (θ.app ⟨g.obj x.as⟩)).inv) ≫
            (η.naturality (α.app x.as).toLoc).inv ▷ θ.app ⟨g.obj x.as⟩) ≫
              (α_ (F.map (α.app x.as).toLoc) (η.app ⟨g.obj x.as⟩) (θ.app ⟨g.obj x.as⟩)).hom) ≫
        F.map (α.app x.as).toLoc ◁ 𝟙 (η.app ⟨g.obj x.as⟩ ≫ θ.app ⟨g.obj x.as⟩) =
          𝟙 (η.app ⟨f.obj x.as⟩ ≫ θ.app ⟨f.obj x.as⟩) ▷ H.map (α.app x.as).toLoc ≫
            (α_ _ _ _).hom ≫ η.app ⟨f.obj x.as⟩ ◁ (θ.naturality (α.app x.as).toLoc).inv ≫
              (α_ _ _ _).inv ≫ (η.naturality (α.app x.as).toLoc).inv ▷ θ.app ⟨g.obj x.as⟩ ≫
                (α_ _ _ _).hom := by
      simp
    simp only [Iso.symm_hom, homCategory_comp_as_app, whiskerLeft_as_app,
      whiskerRight_as_app, whiskerLeftComp_hom_as_app, associator_hom_as_app,
      associator_inv_as_app]
    exact key

@[simp]
lemma precompNatTrans_app {f g : Γ ⥤ Λ} (α : f ⟶ g) (F : LocallyDiscrete Λ ⥤ᵖ B) :
    (precompNatTrans B α).app F = F.mapNatTrans α :=
  (rfl)

@[simp]
lemma precompNatTrans_naturality_hom_as_app {f g : Γ ⥤ Λ} (α : f ⟶ g)
    {F G : LocallyDiscrete Λ ⥤ᵖ B} (η : F ⟶ G) (x : LocallyDiscrete Γ) :
    ((precompNatTrans B α).naturality η).hom.as.app x = (η.naturality (α.app x.as).toLoc).inv :=
  (rfl)

@[simp]
lemma precompNatTrans_naturality_inv_as_app {f g : Γ ⥤ Λ} (α : f ⟶ g)
    {F G : LocallyDiscrete Λ ⥤ᵖ B} (η : F ⟶ G) (x : LocallyDiscrete Γ) :
    ((precompNatTrans B α).naturality η).inv.as.app x = (η.naturality (α.app x.as).toLoc).hom :=
  (rfl)

/-- The strong transformation induced by the identity natural transformation of `f` is
isomorphic to the identity strong transformation of `precomp B f.toPseudofunctor`, by the
invertible modification with components `F.mapNatTransId f`. -/
def precompNatTransId (f : Γ ⥤ Λ) :
    precompNatTrans B (𝟙 f) ≅ 𝟙 (precomp B f.toPseudofunctor) :=
  isoMk (fun F => F.mapNatTransId f) (fun {F G} η => by
    ext x
    have key : η.app ⟨f.obj x.as⟩ ◁ (G.mapId' ((𝟙 f : f ⟶ f).app x.as).toLoc (by simp)).hom ≫
        (ρ_ (η.app ⟨f.obj x.as⟩)).hom ≫ (λ_ (η.app ⟨f.obj x.as⟩)).inv =
          (η.naturality ((𝟙 f : f ⟶ f).app x.as).toLoc).inv ≫
            (F.mapId' ((𝟙 f : f ⟶ f).app x.as).toLoc (by simp)).hom ▷ η.app ⟨f.obj x.as⟩ := by
      rw [η.naturality_id'_inv _ (by simp)]
      simp
    simp only [homCategory_comp_as_app, whiskerLeft_as_app, whiskerRight_as_app,
      precompNatTrans_naturality_hom_as_app, mapNatTransId_hom_as_app]
    exact key)

@[simp]
lemma precompNatTransId_hom_as_app (f : Γ ⥤ Λ) (F : LocallyDiscrete Λ ⥤ᵖ B) :
    (precompNatTransId B f).hom.as.app F = (F.mapNatTransId f).hom :=
  (rfl)

@[simp]
lemma precompNatTransId_inv_as_app (f : Γ ⥤ Λ) (F : LocallyDiscrete Λ ⥤ᵖ B) :
    (precompNatTransId B f).inv.as.app F = (F.mapNatTransId f).inv :=
  (rfl)

/-- The strong transformation induced by a composite `α ≫ β` of natural transformations is
isomorphic to the composite of the strong transformations induced by `α` and `β`, by the
invertible modification with components `F.mapNatTransComp α β`. -/
def precompNatTransComp {f g h : Γ ⥤ Λ} (α : f ⟶ g) (β : g ⟶ h) :
    precompNatTrans B (α ≫ β) ≅ precompNatTrans B α ≫ precompNatTrans B β :=
  isoMk (fun F => F.mapNatTransComp α β) (fun {F G} η => by
    ext x
    have key : η.app ⟨f.obj x.as⟩ ◁ (G.mapComp' (α.app x.as).toLoc (β.app x.as).toLoc
          ((α ≫ β).app x.as).toLoc (by simp [← Quiver.Hom.comp_toLoc])).hom ≫
        (α_ _ _ _).inv ≫ (η.naturality (α.app x.as).toLoc).inv ▷ G.map (β.app x.as).toLoc ≫
          (α_ _ _ _).hom ≫ F.map (α.app x.as).toLoc ◁ (η.naturality (β.app x.as).toLoc).inv ≫
            (α_ _ _ _).inv =
        (η.naturality ((α ≫ β).app x.as).toLoc).inv ≫
          (F.mapComp' (α.app x.as).toLoc (β.app x.as).toLoc ((α ≫ β).app x.as).toLoc
            (by simp [← Quiver.Hom.comp_toLoc])).hom ▷ η.app ⟨h.obj x.as⟩ := by
      rw [η.naturality_comp'_inv (α.app x.as).toLoc (β.app x.as).toLoc ((α ≫ β).app x.as).toLoc
        (by simp [← Quiver.Hom.comp_toLoc])]
      simp
    simp only [homCategory_comp_as_app, whiskerLeft_as_app, whiskerRight_as_app,
      precompNatTrans_naturality_hom_as_app, mapNatTransComp_hom_as_app]
    exact key)

@[simp]
lemma precompNatTransComp_hom_as_app {f g h : Γ ⥤ Λ} (α : f ⟶ g) (β : g ⟶ h)
    (F : LocallyDiscrete Λ ⥤ᵖ B) :
    (precompNatTransComp B α β).hom.as.app F = (F.mapNatTransComp α β).hom :=
  (rfl)

@[simp]
lemma precompNatTransComp_inv_as_app {f g h : Γ ⥤ Λ} (α : f ⟶ g) (β : g ⟶ h)
    (F : LocallyDiscrete Λ ⥤ᵖ B) :
    (precompNatTransComp B α β).inv.as.app F = (F.mapNatTransComp α β).inv :=
  (rfl)

/-- A natural isomorphism `α : f ≅ g` induces an adjoint equivalence between the precomposition
pseudofunctors `precomp B f.toPseudofunctor` and `precomp B g.toPseudofunctor`, with
`1`-morphisms the strong transformations induced by `α.hom` and `α.inv`. -/
def precompNatIso {f g : Γ ⥤ Λ} (α : f ≅ g) :
    Bicategory.Equivalence (precomp B f.toPseudofunctor) (precomp B g.toPseudofunctor) :=
  Equivalence.mkOfAdjointifyCounit
    ((precompNatTransId B f).symm ≪≫
      eqToIso (congrArg (precompNatTrans B) α.hom_inv_id.symm) ≪≫
        precompNatTransComp B α.hom α.inv)
    ((precompNatTransComp B α.inv α.hom).symm ≪≫
      eqToIso (congrArg (precompNatTrans B) α.inv_hom_id) ≪≫ precompNatTransId B g)

@[simp]
lemma precompNatIso_hom {f g : Γ ⥤ Λ} (α : f ≅ g) :
    (precompNatIso B α).hom = precompNatTrans B α.hom := by
  rw [precompNatIso, Equivalence.mkOfAdjointifyCounit]

@[simp]
lemma precompNatIso_inv {f g : Γ ⥤ Λ} (α : f ≅ g) :
    (precompNatIso B α).inv = precompNatTrans B α.inv := by
  rw [precompNatIso, Equivalence.mkOfAdjointifyCounit]

end LocallyDiscrete

end CategoryTheory.Pseudofunctor
