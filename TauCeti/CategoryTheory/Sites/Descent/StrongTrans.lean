/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Cat
public import TauCeti.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Descent data along a strong transformation

Let `η : F ⟶ G` be a strong transformation between pseudofunctors
`LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`. A morphism `φ : f₁^* M₁ ⟶ f₂^* M₂` between pullbacks of objects of
`F` has an image `f₁^* (η M₁) ⟶ f₂^* (η M₂)`, the image `η φ` conjugated by the naturality
isomorphisms of `η` (`Pseudofunctor.StrongTrans.mapPullHom`). It is compatible with composition,
identities and Mathlib's pullback `LocallyDiscreteOpToCat.pullHom` of such morphisms
(`Pseudofunctor.StrongTrans.mapPullHom_pullHom`). So `η` sends descent data for `F` along a family
of morphisms `f i : X i ⟶ S` to descent data for `G` (`Pseudofunctor.StrongTrans.mapDescentData`),
compatibly with the functors from the fibres over `S` up to the naturality isomorphisms of `η`
(`Pseudofunctor.StrongTrans.toDescentDataCompMapDescentDataIso`). This is compatible with
identities and composites of strong transformations (`StrongTrans.mapDescentDataId`,
`StrongTrans.mapDescentDataComp`), and a modification `Γ : φ ⟶ φ'` induces a natural
transformation `φ.mapDescentData f ⟶ φ'.mapDescentData f` (`StrongTrans.mapDescentData₂`). These
are the fibrewise part of the functoriality of the stackification of prestacks in strong
transformations.

When the components of `η` are fully faithful, so is `η.mapDescentData f`, and a descent datum for
`G` whose objects are isomorphic to images under `η` lifts to a descent datum for `F`
(`Pseudofunctor.StrongTrans.liftDescentData`). Its gluing isomorphisms are the unique lifts of the
*target overlaps* `η (F(a) (M i)) ≅ η (F(b) (M j))`: the gluing isomorphisms of `D` conjugated by
the isomorphisms `η (M i) ≅ D.obj i` and the naturality isomorphisms of `η`
(`Pseudofunctor.StrongTrans.targetOverlapIso`,
`Pseudofunctor.StrongTrans.mapIso_liftDescentData_iso`), which satisfy the identity and cocycle
laws (`Pseudofunctor.StrongTrans.targetOverlapIso_self`,
`Pseudofunctor.StrongTrans.targetOverlapIso_trans`). Hence if `F` has effective descent and `G`
descent of morphisms along a family, an object of `G` whose pullbacks along the family are in the
essential image of `η` is itself in it (`Pseudofunctor.StrongTrans.mem_essImage_of_toDescentData`).
When the components of `η` are equivalences of categories, `η.mapDescentData f` is an equivalence.
Comparing the descent functors of `F` and `G` through it shows that the descent of morphisms and
effective descent along a presieve transfer along `η`, so that `F` is a prestack, respectively a
stack, if and only if `G` is (`Pseudofunctor.isPrestack_iff_of_isEquivalence`,
`Pseudofunctor.isStack_iff_of_isEquivalence`). The descent of morphisms already transfers from
`G` to `F` when the components of `η` are only fully faithful
(`Pseudofunctor.isPrestack_source_of_fullyFaithful`).

The descent data, prestacks and stacks are Mathlib's `Pseudofunctor.DescentData`,
`Pseudofunctor.IsPrestack` and `Pseudofunctor.IsStack`, by Joël Riou and Christian Merten.

## Main declarations

* `CategoryTheory.Pseudofunctor.StrongTrans.mapDescentData`: the functor on descent data induced
  by a strong transformation.
* `CategoryTheory.Pseudofunctor.StrongTrans.isEquivalence_mapDescentData`: it is an equivalence
  when the components are.
* `CategoryTheory.Pseudofunctor.StrongTrans.mem_essImage_of_toDescentData`: descent of the
  essential image along a transformation with fully faithful components.
* `CategoryTheory.Pseudofunctor.isPrestack_iff_of_isEquivalence`,
  `CategoryTheory.Pseudofunctor.isStack_iff_of_isEquivalence`: being a prestack, respectively a
  stack, is invariant under strong transformations whose components are equivalences.

## References

* [Stacks Project, Section 06NY](https://stacks.math.columbia.edu/tag/06NY), Lemma 8.11.2
-/

public section

universe t v' v u' u

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.StrongTrans

open LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (η : StrongTrans F G)

/-- The image under a strong transformation `η : F ⟶ G` of a morphism `φ : f₁^* M₁ ⟶ f₂^* M₂`
between pullbacks, as a morphism `f₁^* (η M₁) ⟶ f₂^* (η M₂)`: the image `η φ` conjugated by
the naturality isomorphisms of `η` at `f₁` and `f₂`. -/
def mapPullHom ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄ ⦃Y : C⦄
    ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) :
    (G.map f₁.op.toLoc).toFunctor.obj ((η.app (.mk (op X₁))).toFunctor.obj M₁) ⟶
      (G.map f₂.op.toLoc).toFunctor.obj ((η.app (.mk (op X₂))).toFunctor.obj M₂) :=
  (η.naturality f₁.op.toLoc).inv.toNatTrans.app M₁ ≫ (η.app (.mk (op Y))).toFunctor.map φ ≫
    (η.naturality f₂.op.toLoc).hom.toNatTrans.app M₂

/-- The definition of `StrongTrans.mapPullHom`. -/
lemma mapPullHom_def ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄ ⦃Y : C⦄
    ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) :
    η.mapPullHom φ = (η.naturality f₁.op.toLoc).inv.toNatTrans.app M₁ ≫
      (η.app (.mk (op Y))).toFunctor.map φ ≫ (η.naturality f₂.op.toLoc).hom.toNatTrans.app M₂ :=
  (rfl)

/-- The image of an identity is an identity. -/
@[simp]
lemma mapPullHom_id ⦃X : C⦄ ⦃M : F.obj (.mk (op X))⦄ ⦃Y : C⦄ (f : Y ⟶ X) :
    η.mapPullHom (𝟙 ((F.map f.op.toLoc).toFunctor.obj M)) = 𝟙 _ := by
  simp [mapPullHom]

/-- The image of a composite is the composite of the images. -/
@[simp, reassoc]
lemma mapPullHom_comp ⦃X₁ X₂ X₃ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃M₃ : F.obj (.mk (op X₃))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄ ⦃f₃ : Y ⟶ X₃⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (ψ : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃) :
    η.mapPullHom (φ ≫ ψ) = η.mapPullHom φ ≫ η.mapPullHom ψ := by
  simp [mapPullHom]

/-- The image of the pullback `f^* φ` of a morphism `φ` is the pullback `f^* (η φ)`. -/
@[simp]
lemma mapPullHom_map ⦃X : C⦄ ⦃M N : F.obj (.mk (op X))⦄ (φ : M ⟶ N) ⦃Y : C⦄ (f : Y ⟶ X) :
    η.mapPullHom ((F.map f.op.toLoc).toFunctor.map φ) =
      (G.map f.op.toLoc).toFunctor.map ((η.app (.mk (op X))).toFunctor.map φ) := by
  simp only [mapPullHom]
  exact η.naturality_naturality_1 f.op.toLoc φ

/-- Taking images under `η` commutes with pulling back morphisms between pullbacks. -/
@[simp]
lemma mapPullHom_pullHom ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    η.mapPullHom (pullHom φ g gf₁ gf₂ hgf₁ hgf₂) =
      pullHom (η.mapPullHom φ) g gf₁ gf₂ hgf₁ hgf₂ := by
  subst hgf₁ hgf₂
  simp only [mapPullHom, pullHom, CategoryTheory.Functor.map_comp, Category.assoc,
    η.naturality_comp'_inv_app f₁.op.toLoc g.op.toLoc (g ≫ f₁).op.toLoc rfl,
    η.naturality_comp'_hom_app f₂.op.toLoc g.op.toLoc (g ≫ f₂).op.toLoc rfl]
  rw [← CategoryTheory.Functor.map_comp_assoc _
      ((F.mapComp' f₁.op.toLoc g.op.toLoc (g ≫ f₁).op.toLoc rfl).inv.toNatTrans.app M₁),
    Cat.Hom.inv_hom_id_toNatTrans_app, CategoryTheory.Functor.map_id, Category.id_comp,
    ← CategoryTheory.Functor.map_comp_assoc _
      ((F.mapComp' f₂.op.toLoc g.op.toLoc (g ≫ f₂).op.toLoc rfl).inv.toNatTrans.app M₂),
    Cat.Hom.inv_hom_id_toNatTrans_app]
  -- The identity lives over `(F.map f₂ ≫ F.map g).toFunctor.obj M₂`, which is only
  -- definitionally the source of `(η.naturality g).hom.toNatTrans.app`.
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [η.naturality_naturality_1_assoc]

/-- The image of a composition comparison `(f ≫ g)^* M ⟶ g^* (f^* M)` of `F` is the composition
comparison of `G` followed by the inverse naturality isomorphism of `η` at `f`. -/
lemma mapPullHom_mapComp'_hom ⦃X Y Z : C⦄ (f : Y ⟶ X) (g : Z ⟶ Y) (fg : Z ⟶ X)
    (h : g ≫ f = fg) (M : F.obj (.mk (op X))) :
    η.mapPullHom (f₂ := g) (M₂ := (F.map f.op.toLoc).toFunctor.obj M)
        ((F.mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).hom.toNatTrans.app M) =
      (G.mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).hom.toNatTrans.app
          ((η.app _).toFunctor.obj M) ≫
        (G.map g.op.toLoc).toFunctor.map ((η.naturality f.op.toLoc).inv.toNatTrans.app M) := by
  rw [mapPullHom_def, naturality_comp'_inv_app η f.op.toLoc g.op.toLoc fg.op.toLoc
    (by rw [← h]; rfl)]
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp_assoc,
    Cat.Hom.inv_hom_id_toNatTrans_app]
  -- The identity left by cancelling the comparisons of `F` lives over
  -- `(F.map f ≫ F.map g).toFunctor.obj M`, which is only definitionally the source of the
  -- naturality isomorphism of `η` at `g`.
  erw [CategoryTheory.Functor.map_id]
  simp

/-- The image of an inverse composition comparison `g^* (f^* M) ⟶ (f ≫ g)^* M` of `F` is the
naturality isomorphism of `η` at `f` followed by the inverse composition comparison of `G`. -/
lemma mapPullHom_mapComp'_inv ⦃X Y Z : C⦄ (f : Y ⟶ X) (g : Z ⟶ Y) (fg : Z ⟶ X)
    (h : g ≫ f = fg) (M : F.obj (.mk (op X))) :
    η.mapPullHom (f₁ := g) (M₁ := (F.map f.op.toLoc).toFunctor.obj M)
        ((F.mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).inv.toNatTrans.app M) =
      (G.map g.op.toLoc).toFunctor.map ((η.naturality f.op.toLoc).hom.toNatTrans.app M) ≫
        (G.mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).inv.toNatTrans.app
          ((η.app _).toFunctor.obj M) := by
  rw [mapPullHom_def, naturality_comp'_hom_app η f.op.toLoc g.op.toLoc fg.op.toLoc
    (by rw [← h]; rfl)]
  simp only [← CategoryTheory.Functor.map_comp_assoc, Cat.Hom.inv_hom_id_toNatTrans_app]
  -- As in `mapPullHom_mapComp'_hom`, the identity is over a composite in `Cat`.
  erw [CategoryTheory.Functor.map_id]
  simp

/-- `StrongTrans.mapPullHom` for the identity strong transformation is the identity. -/
@[simp]
lemma id_mapPullHom ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (a : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) :
    (𝟙 F : F ⟶ F).mapPullHom a = a := by
  simp only [mapPullHom_def, categoryStruct_id_naturality_inv, categoryStruct_id_naturality_hom]
  -- The unitors of `Cat` have identity components, and `(𝟙 F).app` is the identity functor.
  erw [Cat.Hom₂.comp_app, Cat.Hom₂.comp_app]
  simp only [Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app, Cat.rightUnitor_hom_app,
    Cat.leftUnitor_inv_app, eqToHom_refl]
  -- The identities are over objects that agree with those of `a` only up to unfolding the
  -- composites with identities in `Cat`, so they are cancelled by unification.
  have cancel {D : Type u'} [Category.{v'} D] {X Y : D} (x : X ⟶ Y) :
      (𝟙 X ≫ 𝟙 X) ≫ x ≫ 𝟙 Y ≫ 𝟙 Y = x := by
    simp
  exact cancel a

/-- `StrongTrans.mapPullHom` for a composite of strong transformations is the composite of the
`StrongTrans.mapPullHom`. -/
@[simp]
lemma comp_mapPullHom {H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} (φ : F ⟶ G) (ψ : G ⟶ H)
    ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄
    ⦃f₂ : Y ⟶ X₂⦄
    (a : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) :
    (φ ≫ ψ).mapPullHom a = ψ.mapPullHom (φ.mapPullHom a) := by
  simp only [mapPullHom_def, comp_naturality_inv_app, comp_naturality_hom_app,
    CategoryTheory.Functor.map_comp, Category.assoc]
  -- The component of `φ ≫ ψ` over `Y` is the composite of those of `φ` and `ψ`, by definition.
  exact Category.assoc _ _ _

/-- `StrongTrans.mapPullHom` is natural with respect to modifications. -/
@[reassoc]
lemma map_app_comp_mapPullHom {φ φ' : F ⟶ G} (Γ : φ ⟶ φ') ⦃X₁ X₂ : C⦄
    ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄
    ⦃f₂ : Y ⟶ X₂⦄
    (a : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) :
    (G.map f₁.op.toLoc).toFunctor.map ((Γ.as.app _).toNatTrans.app M₁) ≫ φ'.mapPullHom a =
      φ.mapPullHom a ≫ (G.map f₂.op.toLoc).toFunctor.map ((Γ.as.app _).toNatTrans.app M₂) := by
  have h₁ := congrArg (fun m ↦ m.toNatTrans.app M₁) (Γ.as.naturality f₁.op.toLoc)
  have h₂ := congrArg (fun m ↦ m.toNatTrans.app M₂) (Γ.as.naturality f₂.op.toLoc)
  simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app] at h₁ h₂
  rw [mapPullHom_def, mapPullHom_def,
    ← cancel_epi ((φ.naturality f₁.op.toLoc).hom.toNatTrans.app M₁), ← reassoc_of% h₁]
  simp only [Cat.Hom.hom_inv_id_toNatTrans_app_assoc, Category.assoc, ← h₂]
  exact ((Γ.as.app _).toNatTrans.naturality_assoc a _).symm

/-- For a fully faithful component `η.app Y`, `StrongTrans.mapPullHom` is a bijection between the
morphisms `f₁^* M₁ ⟶ f₂^* M₂` and `f₁^* (η M₁) ⟶ f₂^* (η M₂)`. -/
noncomputable def mapPullHomEquiv ⦃X₁ X₂ : C⦄ (M₁ : F.obj (.mk (op X₁))) (M₂ : F.obj (.mk (op X₂)))
    ⦃Y : C⦄ (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (h : (η.app (.mk (op Y))).toFunctor.FullyFaithful) :
    ((F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) ≃
      ((G.map f₁.op.toLoc).toFunctor.obj ((η.app (.mk (op X₁))).toFunctor.obj M₁) ⟶
        (G.map f₂.op.toLoc).toFunctor.obj ((η.app (.mk (op X₂))).toFunctor.obj M₂)) :=
  h.homEquiv.trans ((η.naturalityObjIso f₁.op.toLoc M₁).homCongr
    (η.naturalityObjIso f₂.op.toLoc M₂))

/-- The bijection `StrongTrans.mapPullHomEquiv` is `StrongTrans.mapPullHom`. -/
@[simp]
lemma mapPullHomEquiv_apply ⦃X₁ X₂ : C⦄ (M₁ : F.obj (.mk (op X₁))) (M₂ : F.obj (.mk (op X₂)))
    ⦃Y : C⦄ (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (h : (η.app (.mk (op Y))).toFunctor.FullyFaithful)
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) :
    η.mapPullHomEquiv M₁ M₂ f₁ f₂ h φ = η.mapPullHom φ := by
  simp [mapPullHomEquiv, mapPullHom, Iso.homCongr_apply]

/-- `StrongTrans.mapPullHom` is a left inverse of the inverse of `StrongTrans.mapPullHomEquiv`. -/
@[simp]
lemma mapPullHom_mapPullHomEquiv_symm ⦃X₁ X₂ : C⦄ (M₁ : F.obj (.mk (op X₁)))
    (M₂ : F.obj (.mk (op X₂))) ⦃Y : C⦄ (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (h : (η.app (.mk (op Y))).toFunctor.FullyFaithful)
    (ψ : (G.map f₁.op.toLoc).toFunctor.obj ((η.app (.mk (op X₁))).toFunctor.obj M₁) ⟶
      (G.map f₂.op.toLoc).toFunctor.obj ((η.app (.mk (op X₂))).toFunctor.obj M₂)) :
    η.mapPullHom ((η.mapPullHomEquiv M₁ M₂ f₁ f₂ h).symm ψ) = ψ := by
  rw [← mapPullHomEquiv_apply _ _ _ _ _ h, Equiv.apply_symm_apply]

variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- The functor from descent data for `F` to descent data for `G` induced by a strong
transformation `η : F ⟶ G`. The image of a descent datum has the images under `η` of its objects,
and the images of its compatibility morphisms given by `StrongTrans.mapPullHom`. -/
-- This is an abbreviation so that the objects of a mapped descent datum are reducibly the images of
-- the objects under `η`: rewriting in local morphisms between them fails otherwise.
@[simps]
abbrev mapDescentData : F.DescentData f ⥤ G.DescentData f where
  obj D :=
    { obj i := (η.app (.mk (op (X i)))).toFunctor.obj (D.obj i)
      hom _ q _ _ f₁ f₂ hf₁ hf₂ := η.mapPullHom (D.hom q f₁ f₂ hf₁ hf₂)
      pullHom_hom _ _ g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
        rw [← mapPullHom_pullHom, D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
      hom_self _ q _ g hg := by rw [D.hom_self q g hg, mapPullHom_id]
      hom_comp _ q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by rw [← mapPullHom_comp, D.hom_comp] }
  map {D₁ D₂} φ :=
    { hom i := (η.app (.mk (op (X i)))).toFunctor.map (φ.hom i)
      comm _ q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
        calc _ = η.mapPullHom ((F.map f₁.op.toLoc).toFunctor.map (φ.hom i₁) ≫
              D₂.hom q f₁ f₂ hf₁ hf₂) := by rw [mapPullHom_comp, mapPullHom_map]
          _ = η.mapPullHom (D₁.hom q f₁ f₂ hf₁ hf₂ ≫
              (F.map f₂.op.toLoc).toFunctor.map (φ.hom i₂)) := by rw [φ.comm q f₁ f₂ hf₁ hf₂]
          _ = _ := by rw [mapPullHom_comp, mapPullHom_map] }
  map_id _ := by ext; exact (η.app _).toFunctor.map_id _
  map_comp _ _ := by ext; exact (η.app _).toFunctor.map_comp _ _

/-- The naturality isomorphisms of `η` commute with the comparison isomorphisms
`f₁^* (p₁^* M) ≅ f₂^* (p₂^* M)` of `F` and of `G` for `f₁ ≫ p₁ = f₂ ≫ p₂`. These are the
compatibility morphisms of the descent data given by `M` and by `η M`. -/
lemma map_naturality_comp_mapComp'_inv_comp_mapComp'_hom ⦃X₁ X₂ : C⦄ (p₁ : X₁ ⟶ S)
    (p₂ : X₂ ⟶ S) (M : F.obj (.mk (op S))) ⦃Y : C⦄ (q : Y ⟶ S) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    (h₁ : p₁.op.toLoc ≫ f₁.op.toLoc = q.op.toLoc) (h₂ : p₂.op.toLoc ≫ f₂.op.toLoc = q.op.toLoc) :
    (G.map f₁.op.toLoc).toFunctor.map ((η.naturality p₁.op.toLoc).hom.toNatTrans.app M) ≫
        (G.mapComp' p₁.op.toLoc f₁.op.toLoc q.op.toLoc h₁).inv.toNatTrans.app _ ≫
          (G.mapComp' p₂.op.toLoc f₂.op.toLoc q.op.toLoc h₂).hom.toNatTrans.app _ =
      η.mapPullHom ((F.mapComp' p₁.op.toLoc f₁.op.toLoc q.op.toLoc h₁).inv.toNatTrans.app M ≫
          (F.mapComp' p₂.op.toLoc f₂.op.toLoc q.op.toLoc h₂).hom.toNatTrans.app M) ≫
        (G.map f₂.op.toLoc).toFunctor.map ((η.naturality p₂.op.toLoc).hom.toNatTrans.app M) := by
  -- Both sides are computed by the composition condition of `η` at `q = pₖ ≫ fₖ`.
  have key₁ : (G.map f₁.op.toLoc).toFunctor.map
        ((η.naturality p₁.op.toLoc).hom.toNatTrans.app M) ≫
      (G.mapComp' p₁.op.toLoc f₁.op.toLoc q.op.toLoc h₁).inv.toNatTrans.app _ =
      (η.naturality f₁.op.toLoc).inv.toNatTrans.app ((F.map p₁.op.toLoc).toFunctor.obj M) ≫
        (η.app (.mk (op Y))).toFunctor.map
          ((F.mapComp' p₁.op.toLoc f₁.op.toLoc q.op.toLoc h₁).inv.toNatTrans.app M) ≫
        (η.naturality q.op.toLoc).hom.toNatTrans.app M := by
    rw [η.naturality_comp'_hom_app p₁.op.toLoc f₁.op.toLoc q.op.toLoc h₁,
      ← CategoryTheory.Functor.map_comp_assoc, Cat.Hom.inv_hom_id_toNatTrans_app]
    -- The identity lives over `(F.map p₁ ≫ F.map f₁).toFunctor.obj M`, which is only
    -- definitionally the source of `(η.naturality f₁).hom.toNatTrans.app`.
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    simp
  have key₂ : (η.app (.mk (op Y))).toFunctor.map
        ((F.mapComp' p₂.op.toLoc f₂.op.toLoc q.op.toLoc h₂).hom.toNatTrans.app M) ≫
      (η.naturality f₂.op.toLoc).hom.toNatTrans.app ((F.map p₂.op.toLoc).toFunctor.obj M) ≫
        (G.map f₂.op.toLoc).toFunctor.map ((η.naturality p₂.op.toLoc).hom.toNatTrans.app M) =
      (η.naturality q.op.toLoc).hom.toNatTrans.app M ≫
        (G.mapComp' p₂.op.toLoc f₂.op.toLoc q.op.toLoc h₂).hom.toNatTrans.app _ := by
    rw [η.naturality_comp'_hom_app p₂.op.toLoc f₂.op.toLoc q.op.toLoc h₂]
    simp
  rw [reassoc_of% key₁, ← key₂]
  simp [mapPullHom]

/-- The descent functors of `F` and `G` commute with `η` up to the naturality isomorphisms of
`η`. -/
@[expose, simps!]
def toDescentDataCompMapDescentDataIso :
    F.toDescentData f ⋙ η.mapDescentData f ≅
      (η.app (.mk (op S))).toFunctor ⋙ G.toDescentData f :=
  NatIso.ofComponents
    (fun M ↦ DescentData.isoMk (fun i ↦ (Cat.Hom.toNatIso (η.naturality (f i).op.toLoc)).app M)
      (fun _ q _ _ f₁ f₂ hf₁ hf₂ ↦ η.map_naturality_comp_mapComp'_inv_comp_mapComp'_hom _ _ M q
        f₁ f₂ (by rw [← hf₁]; rfl) (by rw [← hf₂]; rfl)))
    (fun φ ↦ by
      ext i
      exact (η.naturality (f i).op.toLoc).hom.toNatTrans.naturality φ)

/-- Composing an equation of morphisms `K₁.obj P ⟶ K₂.obj Q` with images of identities on both
sides. It is applied by unification to cancel identities over objects that agree with `P` and `Q`
only up to unfolding. -/
private lemma map_id_comp_eq_comp_map_id {D₁ D₂ D' : Type*} [Category D₁] [Category D₂]
    [Category D'] (K₁ : D₁ ⥤ D') (K₂ : D₂ ⥤ D') {P : D₁} {Q : D₂} {x y : K₁.obj P ⟶ K₂.obj Q}
    (h : x = y) : K₁.map (𝟙 P) ≫ x = y ≫ K₂.map (𝟙 Q) := by
  simp [h]

variable (F) in
/-- Descent data mapped along the identity strong transformation are isomorphic to the original
ones, through identities. -/
def mapDescentDataId : (𝟙 F : F ⟶ F).mapDescentData f ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun D ↦ DescentData.isoMk (fun i ↦ Iso.refl _) (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
      -- The objects of the mapped descent datum are those of `D` only up to unfolding the
      -- identity strong transformation, so the identities are cancelled by unification.
      exact map_id_comp_eq_comp_map_id (F.map f₁.op.toLoc).toFunctor
        (F.map f₂.op.toLoc).toFunctor (id_mapPullHom (D.hom q f₁ f₂ hf₁ hf₂)).symm))
    (fun ψ ↦ by
      ext i
      -- As above, the components of the identity strong transformation are identities.
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

variable (F) in
@[simp]
lemma mapDescentDataId_hom_app_hom (D : F.DescentData f) (i : ι) :
    ((mapDescentDataId F f).hom.app D).hom i = 𝟙 (D.obj i) :=
  (rfl)

variable (F) in
@[simp]
lemma mapDescentDataId_inv_app_hom (D : F.DescentData f) (i : ι) :
    ((mapDescentDataId F f).inv.app D).hom i = 𝟙 (D.obj i) :=
  (rfl)

/-- Descent data mapped along a composite of strong transformations are isomorphic to the
descent data mapped along the two strong transformations, through identities. -/
def mapDescentDataComp {H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} (ψ : G ⟶ H) :
    (η ≫ ψ).mapDescentData f ≅ η.mapDescentData f ⋙ ψ.mapDescentData f :=
  NatIso.ofComponents
    (fun D ↦ DescentData.isoMk
      (fun i ↦ Iso.refl _) (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
        -- As in `mapDescentDataId`, the identities are cancelled by unification.
        exact map_id_comp_eq_comp_map_id (H.map f₁.op.toLoc).toFunctor
          (H.map f₂.op.toLoc).toFunctor (comp_mapPullHom η ψ (D.hom q f₁ f₂ hf₁ hf₂)).symm))
    (fun χ ↦ by
      ext i
      -- The components of `η ≫ ψ` are the composites of those of `η` and `ψ`, by definition.
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

@[simp]
lemma mapDescentDataComp_hom_app_hom {H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} (ψ : G ⟶ H)
    (D : F.DescentData f) (i : ι) :
    ((η.mapDescentDataComp f ψ).hom.app D).hom i =
      𝟙 ((ψ.app _).toFunctor.obj ((η.app _).toFunctor.obj (D.obj i))) :=
  (rfl)

@[simp]
lemma mapDescentDataComp_inv_app_hom {H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} (ψ : G ⟶ H)
    (D : F.DescentData f) (i : ι) :
    ((η.mapDescentDataComp f ψ).inv.app D).hom i =
      𝟙 ((ψ.app _).toFunctor.obj ((η.app _).toFunctor.obj (D.obj i))) :=
  (rfl)

/-- The natural transformation between mapped descent data given by a modification `Γ : φ ⟶ φ'`:
its components are those of `Γ`. -/
def mapDescentData₂ {φ φ' : F ⟶ G} (Γ : φ ⟶ φ') : φ.mapDescentData f ⟶ φ'.mapDescentData f where
  app D :=
    { hom i := (Γ.as.app _).toNatTrans.app (D.obj i)
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := map_app_comp_mapPullHom Γ _ }
  naturality D₁ D₂ ψ := by
    ext i
    exact (Γ.as.app _).toNatTrans.naturality (ψ.hom i)

@[simp]
lemma mapDescentData₂_app_hom {φ φ' : F ⟶ G} (Γ : φ ⟶ φ') (D : F.DescentData f) (i : ι) :
    ((mapDescentData₂ f Γ).app D).hom i = (Γ.as.app _).toNatTrans.app (D.obj i) :=
  (rfl)

/-- If the components of `η` are fully faithful, then so is the functor `η.mapDescentData f`. -/
noncomputable def fullyFaithfulMapDescentData
    (hη : ∀ U : C, (η.app (.mk (op U))).toFunctor.FullyFaithful) :
    (η.mapDescentData f).FullyFaithful where
  preimage {D₁ D₂} ψ :=
    { hom i := (hη (X i)).preimage (ψ.hom i)
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := (η.mapPullHomEquiv _ _ f₁ f₂ (hη Y)).injective (by
        simp only [mapPullHomEquiv_apply, mapPullHom_comp, mapPullHom_map]
        -- `ψ.hom i` is typed by the objects of `(η.mapDescentData f).obj D`, which are only
        -- definitionally the images under `η`.
        erw [(hη _).map_preimage, (hη _).map_preimage]
        exact ψ.comm q f₁ f₂ hf₁ hf₂) }
  map_preimage ψ := by ext i; exact (hη _).map_preimage _
  preimage_map φ := by ext i; exact (hη _).preimage_map _

section lift

variable (hη : ∀ U : C, (η.app (.mk (op U))).toFunctor.FullyFaithful) (D : G.DescentData f)
  {M : ∀ i, F.obj (.mk (op (X i)))}
  (e : ∀ i, (η.app (.mk (op (X i)))).toFunctor.obj (M i) ≅ D.obj i)

/-- The compatibility morphisms of a descent datum `D` for `G`, transported along isomorphisms
`e i : η (M i) ≅ D.obj i`. -/
def liftDescentDataHom ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (G.map f₁.op.toLoc).toFunctor.obj ((η.app (.mk (op (X i₁)))).toFunctor.obj (M i₁)) ⟶
      (G.map f₂.op.toLoc).toFunctor.obj ((η.app (.mk (op (X i₂)))).toFunctor.obj (M i₂)) :=
  (G.map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫ D.hom q f₁ f₂ hf₁ hf₂ ≫
    (G.map f₂.op.toLoc).toFunctor.map (e i₂).inv

/-- The transported compatibility morphisms, composed with `e`, are those of `D`. -/
@[reassoc]
lemma liftDescentDataHom_comp ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    η.liftDescentDataHom f D e q f₁ f₂ hf₁ hf₂ ≫ (G.map f₂.op.toLoc).toFunctor.map (e i₂).hom =
      (G.map f₁.op.toLoc).toFunctor.map (e i₁).hom ≫ D.hom q f₁ f₂ hf₁ hf₂ := by
  simp [liftDescentDataHom]

/-- For a strong transformation `η : F ⟶ G` with fully faithful components, the descent datum for
`F` with objects `M i` lifting a descent datum `D` for `G` along isomorphisms
`e i : η (M i) ≅ D.obj i`. Its body is exposed so that its objects are the `M i` by definition,
which the statements of `StrongTrans.liftDescentData_hom` and of the components of
`StrongTrans.mapDescentDataLiftDescentDataIso` need. -/
@[expose]
noncomputable def liftDescentData : F.DescentData f where
  obj := M
  hom Y q _ _ f₁ f₂ hf₁ hf₂ :=
    (η.mapPullHomEquiv _ _ f₁ f₂ (hη Y)).symm (η.liftDescentDataHom f D e q f₁ f₂ hf₁ hf₂)
  pullHom_hom Y' _ g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ :=
    (η.mapPullHomEquiv _ _ gf₁ gf₂ (hη Y')).injective (by
      simp only [mapPullHomEquiv_apply, mapPullHom_pullHom, mapPullHom_mapPullHomEquiv_symm,
        liftDescentDataHom]
      rw [pullHom_comp _ _ g gf₁ gf₁ gf₂ hgf₁ hgf₁ hgf₂,
        pullHom_comp _ _ g gf₁ gf₂ gf₂ hgf₁ hgf₂ hgf₂,
        pullHom_map, pullHom_map, D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂])
  hom_self Y q i g hg := (η.mapPullHomEquiv _ _ g g (hη Y)).injective (by
    simp [liftDescentDataHom, D.hom_self q g hg])
  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := (η.mapPullHomEquiv _ _ f₁ f₃ (hη Y)).injective (by
    simp [liftDescentDataHom])

/-- The objects of the lift of `D` are the `M i`. -/
@[simp]
lemma liftDescentData_obj (i : ι) : (η.liftDescentData f hη D e).obj i = M i :=
  (rfl)

/-- The compatibility morphisms of the lift of `D` are the preimages under
`StrongTrans.mapPullHom` of the transported compatibility morphisms of `D`. Their images under
`StrongTrans.mapPullHom` are rewritten by the simp lemma
`StrongTrans.mapPullHom_liftDescentData_hom`. -/
lemma liftDescentData_hom ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (η.liftDescentData f hη D e).hom q f₁ f₂ hf₁ hf₂ =
      (η.mapPullHomEquiv _ _ f₁ f₂ (hη Y)).symm (η.liftDescentDataHom f D e q f₁ f₂ hf₁ hf₂) :=
  (rfl)

/-- The images under `StrongTrans.mapPullHom` of the compatibility morphisms of the lift of `D`
are the transported compatibility morphisms of `D`. -/
@[simp]
lemma mapPullHom_liftDescentData_hom ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁)
    (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    η.mapPullHom ((η.liftDescentData f hη D e).hom q f₁ f₂ hf₁ hf₂) =
      η.liftDescentDataHom f D e q f₁ f₂ hf₁ hf₂ :=
  mapPullHom_mapPullHomEquiv_symm η _ _ f₁ f₂ (hη Y) _

/-- The image under `η.mapDescentData f` of the lift of a descent datum `D` along isomorphisms
`e i : η (M i) ≅ D.obj i` is isomorphic to `D`. -/
noncomputable def mapDescentDataLiftDescentDataIso :
    (η.mapDescentData f).obj (η.liftDescentData f hη D e) ≅ D :=
  DescentData.isoMk e (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
    rw [mapDescentData_obj_hom, mapPullHom_liftDescentData_hom]
    exact (η.liftDescentDataHom_comp f D e q f₁ f₂ hf₁ hf₂).symm)

/-- The components of `StrongTrans.mapDescentDataLiftDescentDataIso` are the isomorphisms `e`. -/
@[simp]
lemma mapDescentDataLiftDescentDataIso_hom_hom (i : ι) :
    (η.mapDescentDataLiftDescentDataIso f hη D e).hom.hom i = (e i).hom :=
  (rfl)

/-- The components of the inverse of `StrongTrans.mapDescentDataLiftDescentDataIso` are the
inverses of the isomorphisms `e`. -/
@[simp]
lemma mapDescentDataLiftDescentDataIso_inv_hom (i : ι) :
    (η.mapDescentDataLiftDescentDataIso f hη D e).inv.hom i = (e i).inv :=
  (rfl)

/-- The **target overlap** of isomorphisms `e i : η (M i) ≅ D.obj i` on a common refinement
`q = a ≫ f i = b ≫ f j`: the isomorphism `η_Y (F(a) (M i)) ≅ η_Y (F(b) (M j))` through
`c_a(M i)`, `G(a)(e i)`, the gluing isomorphism `G(a) (D.obj i) ≅ G(b) (D.obj j)` of `D`
(`DescentData.iso`), `G(b)(e j)⁻¹` and `c_b(M j)⁻¹`. -/
noncomputable def targetOverlapIso ⦃Y : C⦄ (q : Y ⟶ S) ⦃i j : ι⦄ (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (η.app (.mk (op Y))).toFunctor.obj ((F.map a.op.toLoc).toFunctor.obj (M i)) ≅
      (η.app (.mk (op Y))).toFunctor.obj ((F.map b.op.toLoc).toFunctor.obj (M j)) :=
  η.naturalityObjIso a.op.toLoc (M i) ≪≫ (G.map a.op.toLoc).toFunctor.mapIso (e i) ≪≫
    D.iso q a b ha hb ≪≫
      ((G.map b.op.toLoc).toFunctor.mapIso (e j)).symm ≪≫ (η.naturalityObjIso b.op.toLoc (M j)).symm

/-- The forward arrow of the target overlap, as the composite of its five factors. -/
lemma targetOverlapIso_hom ⦃Y : C⦄ (q : Y ⟶ S) ⦃i j : ι⦄ (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (η.targetOverlapIso f D e q a b ha hb).hom =
      (η.naturalityObjIso a.op.toLoc (M i)).hom ≫ (G.map a.op.toLoc).toFunctor.map (e i).hom ≫
        D.hom q a b ha hb ≫
          (G.map b.op.toLoc).toFunctor.map (e j).inv ≫ (η.naturalityObjIso b.op.toLoc (M j)).inv :=
  (rfl)

/-- On the diagonal, the target overlap is the identity. -/
@[simp]
lemma targetOverlapIso_self ⦃Y : C⦄ (q : Y ⟶ S) ⦃i : ι⦄ (a : Y ⟶ X i) (ha : a ≫ f i = q) :
    η.targetOverlapIso f D e q a a ha ha = Iso.refl _ := by
  ext
  simp [targetOverlapIso_hom, D.hom_self q a ha]

/-- **The cocycle condition** for the forward arrows of target overlaps on a common
refinement. -/
@[reassoc (attr := simp)]
lemma targetOverlapIso_hom_comp_hom ⦃Y : C⦄ (q : Y ⟶ S) ⦃i j k : ι⦄ (a : Y ⟶ X i)
    (b : Y ⟶ X j) (c : Y ⟶ X k) (ha : a ≫ f i = q) (hb : b ≫ f j = q) (hc : c ≫ f k = q) :
    (η.targetOverlapIso f D e q a b ha hb).hom ≫ (η.targetOverlapIso f D e q b c hb hc).hom =
      (η.targetOverlapIso f D e q a c ha hc).hom := by
  simp [targetOverlapIso_hom]

/-- **The cocycle condition** for target overlaps on a common refinement. -/
@[simp]
lemma targetOverlapIso_trans ⦃Y : C⦄ (q : Y ⟶ S) ⦃i j k : ι⦄ (a : Y ⟶ X i) (b : Y ⟶ X j)
    (c : Y ⟶ X k) (ha : a ≫ f i = q) (hb : b ≫ f j = q) (hc : c ≫ f k = q) :
    η.targetOverlapIso f D e q a b ha hb ≪≫ η.targetOverlapIso f D e q b c hb hc =
      η.targetOverlapIso f D e q a c ha hc :=
  Iso.ext (η.targetOverlapIso_hom_comp_hom f D e q a b c ha hb hc)

/-- The inverse arrow of the target overlap is the forward arrow of the target overlap with the
two maps interchanged. -/
@[simp]
lemma targetOverlapIso_inv ⦃Y : C⦄ (q : Y ⟶ S) ⦃i j : ι⦄ (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (η.targetOverlapIso f D e q a b ha hb).inv = (η.targetOverlapIso f D e q b a hb ha).hom :=
  Iso.inv_ext (by simp)

/-- Interchanging the two maps inverts the target overlap. -/
@[simp]
lemma targetOverlapIso_symm ⦃Y : C⦄ (q : Y ⟶ S) ⦃i j : ι⦄ (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (η.targetOverlapIso f D e q a b ha hb).symm = η.targetOverlapIso f D e q b a hb ha :=
  Iso.ext (η.targetOverlapIso_inv f D e q a b ha hb)

/-- The image under `η_Y` of the gluing morphism of the lift of `D` along `e` is the forward
arrow of the target overlap. The objects of the lift are the `M i` only by definition, so the
statement names the domain `F(a) (M i)` and codomain `F(b) (M j)` of the arrow. -/
@[simp, reassoc]
lemma map_liftDescentData_hom ⦃Y : C⦄ (q : Y ⟶ S) ⦃i j : ι⦄ (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (η.app (.mk (op Y))).toFunctor.map (X := (F.map a.op.toLoc).toFunctor.obj (M i))
        (Y := (F.map b.op.toLoc).toFunctor.obj (M j))
        ((η.liftDescentData f hη D e).hom q a b ha hb) =
      (η.targetOverlapIso f D e q a b ha hb).hom := by
  -- `mapPullHom_liftDescentData_hom`, with the naturality isomorphisms at the `M i` rather than
  -- at the objects of the lift, which are only definitionally equal to them.
  have h : (η.naturality a.op.toLoc).inv.toNatTrans.app (M i) ≫
      (η.app (.mk (op Y))).toFunctor.map (X := (F.map a.op.toLoc).toFunctor.obj (M i))
        (Y := (F.map b.op.toLoc).toFunctor.obj (M j))
        ((η.liftDescentData f hη D e).hom q a b ha hb) ≫
        (η.naturality b.op.toLoc).hom.toNatTrans.app (M j) =
      η.liftDescentDataHom f D e q a b ha hb :=
    (η.mapPullHom_def _).symm.trans (η.mapPullHom_liftDescentData_hom f hη D e q a b ha hb)
  rw [targetOverlapIso_hom, ← η.liftDescentDataHom_comp_assoc f D e q a b ha hb, ← h]
  simp

/-- The image under `η_Y` of the gluing isomorphism of the lift of `D` along `e` is the target
overlap. -/
@[simp]
lemma mapIso_liftDescentData_iso ⦃Y : C⦄ (q : Y ⟶ S) ⦃i j : ι⦄ (a : Y ⟶ X i) (b : Y ⟶ X j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (η.app (.mk (op Y))).toFunctor.mapIso (X := (F.map a.op.toLoc).toFunctor.obj (M i))
        (Y := (F.map b.op.toLoc).toFunctor.obj (M j))
        ((η.liftDescentData f hη D e).iso q a b ha hb) =
      η.targetOverlapIso f D e q a b ha hb :=
  Iso.ext (η.map_liftDescentData_hom f hη D e q a b ha hb)

end lift

/-- If the components of `η` are fully faithful and those over the `X i` are essentially
surjective, then the functor `η.mapDescentData f` is essentially surjective. -/
lemma essSurj_mapDescentData (hη : ∀ U : C, (η.app (.mk (op U))).toFunctor.FullyFaithful)
    [∀ i, (η.app (.mk (op (X i)))).toFunctor.EssSurj] : (η.mapDescentData f).EssSurj where
  mem_essImage D := ⟨_, ⟨η.mapDescentDataLiftDescentDataIso f hη D
    (fun i ↦ (η.app (.mk (op (X i)))).toFunctor.objObjPreimageIso (D.obj i))⟩⟩

/-- If the components of `η` are equivalences, then so is the functor `η.mapDescentData f`. -/
lemma isEquivalence_mapDescentData
    (hη : ∀ U : C, (η.app (.mk (op U))).toFunctor.IsEquivalence) :
    (η.mapDescentData f).IsEquivalence :=
  have hff (U : C) :=
    have := hη U; Functor.FullyFaithful.ofFullyFaithful (η.app (.mk (op U))).toFunctor
  have := fun i ↦ hη (X i)
  have := essSurj_mapDescentData η f hff
  have := (η.fullyFaithfulMapDescentData f hff).full
  have := (η.fullyFaithfulMapDescentData f hff).faithful
  { }

/-- **Descent of the essential image.** Let the components of `η : F ⟶ G` be fully faithful, and
let `F` have effective descent and `G` descent of morphisms along a family `f i : X i ⟶ S`. If the
pullback of `z` along every `f i` is in the essential image of `η`, then so is `z`: the lift of the
descent datum of `z` descends to an object of `F` over `S`, whose image has the descent datum of
`z`. -/
lemma mem_essImage_of_toDescentData
    (hη : ∀ U : C, (η.app (.mk (op U))).toFunctor.FullyFaithful)
    [(F.toDescentData f).EssSurj] (hG : (G.toDescentData f).FullyFaithful)
    (z : G.obj (.mk (op S)))
    (hz : ∀ i, (η.app (.mk (op (X i)))).toFunctor.essImage
      ((G.map (f i).op.toLoc).toFunctor.obj z)) :
    (η.app (.mk (op S))).toFunctor.essImage z := by
  choose M e using hz
  let D := η.liftDescentData f hη ((G.toDescentData f).obj z) (fun i ↦ (e i).some)
  exact ⟨(F.toDescentData f).objPreimage D, ⟨hG.preimageIso
    ((η.toDescentDataCompMapDescentDataIso f).symm.app _ ≪≫
      (η.mapDescentData f).mapIso ((F.toDescentData f).objObjPreimageIso D) ≪≫
      η.mapDescentDataLiftDescentDataIso f hη _ _)⟩⟩

end CategoryTheory.Pseudofunctor.StrongTrans

namespace CategoryTheory.Pseudofunctor

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  (η : StrongTrans F G) {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- If the components of `η : F ⟶ G` are fully faithful and the descent functor of `G` along a
family `f` is fully faithful, then so is that of `F`. -/
noncomputable def StrongTrans.fullyFaithfulToDescentData
    (hη : ∀ U : C, (η.app (.mk (op U))).toFunctor.FullyFaithful)
    (hG : (G.toDescentData f).FullyFaithful) : (F.toDescentData f).FullyFaithful :=
  have := (η.fullyFaithfulMapDescentData f hη).faithful
  .ofCompFaithful (G := η.mapDescentData f)
    (((hη S).comp hG).ofIso (η.toDescentDataCompMapDescentDataIso f).symm)

section

variable (hη : ∀ U : C, (η.app (.mk (op U))).toFunctor.IsEquivalence)
include hη

/-- For a strong transformation `η : F ⟶ G` whose components are equivalences, the descent
functor of `F` along a family `f` is fully faithful if and only if that of `G` is. -/
lemma nonempty_fullyFaithful_toDescentData_iff_of_isEquivalence :
    Nonempty (F.toDescentData f).FullyFaithful ↔ Nonempty (G.toDescentData f).FullyFaithful := by
  have hff (U : C) :=
    have := hη U; Functor.FullyFaithful.ofFullyFaithful (η.app (.mk (op U))).toFunctor
  refine ⟨fun ⟨hF⟩ ↦ ⟨?_⟩, fun ⟨hG⟩ ↦ ⟨StrongTrans.fullyFaithfulToDescentData η f hff hG⟩⟩
  have := hη S
  let E := (η.app (.mk (op S))).toFunctor
  -- `G.toDescentData f` is `E.inv ⋙ E ⋙ G.toDescentData f`, and `E ⋙ G.toDescentData f` is
  -- `F.toDescentData f ⋙ η.mapDescentData f`.
  exact ((Functor.FullyFaithful.ofFullyFaithful E.inv).comp
    ((hF.comp (η.fullyFaithfulMapDescentData f hff)).ofIso
      (η.toDescentDataCompMapDescentDataIso f))).ofIso
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight E.asEquivalence.counitIso (G.toDescentData f) ≪≫ Functor.leftUnitor _)

/-- For a strong transformation `η : F ⟶ G` whose components are equivalences, the descent
functor of `F` along a family `f` is an equivalence if and only if that of `G` is. -/
lemma isEquivalence_toDescentData_iff_of_isEquivalence :
    (F.toDescentData f).IsEquivalence ↔ (G.toDescentData f).IsEquivalence := by
  have := hη S
  have := η.isEquivalence_mapDescentData f hη
  let e := η.toDescentDataCompMapDescentDataIso f
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have := Functor.isEquivalence_of_iso e
    exact Functor.isEquivalence_of_comp_left (η.app (.mk (op S))).toFunctor _
  · have := Functor.isEquivalence_of_iso e.symm
    exact Functor.isEquivalence_of_comp_right _ (η.mapDescentData f)

omit hη in
/-- If the components of `η : F ⟶ G` are fully faithful and `G` satisfies the descent of
morphisms along a presieve `R`, then so does `F`. -/
lemma IsPrestackFor.of_fullyFaithful (hη : ∀ U : C, (η.app (.mk (op U))).toFunctor.FullyFaithful)
    {R : Presieve S} (hG : G.IsPrestackFor R) : F.IsPrestackFor R :=
  ⟨⟨StrongTrans.fullyFaithfulToDescentData η _ hη hG.fullyFaithful⟩⟩

/-- For a strong transformation `η : F ⟶ G` whose components are equivalences, `F` satisfies the
descent of morphisms along a presieve if and only if `G` does. -/
lemma isPrestackFor_iff_of_isEquivalence (R : Presieve S) :
    F.IsPrestackFor R ↔ G.IsPrestackFor R := by
  simp only [isPrestackFor_iff]
  exact nonempty_fullyFaithful_toDescentData_iff_of_isEquivalence η _ hη

/-- For a strong transformation `η : F ⟶ G` whose components are equivalences, `F` has effective
descent along a presieve if and only if `G` does. -/
lemma isStackFor_iff_of_isEquivalence (R : Presieve S) : F.IsStackFor R ↔ G.IsStackFor R := by
  simp only [isStackFor_iff]
  exact isEquivalence_toDescentData_iff_of_isEquivalence η _ hη

end

variable {J : GrothendieckTopology C}

/-- If the components of a strong transformation `η : F ⟶ G` are fully faithful and `G` is a
prestack, then `F` is a prestack. -/
theorem isPrestack_source_of_fullyFaithful [G.IsPrestack J] (η : StrongTrans F G)
    (hη : ∀ U : C, (η.app (.mk (op U))).toFunctor.FullyFaithful) : F.IsPrestack J :=
  .of_isPrestackFor fun _ R hR ↦ (G.isPrestackFor' R hR).of_fullyFaithful η hη

/-- For a strong transformation `η : F ⟶ G` whose components are equivalences of fibre
categories, `F` is a prestack if and only if `G` is. -/
theorem isPrestack_iff_of_isEquivalence (η : StrongTrans F G)
    (hη : ∀ U : C, (η.app (.mk (op U))).toFunctor.IsEquivalence) :
    F.IsPrestack J ↔ G.IsPrestack J :=
  ⟨fun _ ↦ .of_isPrestackFor fun _ R hR ↦
      (isPrestackFor_iff_of_isEquivalence η hη R.arrows).1 (F.isPrestackFor' R hR),
    fun _ ↦ .of_isPrestackFor fun _ R hR ↦
      (isPrestackFor_iff_of_isEquivalence η hη R.arrows).2 (G.isPrestackFor' R hR)⟩

/-- For a strong transformation `η : F ⟶ G` whose components are equivalences of fibre
categories, `F` is a stack if and only if `G` is. -/
theorem isStack_iff_of_isEquivalence (η : StrongTrans F G)
    (hη : ∀ U : C, (η.app (.mk (op U))).toFunctor.IsEquivalence) :
    F.IsStack J ↔ G.IsStack J :=
  ⟨fun _ ↦ .of_isStackFor fun _ R hR ↦
      (isStackFor_iff_of_isEquivalence η hη R.arrows).1 (F.isStackFor' R hR),
    fun _ ↦ .of_isStackFor fun _ R hR ↦
      (isStackFor_iff_of_isEquivalence η hη R.arrows).2 (G.isStackFor' R hR)⟩

end CategoryTheory.Pseudofunctor
