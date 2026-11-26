/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Cat
public import TauCeti.CategoryTheory.Sites.Descent.IsPrestack

/-!
# Descent data along a strong transformation

Let `φ : F ⟶ G` be a strong transformation of pseudofunctors `LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`. A local
morphism `a : f₁^* M₁ ⟶ f₂^* M₂` of `F` over `Y`, for `f₁ : Y ⟶ X₁` and `f₂ : Y ⟶ X₂`, is sent to
the local morphism `f₁^* (φ M₁) ⟶ f₂^* (φ M₂)` of `G` obtained by applying `φ` over `Y` and
conjugating by the naturality isomorphisms of `φ` at `f₁` and `f₂`
(`Pseudofunctor.StrongTrans.mapPullbackHom`). This is compatible with composition, identities and
pullback of local morphisms (`mapPullbackHom_comp`, `mapPullbackHom_id`,
`pullHom_mapPullbackHom`), so it sends descent data for `F` along a family `f` to descent data for
`G` along `f`: this is the functor `φ.mapDescentData f : F.DescentData f ⥤ G.DescentData f`. It is
compatible with the functors `toDescentData` (`StrongTrans.toDescentDataCompMapDescentDataIso`),
with identities and composites of strong transformations (`StrongTrans.mapDescentDataId`,
`StrongTrans.mapDescentDataComp`), and a modification `Γ : φ ⟶ φ'` induces a natural transformation
`φ.mapDescentData f ⟶ φ'.mapDescentData f` (`StrongTrans.mapDescentData₂`).

These constructions are the fibrewise part of the functoriality of the stackification of prestacks
in strong transformations.
-/

public section

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.StrongTrans

open LocallyDiscreteOpToCat

universe v' u' v u t

variable {C : Type u} [Category.{v} C] {F G H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}

section mapPullbackHom

variable (φ : F ⟶ G)

/-- The local morphism `f₁^* (φ M₁) ⟶ f₂^* (φ M₂)` of `G` given by a local morphism
`a : f₁^* M₁ ⟶ f₂^* M₂` of `F`: apply `φ` over `Y` and conjugate by the naturality isomorphisms of
`φ` at `f₁` and `f₂`. -/
def mapPullbackHom ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (a : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) :
    (G.map f₁.op.toLoc).toFunctor.obj ((φ.app _).toFunctor.obj M₁) ⟶
      (G.map f₂.op.toLoc).toFunctor.obj ((φ.app _).toFunctor.obj M₂) :=
  (φ.naturality f₁.op.toLoc).inv.toNatTrans.app M₁ ≫ (φ.app _).toFunctor.map a ≫
    (φ.naturality f₂.op.toLoc).hom.toNatTrans.app M₂

/-- `mapPullbackHom` conjugates the image of a local morphism under `φ` by the naturality
isomorphisms of `φ`. -/
lemma mapPullbackHom_def ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (a : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) :
    φ.mapPullbackHom a = (φ.naturality f₁.op.toLoc).inv.toNatTrans.app M₁ ≫
      (φ.app _).toFunctor.map a ≫ (φ.naturality f₂.op.toLoc).hom.toNatTrans.app M₂ :=
  (rfl)

/-- `mapPullbackHom` is compatible with composition. -/
@[reassoc]
lemma mapPullbackHom_comp ⦃X₁ X₂ X₃ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄
    ⦃M₂ : F.obj (.mk (op X₂))⦄ ⦃M₃ : F.obj (.mk (op X₃))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄
    ⦃f₂ : Y ⟶ X₂⦄ ⦃f₃ : Y ⟶ X₃⦄
    (a : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (b : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃) :
    φ.mapPullbackHom (a ≫ b) = φ.mapPullbackHom a ≫ φ.mapPullbackHom b := by
  simp [mapPullbackHom]

/-- `mapPullbackHom` sends identities to identities. -/
@[simp]
lemma mapPullbackHom_id ⦃X : C⦄ (M : F.obj (.mk (op X))) ⦃Y : C⦄ (f : Y ⟶ X) :
    φ.mapPullbackHom (𝟙 ((F.map f.op.toLoc).toFunctor.obj M)) = 𝟙 _ := by
  simp [mapPullbackHom]

/-- `mapPullbackHom` sends the pullback `f^* ψ` of a morphism to the pullback of `φ ψ`. -/
@[simp]
lemma mapPullbackHom_map ⦃X : C⦄ ⦃M M' : F.obj (.mk (op X))⦄ (ψ : M ⟶ M') ⦃Y : C⦄
    (f : Y ⟶ X) :
    φ.mapPullbackHom ((F.map f.op.toLoc).toFunctor.map ψ) =
      (G.map f.op.toLoc).toFunctor.map ((φ.app _).toFunctor.map ψ) :=
  φ.naturality_naturality_1 f.op.toLoc ψ

/-- `mapPullbackHom` is compatible with pullback of local morphisms. -/
lemma pullHom_mapPullbackHom ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (a : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) ⦃Y' : C⦄
    (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    pullHom (φ.mapPullbackHom a) g gf₁ gf₂ hgf₁ hgf₂ =
      φ.mapPullbackHom (pullHom a g gf₁ gf₂ hgf₁ hgf₂) := by
  have key := φ.mapPullbackHom_map a g
  rw [mapPullbackHom_def] at key
  simp only [pullHom, mapPullbackHom_def, Functor.map_comp, Category.assoc,
    naturality_comp'_inv_app φ f₁.op.toLoc g.op.toLoc gf₁.op.toLoc (by rw [← hgf₁]; rfl),
    naturality_comp'_hom_app φ f₂.op.toLoc g.op.toLoc gf₂.op.toLoc (by rw [← hgf₂]; rfl)]
  simp only [← Functor.map_comp_assoc, Cat.Hom.inv_hom_id_toNatTrans_app]
  -- The identity left by cancelling the comparisons of `F` lives over
  -- `(F.map f₂ ≫ F.map g).toFunctor.obj M₂`, which is only definitionally the source of `pullHom`.
  erw [Cat.Hom.inv_hom_id_toNatTrans_app_assoc, Category.comp_id]
  rw [reassoc_of% key]
  simp only [Functor.map_comp, Category.assoc]

/-- `mapPullbackHom` of a composition comparison `(f ≫ g)^* M ⟶ g^* (f^* M)` of `F` is the
composition comparison of `G` followed by the inverse naturality isomorphism of `φ` at `f`. -/
lemma mapPullbackHom_mapComp'_hom ⦃X Y Z : C⦄ (f : Y ⟶ X) (g : Z ⟶ Y) (fg : Z ⟶ X)
    (h : g ≫ f = fg) (M : F.obj (.mk (op X))) :
    φ.mapPullbackHom (f₂ := g) (M₂ := (F.map f.op.toLoc).toFunctor.obj M)
        ((F.mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).hom.toNatTrans.app M) =
      (G.mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).hom.toNatTrans.app
          ((φ.app _).toFunctor.obj M) ≫
        (G.map g.op.toLoc).toFunctor.map ((φ.naturality f.op.toLoc).inv.toNatTrans.app M) := by
  rw [mapPullbackHom_def, naturality_comp'_inv_app φ f.op.toLoc g.op.toLoc fg.op.toLoc
    (by rw [← h]; rfl)]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Cat.Hom.inv_hom_id_toNatTrans_app]
  -- The identity left by cancelling the comparisons of `F` lives over
  -- `(F.map f ≫ F.map g).toFunctor.obj M`, which is only definitionally the source of the
  -- naturality isomorphism of `φ` at `g`.
  erw [CategoryTheory.Functor.map_id]
  simp

/-- `mapPullbackHom` of an inverse composition comparison `g^* (f^* M) ⟶ (f ≫ g)^* M` of `F` is
the naturality isomorphism of `φ` at `f` followed by the inverse composition comparison of
`G`. -/
lemma mapPullbackHom_mapComp'_inv ⦃X Y Z : C⦄ (f : Y ⟶ X) (g : Z ⟶ Y) (fg : Z ⟶ X)
    (h : g ≫ f = fg) (M : F.obj (.mk (op X))) :
    φ.mapPullbackHom (f₁ := g) (M₁ := (F.map f.op.toLoc).toFunctor.obj M)
        ((F.mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).inv.toNatTrans.app M) =
      (G.map g.op.toLoc).toFunctor.map ((φ.naturality f.op.toLoc).hom.toNatTrans.app M) ≫
        (G.mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc (by rw [← h]; rfl)).inv.toNatTrans.app
          ((φ.app _).toFunctor.obj M) := by
  rw [mapPullbackHom_def, naturality_comp'_hom_app φ f.op.toLoc g.op.toLoc fg.op.toLoc
    (by rw [← h]; rfl)]
  simp only [← Functor.map_comp_assoc, Cat.Hom.inv_hom_id_toNatTrans_app]
  -- As in `mapPullbackHom_mapComp'_hom`, the identity is over a composite in `Cat`.
  erw [CategoryTheory.Functor.map_id]
  simp

end mapPullbackHom

/-- `mapPullbackHom` for the identity strong transformation is the identity. -/
@[simp]
lemma id_mapPullbackHom ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄
    ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (a : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) :
    (𝟙 F : F ⟶ F).mapPullbackHom a = a := by
  simp only [mapPullbackHom_def, categoryStruct_id_naturality_inv, categoryStruct_id_naturality_hom]
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

/-- `mapPullbackHom` for a composite of strong transformations is the composite of the
`mapPullbackHom`. -/
@[simp]
lemma comp_mapPullbackHom (φ : F ⟶ G) (ψ : G ⟶ H) ⦃X₁ X₂ : C⦄ ⦃M₁ : F.obj (.mk (op X₁))⦄
    ⦃M₂ : F.obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄ ⦃f₂ : Y ⟶ X₂⦄
    (a : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) :
    (φ ≫ ψ).mapPullbackHom a = ψ.mapPullbackHom (φ.mapPullbackHom a) := by
  simp only [mapPullbackHom_def, comp_naturality_inv_app, comp_naturality_hom_app,
    Functor.map_comp, Category.assoc]
  -- The component of `φ ≫ ψ` over `Y` is the composite of those of `φ` and `ψ`, by definition.
  exact Category.assoc _ _ _

/-- `mapPullbackHom` is natural with respect to modifications. -/
@[reassoc]
lemma map_app_comp_mapPullbackHom {φ φ' : F ⟶ G} (Γ : φ ⟶ φ') ⦃X₁ X₂ : C⦄
    ⦃M₁ : F.obj (.mk (op X₁))⦄ ⦃M₂ : F.obj (.mk (op X₂))⦄ ⦃Y : C⦄ ⦃f₁ : Y ⟶ X₁⦄
    ⦃f₂ : Y ⟶ X₂⦄
    (a : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂) :
    (G.map f₁.op.toLoc).toFunctor.map ((Γ.as.app _).toNatTrans.app M₁) ≫ φ'.mapPullbackHom a =
      φ.mapPullbackHom a ≫ (G.map f₂.op.toLoc).toFunctor.map ((Γ.as.app _).toNatTrans.app M₂) := by
  have h₁ := congrArg (fun m ↦ m.toNatTrans.app M₁) (Γ.as.naturality f₁.op.toLoc)
  have h₂ := congrArg (fun m ↦ m.toNatTrans.app M₂) (Γ.as.naturality f₂.op.toLoc)
  simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app] at h₁ h₂
  rw [mapPullbackHom_def, mapPullbackHom_def,
    ← cancel_epi ((φ.naturality f₁.op.toLoc).hom.toNatTrans.app M₁), ← reassoc_of% h₁]
  simp only [Cat.Hom.hom_inv_id_toNatTrans_app_assoc, Category.assoc, ← h₂]
  exact ((Γ.as.app _).toNatTrans.naturality_assoc a _).symm


section mapDescentData

variable (φ : F ⟶ G) {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- The functor `F.DescentData f ⥤ G.DescentData f` given by a strong transformation `φ : F ⟶ G`:
it applies `φ` to the objects of a descent datum and, through `mapPullbackHom`, to its gluing
morphisms. -/
-- This is an abbreviation so that the objects of a mapped descent datum are reducibly the images of
-- the objects under `φ`: rewriting in local morphisms between them fails otherwise.
abbrev mapDescentData : F.DescentData f ⥤ G.DescentData f where
  obj D :=
    { obj i := (φ.app _).toFunctor.obj (D.obj i)
      hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := φ.mapPullbackHom (D.hom q f₁ f₂ hf₁ hf₂)
      pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
        rw [pullHom_mapPullbackHom, D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
      hom_self Y q i g hg := by rw [D.hom_self q g hg, mapPullbackHom_id]
      hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
        rw [← mapPullbackHom_comp, D.hom_comp] }
  map {D₁ D₂} ψ :=
    { hom i := (φ.app _).toFunctor.map (ψ.hom i)
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
        rw [← mapPullbackHom_map, ← mapPullbackHom_comp, ψ.comm q f₁ f₂ hf₁ hf₂,
          mapPullbackHom_comp, mapPullbackHom_map] }
  map_id D := by
    ext i
    exact (φ.app _).toFunctor.map_id _
  map_comp ψ ψ' := by
    ext i
    exact (φ.app _).toFunctor.map_comp _ _

variable {f} in
@[simp]
lemma mapDescentData_obj_obj (D : F.DescentData f) (i : ι) :
    ((φ.mapDescentData f).obj D).obj i = (φ.app _).toFunctor.obj (D.obj i) :=
  (rfl)

variable {f} in
@[simp]
lemma mapDescentData_obj_hom (D : F.DescentData f) ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    ((φ.mapDescentData f).obj D).hom q f₁ f₂ hf₁ hf₂ = φ.mapPullbackHom (D.hom q f₁ f₂ hf₁ hf₂) :=
  (rfl)

variable {f} in
@[simp]
lemma mapDescentData_map_hom {D₁ D₂ : F.DescentData f} (ψ : D₁ ⟶ D₂) (i : ι) :
    ((φ.mapDescentData f).map ψ).hom i = (φ.app _).toFunctor.map (ψ.hom i) :=
  (rfl)

variable {f} in
/-- The naturality isomorphisms of `φ` at the members of `f` carry the gluing morphisms of the
descent datum of an object `M`, mapped along `φ`, to those of the descent datum of `φ M`. -/
@[reassoc]
lemma map_naturality_hom_comp_ofObj_hom (M : F.obj (.mk (op S))) ⦃Y : C⦄ (q : Y ⟶ S)
    ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (G.map f₁.op.toLoc).toFunctor.map ((φ.naturality (f i₁).op.toLoc).hom.toNatTrans.app M) ≫
        (DescentData.ofObj (f := f) ((φ.app _).toFunctor.obj M)).hom q f₁ f₂ hf₁ hf₂ =
      φ.mapPullbackHom ((DescentData.ofObj (f := f) M).hom q f₁ f₂ hf₁ hf₂) ≫
        (G.map f₂.op.toLoc).toFunctor.map
          ((φ.naturality (f i₂).op.toLoc).hom.toNatTrans.app M) := by
  rw [DescentData.ofObj_hom, DescentData.ofObj_hom]
  -- After unfolding `DescentData.ofObj`, the objects of the two sides agree only up to unfolding
  -- composites in `Cat`, so the expansions of `mapPullbackHom` are applied by `erw`.
  erw [mapPullbackHom_comp, mapPullbackHom_mapComp'_inv φ (f i₁) f₁ q hf₁,
    mapPullbackHom_mapComp'_hom φ (f i₂) f₂ q hf₂]
  -- It remains to cancel the inverse naturality isomorphism at `f i₂` against itself.
  have cancel {D D' : Type u'} [Category.{v'} D] [Category.{v'} D'] (K : D ⥤ D') {P Q : D}
      (e : P ≅ Q) {W₁ W₂ W₃ : D'} (a : W₁ ⟶ W₂) (b : W₂ ⟶ W₃) (c : W₃ ⟶ K.obj Q) :
      a ≫ b ≫ c = ((a ≫ b) ≫ c ≫ K.map e.inv) ≫ K.map e.hom := by
    simp
  exact cancel (G.map f₂.op.toLoc).toFunctor
    ((Cat.Hom.toNatIso (φ.naturality (f i₂).op.toLoc)).app M) _ _ _

/-- Mapping the descent datum of an object `M` along `φ` gives the descent datum of `φ M`, through
the naturality isomorphisms of `φ` at the members of the family. -/
def toDescentDataCompMapDescentDataIso :
    F.toDescentData f ⋙ φ.mapDescentData f ≅ (φ.app (.mk (op S))).toFunctor ⋙ G.toDescentData f :=
  NatIso.ofComponents
    (fun M ↦ DescentData.isoMk (fun i ↦ (Cat.Hom.toNatIso (φ.naturality (f i).op.toLoc)).app M)
      (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ φ.map_naturality_hom_comp_ofObj_hom M q f₁ f₂ hf₁ hf₂))
    (fun {M M'} ψ ↦ by
      ext i
      exact (φ.naturality (f i).op.toLoc).hom.toNatTrans.naturality ψ)

@[simp]
lemma toDescentDataCompMapDescentDataIso_hom_app_hom (M : F.obj (.mk (op S))) (i : ι) :
    ((φ.toDescentDataCompMapDescentDataIso f).hom.app M).hom i =
      (φ.naturality (f i).op.toLoc).hom.toNatTrans.app M :=
  (rfl)

@[simp]
lemma toDescentDataCompMapDescentDataIso_inv_app_hom (M : F.obj (.mk (op S))) (i : ι) :
    ((φ.toDescentDataCompMapDescentDataIso f).inv.app M).hom i =
      (φ.naturality (f i).op.toLoc).inv.toNatTrans.app M :=
  (rfl)

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
        (F.map f₂.op.toLoc).toFunctor (id_mapPullbackHom (D.hom q f₁ f₂ hf₁ hf₂)).symm))
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
def mapDescentDataComp (ψ : G ⟶ H) :
    (φ ≫ ψ).mapDescentData f ≅ φ.mapDescentData f ⋙ ψ.mapDescentData f :=
  NatIso.ofComponents
    (fun D ↦ DescentData.isoMk
      (fun i ↦ Iso.refl _) (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
        -- As in `mapDescentDataId`, the identities are cancelled by unification.
        exact map_id_comp_eq_comp_map_id (H.map f₁.op.toLoc).toFunctor
          (H.map f₂.op.toLoc).toFunctor (comp_mapPullbackHom φ ψ (D.hom q f₁ f₂ hf₁ hf₂)).symm))
    (fun χ ↦ by
      ext i
      -- The components of `φ ≫ ψ` are the composites of those of `φ` and `ψ`, by definition.
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

@[simp]
lemma mapDescentDataComp_hom_app_hom (ψ : G ⟶ H) (D : F.DescentData f) (i : ι) :
    ((φ.mapDescentDataComp f ψ).hom.app D).hom i =
      𝟙 ((ψ.app _).toFunctor.obj ((φ.app _).toFunctor.obj (D.obj i))) :=
  (rfl)

@[simp]
lemma mapDescentDataComp_inv_app_hom (ψ : G ⟶ H) (D : F.DescentData f) (i : ι) :
    ((φ.mapDescentDataComp f ψ).inv.app D).hom i =
      𝟙 ((ψ.app _).toFunctor.obj ((φ.app _).toFunctor.obj (D.obj i))) :=
  (rfl)

/-- The natural transformation between mapped descent data given by a modification `Γ : φ ⟶ φ'`:
its components are those of `Γ`. -/
def mapDescentData₂ {φ φ' : F ⟶ G} (Γ : φ ⟶ φ') : φ.mapDescentData f ⟶ φ'.mapDescentData f where
  app D :=
    { hom i := (Γ.as.app _).toNatTrans.app (D.obj i)
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := map_app_comp_mapPullbackHom Γ _ }
  naturality D₁ D₂ ψ := by
    ext i
    exact (Γ.as.app _).toNatTrans.naturality (ψ.hom i)

@[simp]
lemma mapDescentData₂_app_hom {φ φ' : F ⟶ G} (Γ : φ ⟶ φ') (D : F.DescentData f) (i : ι) :
    ((mapDescentData₂ f Γ).app D).hom i = (Γ.as.app _).toNatTrans.app (D.obj i) :=
  (rfl)

end mapDescentData

end CategoryTheory.Pseudofunctor.StrongTrans
