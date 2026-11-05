/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Adjunction.Basic
public import TauCeti.CategoryTheory.Bicategory.Basic
public import TauCeti.CategoryTheory.Bicategory.Biequivalence
public import TauCeti.CategoryTheory.Bicategory.FunctorBicategory.Precomp

/-!
# The biequivalence of families induced by an equivalence of indexing categories

For a bicategory `B` and a functor `f : Γ ⥤ Λ`, the pseudofunctor
`precomp B f.toPseudofunctor : (LocallyDiscrete Λ ⥤ᵖ B) ⥤ᵖ (LocallyDiscrete Γ ⥤ᵖ B)` pulls
families of objects of `B` indexed by `Λ` back to `Γ`. This file constructs the identity and
composition comparisons of pulling back, `precomp B (𝟭 Γ).toPseudofunctor ≌ Pseudofunctor.id _`
and `precomp B (f ⋙ g).toPseudofunctor ≌ (precomp B g.toPseudofunctor).comp (precomp B
f.toPseudofunctor)`, and deduces that an equivalence `e : Γ ≌ Λ` induces a biequivalence

`precompBiequivalence B e :
  TauCeti.Biequivalence (LocallyDiscrete Γ ⥤ᵖ B) (LocallyDiscrete Λ ⥤ᵖ B)`

whose pseudofunctors pull back along `e.inverse` and `e.functor`. For `B = Cat` this transports
families of categories, with their transport functors and all coherence data, along an
equivalence of parameter groupoids. Applied to `e.prod (Equivalence.refl)`, it relates
pseudofunctors on `Γ × SingleObj H` and on `Λ × SingleObj H`, the joint pseudofunctors of
equivariant families of categories.

Pulling a family `F` back along `𝟭 Γ` gives a pseudofunctor with the same objects, `1`-morphisms
and `2`-morphisms as `F`, but with unit and composition comparisons that are equal to those of
`F` only after a computation. The strong transformations `F.pullbackIdHom` and
`F.pullbackIdInv` between the two have identity components; so do `F.pullbackCompHom f g` and
`F.pullbackCompInv f g` between the pullbacks along `f ⋙ g` and along `g` then `f`. They are
natural in `F`, giving the adjoint equivalences

* `precompIdEquiv B Γ : precomp B (𝟭 Γ).toPseudofunctor ≌ Pseudofunctor.id _`,
* `precompCompEquiv B f g : precomp B (f ⋙ g).toPseudofunctor ≌
  (precomp B g.toPseudofunctor).comp (precomp B f.toPseudofunctor)`

in bicategories of pseudofunctors. With the equivalences `precompNatIso B e.unitIso` and
`precompNatIso B e.counitIso` they assemble into the unit and counit of `precompBiequivalence`.

## Main definitions

* `CategoryTheory.Pseudofunctor.precompIdEquiv`: pulling back along the identity functor is
  equivalent to the identity pseudofunctor;
* `CategoryTheory.Pseudofunctor.precompCompEquiv`: pulling back along a composite functor is
  equivalent to the composite of the pullbacks;
* `CategoryTheory.Pseudofunctor.precompBiequivalence`: the biequivalence induced by an
  equivalence of indexing categories.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055): pseudofunctors, strong
  transformations, modifications and biequivalences.
* Edward Frenkel,
  [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  Cambridge Studies in Advanced Mathematics 103 (2007): families of local categories over the
  groupoid of local Langlands parameters, and their descent to local systems.
-/

public section

namespace CategoryTheory.Pseudofunctor

open Bicategory StrongTrans

universe w₃ v₃ u₃ v₂ u₂ v₁ u₁ v₄ u₄

variable {B : Type u₃} [Bicategory.{w₃, v₃} B] {Γ : Type u₁} [Category.{v₁} Γ]
  {Λ : Type u₂} [Category.{v₂} Λ] {Λ' : Type u₄} [Category.{v₄} Λ']

/-! ### Pulling back along the identity functor -/

variable (B Γ) in
/-- The strong transformation `precomp B (𝟭 Γ).toPseudofunctor ⟶ Pseudofunctor.id _` with
components `F.pullbackIdHom`. Its naturality isomorphisms are given by the unitors. -/
-- The body is exposed so that the components of the unit and counit of `precompIdEquiv`, whose
-- types mention the components of this transformation, can be stated.
@[expose] def precompIdHom :
    precomp B (𝟭 Γ).toPseudofunctor ⟶ Pseudofunctor.id (LocallyDiscrete Γ ⥤ᵖ B) where
  app F := pullbackIdHom F
  naturality {F G} η := isoMk (fun x => ρ_ (η.app x) ≪≫ (λ_ (η.app x)).symm)
    (fun φ => rightUnitor_trans_leftUnitor_symm_naturality_whisker _ _ _ _
      (η.naturality φ).hom)
  naturality_naturality Θ := by
    ext x
    exact rightUnitor_trans_leftUnitor_symm_naturality (Θ.as.app x)
  naturality_id F := by
    ext x
    exact rightUnitor_trans_leftUnitor_symm_naturality_id _ _ rfl
      (whiskerLeftId_hom_as_app _ _ _)
  naturality_comp η θ := by
    ext x
    exact rightUnitor_trans_leftUnitor_symm_naturality_comp _ _ _ _ rfl
      (whiskerLeftComp_hom_as_app _ _ _ _)

@[simp]
lemma precompIdHom_app (F : LocallyDiscrete Γ ⥤ᵖ B) :
    (precompIdHom B Γ).app F = F.pullbackIdHom :=
  (rfl)

@[simp]
lemma precompIdHom_naturality_hom_as_app {F G : LocallyDiscrete Γ ⥤ᵖ B} (η : F ⟶ G)
    (x : LocallyDiscrete Γ) :
    ((precompIdHom B Γ).naturality η).hom.as.app x = (ρ_ (η.app x)).hom ≫ (λ_ (η.app x)).inv :=
  (rfl)

@[simp]
lemma precompIdHom_naturality_inv_as_app {F G : LocallyDiscrete Γ ⥤ᵖ B} (η : F ⟶ G)
    (x : LocallyDiscrete Γ) :
    ((precompIdHom B Γ).naturality η).inv.as.app x = (λ_ (η.app x)).hom ≫ (ρ_ (η.app x)).inv :=
  (rfl)

variable (B Γ) in
/-- The strong transformation `Pseudofunctor.id _ ⟶ precomp B (𝟭 Γ).toPseudofunctor` with
components `F.pullbackIdInv`. Its naturality isomorphisms are given by the unitors. -/
-- The body is exposed so that the components of the unit and counit of `precompIdEquiv`, whose
-- types mention the components of this transformation, can be stated.
@[expose] def precompIdInv :
    Pseudofunctor.id (LocallyDiscrete Γ ⥤ᵖ B) ⟶ precomp B (𝟭 Γ).toPseudofunctor where
  app F := pullbackIdInv F
  naturality {F G} η := isoMk (fun x => ρ_ (η.app x) ≪≫ (λ_ (η.app x)).symm)
    (fun φ => rightUnitor_trans_leftUnitor_symm_naturality_whisker _ _ _ _
      (η.naturality φ).hom)
  naturality_naturality Θ := by
    ext x
    exact rightUnitor_trans_leftUnitor_symm_naturality (Θ.as.app x)
  naturality_id F := by
    ext x
    exact rightUnitor_trans_leftUnitor_symm_naturality_id _ _
      (whiskerLeftId_hom_as_app _ _ _) rfl
  naturality_comp η θ := by
    ext x
    exact rightUnitor_trans_leftUnitor_symm_naturality_comp _ _ _ _
      (whiskerLeftComp_hom_as_app _ _ _ _) rfl

@[simp]
lemma precompIdInv_app (F : LocallyDiscrete Γ ⥤ᵖ B) :
    (precompIdInv B Γ).app F = F.pullbackIdInv :=
  (rfl)

@[simp]
lemma precompIdInv_naturality_hom_as_app {F G : LocallyDiscrete Γ ⥤ᵖ B} (η : F ⟶ G)
    (x : LocallyDiscrete Γ) :
    ((precompIdInv B Γ).naturality η).hom.as.app x = (ρ_ (η.app x)).hom ≫ (λ_ (η.app x)).inv :=
  (rfl)

@[simp]
lemma precompIdInv_naturality_inv_as_app {F G : LocallyDiscrete Γ ⥤ᵖ B} (η : F ⟶ G)
    (x : LocallyDiscrete Γ) :
    ((precompIdInv B Γ).naturality η).inv.as.app x = (λ_ (η.app x)).hom ≫ (ρ_ (η.app x)).inv :=
  (rfl)

variable (B Γ) in
/-- Pulling back along the identity functor is equivalent to the identity pseudofunctor of the
bicategory of families indexed by `Γ`, through `precompIdHom` and `precompIdInv`. The unit and
counit have components the unitors `λ_ (𝟙 (F.obj x))`. -/
-- The body is exposed so that the types of the components of its unit and counit, which
-- mention its `1`-morphisms, can be computed.
@[expose] def precompIdEquiv :
    Bicategory.Equivalence (precomp B (𝟭 Γ).toPseudofunctor)
      (Pseudofunctor.id (LocallyDiscrete Γ ⥤ᵖ B)) :=
  Equivalence.mkOfAdjointifyCounit (f := precompIdHom B Γ) (g := precompIdInv B Γ)
    (StrongTrans.isoMk (fun (F : LocallyDiscrete Γ ⥤ᵖ B) =>
      StrongTrans.isoMk (fun (x : LocallyDiscrete Γ) => (λ_ (𝟙 (F.obj x))).symm)
      (fun φ => rightUnitor_trans_leftUnitor_symm_naturality_leftUnitor_inv _))
      (fun η => by
        ext x
        exact rightUnitor_trans_leftUnitor_symm_naturality_leftUnitor_inv (η.app x)))
    (StrongTrans.isoMk (fun (F : LocallyDiscrete Γ ⥤ᵖ B) =>
      StrongTrans.isoMk (fun (x : LocallyDiscrete Γ) => λ_ (𝟙 (F.obj x)))
      (fun φ => rightUnitor_trans_leftUnitor_symm_naturality_leftUnitor _))
      (fun η => by
        ext x
        exact rightUnitor_trans_leftUnitor_symm_naturality_leftUnitor (η.app x)))

@[simp]
lemma precompIdEquiv_hom : (precompIdEquiv B Γ).hom = precompIdHom B Γ :=
  (rfl)

@[simp]
lemma precompIdEquiv_inv : (precompIdEquiv B Γ).inv = precompIdInv B Γ :=
  (rfl)

@[simp]
lemma precompIdEquiv_unit_hom_as_app_as_app (F : LocallyDiscrete Γ ⥤ᵖ B) (x : LocallyDiscrete Γ) :
    (((precompIdEquiv B Γ).unit.hom.as.app F).as.app x) = (λ_ (𝟙 (F.obj x))).inv :=
  (rfl)

@[simp]
lemma precompIdEquiv_unit_inv_as_app_as_app (F : LocallyDiscrete Γ ⥤ᵖ B) (x : LocallyDiscrete Γ) :
    (((precompIdEquiv B Γ).unit.inv.as.app F).as.app x) = (λ_ (𝟙 (F.obj x))).hom :=
  (rfl)

/-- The adjointified counit of `precompIdEquiv` still has components the left unitors. -/
@[simp]
lemma precompIdEquiv_counit_hom_as_app_as_app (F : LocallyDiscrete Γ ⥤ᵖ B) (x : LocallyDiscrete Γ) :
    (((precompIdEquiv B Γ).counit.hom.as.app F).as.app x) = (λ_ (𝟙 (F.obj x))).hom := by
  dsimp only [precompIdEquiv, Equivalence.mkOfAdjointifyCounit]
  -- The given counit satisfies the left triangle identity componentwise, so adjointifying it
  -- does not change it.
  rw [adjointifyCounit_eq_of_left_triangle (by
    ext G y
    exact leftZigzag_leftUnitor_inv_leftUnitor_hom _)]
  rfl

@[simp]
lemma precompIdEquiv_counit_inv_as_app_as_app (F : LocallyDiscrete Γ ⥤ᵖ B) (x : LocallyDiscrete Γ) :
    (((precompIdEquiv B Γ).counit.inv.as.app F).as.app x) = (λ_ (𝟙 (F.obj x))).inv := by
  dsimp only [precompIdEquiv, Equivalence.mkOfAdjointifyCounit]
  -- The given counit satisfies the left triangle identity componentwise, so adjointifying it
  -- does not change it.
  rw [adjointifyCounit_eq_of_left_triangle (by
    ext G y
    exact leftZigzag_leftUnitor_inv_leftUnitor_hom _)]
  rfl

/-! ### Pulling back along a composite functor -/

-- The unit and composition comparisons of the composite of two precomposition pseudofunctors
-- have identity components.
private lemma precomp_comp_mapId_hom_as_app (f : Γ ⥤ Λ) (g : Λ ⥤ Λ')
    (F : LocallyDiscrete Λ' ⥤ᵖ B) (x : LocallyDiscrete Γ) :
    (((precomp B g.toPseudofunctor).comp (precomp B f.toPseudofunctor)).mapId F).hom.as.app x =
      𝟙 _ :=
  -- The component is `𝟙 _ ≫ 𝟙 _`, the components of the two whiskered unit comparisons.
  (congrArg₂ (· ≫ ·) (whiskerLeftId_hom_as_app g.toPseudofunctor F (f.toPseudofunctor.obj x))
    (whiskerLeftId_hom_as_app f.toPseudofunctor (g.toPseudofunctor.comp F) x)).trans
      (Category.comp_id _)

private lemma precomp_comp_mapComp_hom_as_app (f : Γ ⥤ Λ) (g : Λ ⥤ Λ')
    {F G H : LocallyDiscrete Λ' ⥤ᵖ B} (η : F ⟶ G) (θ : G ⟶ H) (x : LocallyDiscrete Γ) :
    (((precomp B g.toPseudofunctor).comp (precomp B f.toPseudofunctor)).mapComp η θ).hom.as.app
      x = 𝟙 _ :=
  -- The component is `𝟙 _ ≫ 𝟙 _`, the components of the two whiskered composition comparisons.
  (congrArg₂ (· ≫ ·)
    (whiskerLeftComp_hom_as_app g.toPseudofunctor η θ (f.toPseudofunctor.obj x))
    (whiskerLeftComp_hom_as_app f.toPseudofunctor (g.toPseudofunctor.whiskerLeft η)
      (g.toPseudofunctor.whiskerLeft θ) x)).trans (Category.comp_id _)

variable (B) in
/-- The strong transformation from pulling back along `f ⋙ g` to the composite of pulling back
along `g` and along `f`, with components `F.pullbackCompHom f g`. Its naturality isomorphisms
are given by the unitors. -/
-- The body is exposed so that the components of the unit and counit of `precompCompEquiv`, whose
-- types mention the components of this transformation, can be stated.
@[expose] def precompCompHom (f : Γ ⥤ Λ) (g : Λ ⥤ Λ') :
    precomp B (f ⋙ g).toPseudofunctor ⟶
      (precomp B g.toPseudofunctor).comp (precomp B f.toPseudofunctor) where
  app F := pullbackCompHom f g F
  naturality {F G} η := isoMk (fun x => ρ_ (η.app ⟨g.obj (f.obj x.as)⟩) ≪≫ (λ_ _).symm)
    (fun φ => rightUnitor_trans_leftUnitor_symm_naturality_whisker _ _ _ _
      (η.naturality _).hom)
  naturality_naturality Θ := by
    ext x
    exact rightUnitor_trans_leftUnitor_symm_naturality (Θ.as.app _)
  naturality_id F := by
    ext x
    exact rightUnitor_trans_leftUnitor_symm_naturality_id _ _
      (precomp_comp_mapId_hom_as_app f g F x)
      (whiskerLeftId_hom_as_app _ _ _)
  naturality_comp η θ := by
    ext x
    exact rightUnitor_trans_leftUnitor_symm_naturality_comp _ _ _ _
      (precomp_comp_mapComp_hom_as_app f g η θ x)
      (whiskerLeftComp_hom_as_app _ _ _ _)

@[simp]
lemma precompCompHom_app (f : Γ ⥤ Λ) (g : Λ ⥤ Λ') (F : LocallyDiscrete Λ' ⥤ᵖ B) :
    (precompCompHom B f g).app F = F.pullbackCompHom f g :=
  (rfl)

@[simp]
lemma precompCompHom_naturality_hom_as_app (f : Γ ⥤ Λ) (g : Λ ⥤ Λ')
    {F G : LocallyDiscrete Λ' ⥤ᵖ B} (η : F ⟶ G) (x : LocallyDiscrete Γ) :
    ((precompCompHom B f g).naturality η).hom.as.app x =
      (ρ_ (η.app ⟨g.obj (f.obj x.as)⟩)).hom ≫ (λ_ (η.app ⟨g.obj (f.obj x.as)⟩)).inv :=
  (rfl)

@[simp]
lemma precompCompHom_naturality_inv_as_app (f : Γ ⥤ Λ) (g : Λ ⥤ Λ')
    {F G : LocallyDiscrete Λ' ⥤ᵖ B} (η : F ⟶ G) (x : LocallyDiscrete Γ) :
    ((precompCompHom B f g).naturality η).inv.as.app x =
      (λ_ (η.app ⟨g.obj (f.obj x.as)⟩)).hom ≫ (ρ_ (η.app ⟨g.obj (f.obj x.as)⟩)).inv :=
  (rfl)

variable (B) in
/-- The strong transformation from the composite of pulling back along `g` and along `f` to
pulling back along `f ⋙ g`, with components `F.pullbackCompInv f g`. Its naturality
isomorphisms are given by the unitors. -/
-- The body is exposed so that the components of the unit and counit of `precompCompEquiv`, whose
-- types mention the components of this transformation, can be stated.
@[expose] def precompCompInv (f : Γ ⥤ Λ) (g : Λ ⥤ Λ') :
    (precomp B g.toPseudofunctor).comp (precomp B f.toPseudofunctor) ⟶
      precomp B (f ⋙ g).toPseudofunctor where
  app F := pullbackCompInv f g F
  naturality {F G} η := isoMk (fun x => ρ_ (η.app ⟨g.obj (f.obj x.as)⟩) ≪≫ (λ_ _).symm)
    (fun φ => rightUnitor_trans_leftUnitor_symm_naturality_whisker _ _ _ _
      (η.naturality _).hom)
  naturality_naturality Θ := by
    ext x
    exact rightUnitor_trans_leftUnitor_symm_naturality (Θ.as.app _)
  naturality_id F := by
    ext x
    exact rightUnitor_trans_leftUnitor_symm_naturality_id _ _
      (whiskerLeftId_hom_as_app _ _ _)
      (precomp_comp_mapId_hom_as_app f g F x)
  naturality_comp η θ := by
    ext x
    exact rightUnitor_trans_leftUnitor_symm_naturality_comp _ _ _ _
      (whiskerLeftComp_hom_as_app _ _ _ _)
      (precomp_comp_mapComp_hom_as_app f g η θ x)

@[simp]
lemma precompCompInv_app (f : Γ ⥤ Λ) (g : Λ ⥤ Λ') (F : LocallyDiscrete Λ' ⥤ᵖ B) :
    (precompCompInv B f g).app F = F.pullbackCompInv f g :=
  (rfl)

@[simp]
lemma precompCompInv_naturality_hom_as_app (f : Γ ⥤ Λ) (g : Λ ⥤ Λ')
    {F G : LocallyDiscrete Λ' ⥤ᵖ B} (η : F ⟶ G) (x : LocallyDiscrete Γ) :
    ((precompCompInv B f g).naturality η).hom.as.app x =
      (ρ_ (η.app ⟨g.obj (f.obj x.as)⟩)).hom ≫ (λ_ (η.app ⟨g.obj (f.obj x.as)⟩)).inv :=
  (rfl)

@[simp]
lemma precompCompInv_naturality_inv_as_app (f : Γ ⥤ Λ) (g : Λ ⥤ Λ')
    {F G : LocallyDiscrete Λ' ⥤ᵖ B} (η : F ⟶ G) (x : LocallyDiscrete Γ) :
    ((precompCompInv B f g).naturality η).inv.as.app x =
      (λ_ (η.app ⟨g.obj (f.obj x.as)⟩)).hom ≫ (ρ_ (η.app ⟨g.obj (f.obj x.as)⟩)).inv :=
  (rfl)

variable (B) in
/-- Pulling back along a composite functor `f ⋙ g` is equivalent to pulling back along `g` and
then along `f`, through `precompCompHom` and `precompCompInv`. The unit and counit have
components the unitors. -/
-- The body is exposed so that the types of the components of its unit and counit, which
-- mention its `1`-morphisms, can be computed.
@[expose] def precompCompEquiv (f : Γ ⥤ Λ) (g : Λ ⥤ Λ') :
    Bicategory.Equivalence (precomp B (f ⋙ g).toPseudofunctor)
      ((precomp B g.toPseudofunctor).comp (precomp B f.toPseudofunctor)) :=
  Equivalence.mkOfAdjointifyCounit (f := precompCompHom B f g) (g := precompCompInv B f g)
    (StrongTrans.isoMk (fun (F : LocallyDiscrete Λ' ⥤ᵖ B) =>
      StrongTrans.isoMk (fun (x : LocallyDiscrete Γ) =>
        (λ_ (𝟙 (F.obj ⟨g.obj (f.obj x.as)⟩))).symm)
      (fun φ => rightUnitor_trans_leftUnitor_symm_naturality_leftUnitor_inv _))
      (fun η => by
        ext x
        exact rightUnitor_trans_leftUnitor_symm_naturality_leftUnitor_inv (η.app _)))
    (StrongTrans.isoMk (fun (F : LocallyDiscrete Λ' ⥤ᵖ B) =>
      StrongTrans.isoMk (fun (x : LocallyDiscrete Γ) => λ_ (𝟙 (F.obj ⟨g.obj (f.obj x.as)⟩)))
      (fun φ => rightUnitor_trans_leftUnitor_symm_naturality_leftUnitor _))
      (fun η => by
        ext x
        exact rightUnitor_trans_leftUnitor_symm_naturality_leftUnitor (η.app _)))

@[simp]
lemma precompCompEquiv_hom (f : Γ ⥤ Λ) (g : Λ ⥤ Λ') :
    (precompCompEquiv B f g).hom = precompCompHom B f g :=
  (rfl)

@[simp]
lemma precompCompEquiv_inv (f : Γ ⥤ Λ) (g : Λ ⥤ Λ') :
    (precompCompEquiv B f g).inv = precompCompInv B f g :=
  (rfl)

@[simp]
lemma precompCompEquiv_unit_hom_as_app_as_app (f : Γ ⥤ Λ) (g : Λ ⥤ Λ')
    (F : LocallyDiscrete Λ' ⥤ᵖ B) (x : LocallyDiscrete Γ) :
    (((precompCompEquiv B f g).unit.hom.as.app F).as.app x) =
      (λ_ (𝟙 (F.obj ⟨g.obj (f.obj x.as)⟩))).inv :=
  (rfl)

@[simp]
lemma precompCompEquiv_unit_inv_as_app_as_app (f : Γ ⥤ Λ) (g : Λ ⥤ Λ')
    (F : LocallyDiscrete Λ' ⥤ᵖ B) (x : LocallyDiscrete Γ) :
    (((precompCompEquiv B f g).unit.inv.as.app F).as.app x) =
      (λ_ (𝟙 (F.obj ⟨g.obj (f.obj x.as)⟩))).hom :=
  (rfl)

/-- The adjointified counit of `precompCompEquiv` still has components the left unitors. -/
@[simp]
lemma precompCompEquiv_counit_hom_as_app_as_app (f : Γ ⥤ Λ) (g : Λ ⥤ Λ')
    (F : LocallyDiscrete Λ' ⥤ᵖ B) (x : LocallyDiscrete Γ) :
    (((precompCompEquiv B f g).counit.hom.as.app F).as.app x) =
      (λ_ (𝟙 (F.obj ⟨g.obj (f.obj x.as)⟩))).hom := by
  dsimp only [precompCompEquiv, Equivalence.mkOfAdjointifyCounit]
  -- The given counit satisfies the left triangle identity componentwise, so adjointifying it
  -- does not change it.
  rw [adjointifyCounit_eq_of_left_triangle (by
    ext G y
    exact leftZigzag_leftUnitor_inv_leftUnitor_hom _)]
  rfl

@[simp]
lemma precompCompEquiv_counit_inv_as_app_as_app (f : Γ ⥤ Λ) (g : Λ ⥤ Λ')
    (F : LocallyDiscrete Λ' ⥤ᵖ B) (x : LocallyDiscrete Γ) :
    (((precompCompEquiv B f g).counit.inv.as.app F).as.app x) =
      (λ_ (𝟙 (F.obj ⟨g.obj (f.obj x.as)⟩))).inv := by
  dsimp only [precompCompEquiv, Equivalence.mkOfAdjointifyCounit]
  -- The given counit satisfies the left triangle identity componentwise, so adjointifying it
  -- does not change it.
  rw [adjointifyCounit_eq_of_left_triangle (by
    ext G y
    exact leftZigzag_leftUnitor_inv_leftUnitor_hom _)]
  rfl

/-! ### The biequivalence induced by an equivalence of indexing categories -/

variable (B) in
/-- An equivalence `e : Γ ≌ Λ` induces a biequivalence between the bicategories of families
`LocallyDiscrete Γ ⥤ᵖ B` and `LocallyDiscrete Λ ⥤ᵖ B`, with pseudofunctors pulling back along
`e.inverse` and along `e.functor`. Its unit is the composite of `(precompIdEquiv B Γ).symm`,
the equivalence `precompNatIso B e.unitIso` and `precompCompEquiv B e.functor e.inverse`; its
counit is the composite of `(precompCompEquiv B e.inverse e.functor).symm`,
`precompNatIso B e.counitIso` and `precompIdEquiv B Λ`. -/
-- The body is exposed so that the types of the unit and counit equivalences, which mention the
-- two pseudofunctors, can be computed in `precompBiequivalence_unitEquiv_hom` and its siblings.
@[expose] def precompBiequivalence (e : Γ ≌ Λ) :
    TauCeti.Biequivalence (LocallyDiscrete Γ ⥤ᵖ B) (LocallyDiscrete Λ ⥤ᵖ B) where
  functor := precomp B e.inverse.toPseudofunctor
  inverse := precomp B e.functor.toPseudofunctor
  unitEquiv := (precompIdEquiv B Γ).symm.trans
    ((precompNatIso B e.unitIso).trans (precompCompEquiv B e.functor e.inverse))
  counitEquiv := (precompCompEquiv B e.inverse e.functor).symm.trans
    ((precompNatIso B e.counitIso).trans (precompIdEquiv B Λ))

@[simp]
lemma precompBiequivalence_functor (e : Γ ≌ Λ) :
    (precompBiequivalence B e).functor = precomp B e.inverse.toPseudofunctor :=
  (rfl)

@[simp]
lemma precompBiequivalence_inverse (e : Γ ≌ Λ) :
    (precompBiequivalence B e).inverse = precomp B e.functor.toPseudofunctor :=
  (rfl)

@[simp]
lemma precompBiequivalence_unitEquiv_hom (e : Γ ≌ Λ) :
    (precompBiequivalence B e).unitEquiv.hom =
      precompIdInv B Γ ≫ precompNatTrans B e.unit ≫ precompCompHom B e.functor e.inverse := by
  simp [precompBiequivalence]

@[simp]
lemma precompBiequivalence_unitEquiv_inv (e : Γ ≌ Λ) :
    (precompBiequivalence B e).unitEquiv.inv =
      (precompCompInv B e.functor e.inverse ≫ precompNatTrans B e.unitInv) ≫
        precompIdHom B Γ := by
  simp [precompBiequivalence]

@[simp]
lemma precompBiequivalence_counitEquiv_hom (e : Γ ≌ Λ) :
    (precompBiequivalence B e).counitEquiv.hom =
      precompCompInv B e.inverse e.functor ≫ precompNatTrans B e.counit ≫ precompIdHom B Λ := by
  simp [precompBiequivalence]

@[simp]
lemma precompBiequivalence_counitEquiv_inv (e : Γ ≌ Λ) :
    (precompBiequivalence B e).counitEquiv.inv =
      (precompIdInv B Λ ≫ precompNatTrans B e.counitInv) ≫
        precompCompHom B e.inverse e.functor := by
  simp [precompBiequivalence]

end CategoryTheory.Pseudofunctor
