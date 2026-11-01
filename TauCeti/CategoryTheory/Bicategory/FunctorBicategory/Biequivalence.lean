/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Biequivalence
public import TauCeti.CategoryTheory.Bicategory.FunctorBicategory.Precomp

/-!
# The biequivalence of families induced by an equivalence of indexing categories

For a bicategory `B` and a functor `f : Γ ⥤ Λ`, the pseudofunctor
`precomp B f.toPseudofunctor : (LocallyDiscrete Λ ⥤ᵖ B) ⥤ᵖ (LocallyDiscrete Γ ⥤ᵖ B)` pulls
families of objects of `B` indexed by `Λ` back to `Γ`. This file shows that pulling back is
pseudofunctorial in `f`, and deduces that an equivalence `e : Γ ≌ Λ` induces a biequivalence

`precompBiequivalence B e : Biequivalence (LocallyDiscrete Γ ⥤ᵖ B) (LocallyDiscrete Λ ⥤ᵖ B)`

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

section Aux

variable {B : Type u₃} [Bicategory.{w₃, v₃} B]

-- The coherence conditions of the identity-component transformations below are equations
-- between composites of unitors and associators in `B`. In the goals, their sources and targets
-- are objects such as `((𝟭 Γ).toPseudofunctor.comp F).obj x` and `F.obj x`, which are equal
-- only after unfolding `Pseudofunctor.comp` and `Functor.toPseudofunctor`, so `simp` cannot work
-- on the goals directly. The equations are therefore proved here for arbitrary `1`-morphisms
-- of `B` and applied by unification.

/-- Naturality of `ρ_ ≪≫ (λ_).symm`, the naturality isomorphisms of identity components. -/
private lemma unitors_naturality_whisker {a b : B} {X Y : a ⟶ b} (Θ : X ⟶ Y) :
    Θ ▷ 𝟙 b ≫ (ρ_ Y ≪≫ (λ_ Y).symm).hom = (ρ_ X ≪≫ (λ_ X).symm).hom ≫ 𝟙 a ◁ Θ := by
  simp

/-- The unit condition of an identity-component transformation. -/
private lemma unitors_naturality_id {a : B} (e e' : 𝟙 a ⟶ 𝟙 a) (he : e = 𝟙 _) (he' : e' = 𝟙 _) :
    (ρ_ (𝟙 a) ≪≫ (λ_ (𝟙 a)).symm).hom ≫ 𝟙 a ◁ e =
      e' ▷ 𝟙 a ≫ (λ_ (𝟙 a)).hom ≫ (ρ_ (𝟙 a)).inv := by
  subst he he'
  simp [unitors_equal]

/-- The composition condition of an identity-component transformation. -/
private lemma unitors_naturality_comp {a b c : B} (u : a ⟶ b) (v : b ⟶ c)
    (e e' : u ≫ v ⟶ u ≫ v) (he : e = 𝟙 _) (he' : e' = 𝟙 _) :
    (ρ_ (u ≫ v) ≪≫ (λ_ (u ≫ v)).symm).hom ≫ 𝟙 a ◁ e =
      e' ▷ 𝟙 c ≫ (α_ u v (𝟙 c)).hom ≫ u ◁ (ρ_ v ≪≫ (λ_ v).symm).hom ≫ (α_ u (𝟙 b) v).inv ≫
        (ρ_ u ≪≫ (λ_ u).symm).hom ▷ v ≫ (α_ (𝟙 a) u v).hom := by
  subst he he'
  simp

/-- The naturality condition of the modification with components `ρ_ ≪≫ (λ_).symm` comparing
whiskerings by identity-component transformations. -/
private lemma unitors_naturality_iso {a b a' b' : B} (X : a ⟶ b) (Y : a' ⟶ b') (u : a ⟶ a')
    (v : b ⟶ b') (N : X ≫ v ≅ u ≫ Y) :
    X ◁ (ρ_ v ≪≫ (λ_ v).symm).hom ≫ ((α_ _ _ _).inv ≫ (ρ_ X ≪≫ (λ_ X).symm).hom ▷ v ≫
        (α_ _ _ _).hom ≫ 𝟙 a ◁ N.hom ≫ (α_ _ _ _).inv) =
      ((α_ _ _ _).inv ≫ N.hom ▷ 𝟙 b' ≫ (α_ _ _ _).hom ≫ u ◁ (ρ_ Y ≪≫ (λ_ Y).symm).hom ≫
        (α_ _ _ _).inv) ≫ (ρ_ u ≪≫ (λ_ u).symm).hom ▷ Y := by
  simp

/-- The naturality condition of the modification `𝟙 ≅ τ ≫ σ` with components `(λ_ (𝟙 _)).symm`,
for identity-component transformations `τ` and `σ`. -/
private lemma unitors_naturality_unit {a b : B} (X : a ⟶ b) :
    X ◁ (λ_ (𝟙 b)).inv ≫ ((α_ _ _ _).inv ≫ (ρ_ X ≪≫ (λ_ X).symm).hom ▷ 𝟙 b ≫
        (α_ _ _ _).hom ≫ 𝟙 a ◁ (ρ_ X ≪≫ (λ_ X).symm).hom ≫ (α_ _ _ _).inv) =
      (ρ_ X ≪≫ (λ_ X).symm).hom ≫ (λ_ (𝟙 a)).inv ▷ X := by
  simp only [Iso.trans_hom, Iso.symm_hom]
  bicategory

/-- The naturality condition of the modification `σ ≫ τ ≅ 𝟙` with components `λ_ (𝟙 _)`, for
identity-component transformations `τ` and `σ`. -/
private lemma unitors_naturality_counit {a b : B} (X : a ⟶ b) :
    X ◁ (λ_ (𝟙 b)).hom ≫ (ρ_ X ≪≫ (λ_ X).symm).hom =
      ((α_ _ _ _).inv ≫ (ρ_ X ≪≫ (λ_ X).symm).hom ▷ 𝟙 b ≫
        (α_ _ _ _).hom ≫ 𝟙 a ◁ (ρ_ X ≪≫ (λ_ X).symm).hom ≫ (α_ _ _ _).inv) ≫
        (λ_ (𝟙 a)).hom ▷ X := by
  simp

end Aux

variable {B : Type u₃} [Bicategory.{w₃, v₃} B] {Γ : Type u₁} [Category.{v₁} Γ]
  {Λ : Type u₂} [Category.{v₂} Λ] {Λ' : Type u₄} [Category.{v₄} Λ']

/-! ### Pulling back along the identity functor -/

/-- The strong transformation `(𝟭 Γ).toPseudofunctor.comp F ⟶ F` with identity components and
naturality isomorphisms given by the unitors. -/
-- The body is exposed so that the components and naturality isomorphisms of this transformation
-- can be stated by `simps`, and unfolded in the naturality conditions of the transformations
-- between precomposition pseudofunctors below.
@[expose, simps]
def pullbackIdHom (F : LocallyDiscrete Γ ⥤ᵖ B) : (𝟭 Γ).toPseudofunctor.comp F ⟶ F where
  app x := 𝟙 (F.obj x)
  naturality φ := ρ_ (F.map φ) ≪≫ (λ_ (F.map φ)).symm
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    rw [Subsingleton.elim η (𝟙 _), PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]
    -- The two sides mention `F.map φ` and the definitionally equal image of `φ` under the
    -- pullback, so the identity is applied by unification.
    exact (by simp : ∀ {a b : B} (X : a ⟶ b),
      𝟙 X ▷ 𝟙 b ≫ (ρ_ X ≪≫ (λ_ X).symm).hom = (ρ_ X ≪≫ (λ_ X).symm).hom ≫ 𝟙 a ◁ 𝟙 X) _
  -- After identifying the unit and composition comparisons of the pullback with those of `F`,
  -- the conditions are those of the identity transformation of `F`.
  naturality_id x := by
    rw [toPseudofunctor_id_comp_mapId]
    exact (StrongTrans.id F).naturality_id x
  naturality_comp φ ψ := by
    rw [toPseudofunctor_id_comp_mapComp]
    exact (StrongTrans.id F).naturality_comp φ ψ

/-- The strong transformation `F ⟶ (𝟭 Γ).toPseudofunctor.comp F` with identity components and
naturality isomorphisms given by the unitors. -/
-- The body is exposed so that the components and naturality isomorphisms of this transformation
-- can be stated by `simps`, and unfolded in the naturality conditions of the transformations
-- between precomposition pseudofunctors below.
@[expose, simps]
def pullbackIdInv (F : LocallyDiscrete Γ ⥤ᵖ B) : F ⟶ (𝟭 Γ).toPseudofunctor.comp F where
  app x := 𝟙 (F.obj x)
  naturality φ := ρ_ (F.map φ) ≪≫ (λ_ (F.map φ)).symm
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    rw [Subsingleton.elim η (𝟙 _), PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]
    -- The two sides mention `F.map φ` and the definitionally equal image of `φ` under the
    -- pullback, so the identity is applied by unification.
    exact (by simp : ∀ {a b : B} (X : a ⟶ b),
      𝟙 X ▷ 𝟙 b ≫ (ρ_ X ≪≫ (λ_ X).symm).hom = (ρ_ X ≪≫ (λ_ X).symm).hom ≫ 𝟙 a ◁ 𝟙 X) _
  -- As in `pullbackIdHom`.
  naturality_id x := by
    rw [toPseudofunctor_id_comp_mapId]
    exact (StrongTrans.id F).naturality_id x
  naturality_comp φ ψ := by
    rw [toPseudofunctor_id_comp_mapComp]
    exact (StrongTrans.id F).naturality_comp φ ψ

variable (B Γ) in
/-- The strong transformation `precomp B (𝟭 Γ).toPseudofunctor ⟶ Pseudofunctor.id _` with
components `F.pullbackIdHom`. Its naturality isomorphisms are given by the unitors. -/
def precompIdHom :
    precomp B (𝟭 Γ).toPseudofunctor ⟶ Pseudofunctor.id (LocallyDiscrete Γ ⥤ᵖ B) where
  app F := pullbackIdHom F
  naturality {F G} η := isoMk (fun x => ρ_ (η.app x) ≪≫ (λ_ (η.app x)).symm)
    (fun φ => unitors_naturality_iso _ _ _ _ (η.naturality φ))
  naturality_naturality Θ := by
    ext x
    exact unitors_naturality_whisker (Θ.as.app x)
  naturality_id F := by
    ext x
    exact unitors_naturality_id _ _ rfl (whiskerLeftId_hom_as_app _ _ _)
  naturality_comp η θ := by
    ext x
    exact unitors_naturality_comp _ _ _ _ rfl (whiskerLeftComp_hom_as_app _ _ _ _)

@[simp]
lemma precompIdHom_app (F : LocallyDiscrete Γ ⥤ᵖ B) :
    (precompIdHom B Γ).app F = F.pullbackIdHom :=
  (rfl)

variable (B Γ) in
/-- The strong transformation `Pseudofunctor.id _ ⟶ precomp B (𝟭 Γ).toPseudofunctor` with
components `F.pullbackIdInv`. Its naturality isomorphisms are given by the unitors. -/
def precompIdInv :
    Pseudofunctor.id (LocallyDiscrete Γ ⥤ᵖ B) ⟶ precomp B (𝟭 Γ).toPseudofunctor where
  app F := pullbackIdInv F
  naturality {F G} η := isoMk (fun x => ρ_ (η.app x) ≪≫ (λ_ (η.app x)).symm)
    (fun φ => unitors_naturality_iso _ _ _ _ (η.naturality φ))
  naturality_naturality Θ := by
    ext x
    exact unitors_naturality_whisker (Θ.as.app x)
  naturality_id F := by
    ext x
    exact unitors_naturality_id _ _ (whiskerLeftId_hom_as_app _ _ _) rfl
  naturality_comp η θ := by
    ext x
    exact unitors_naturality_comp _ _ _ _ (whiskerLeftComp_hom_as_app _ _ _ _) rfl

@[simp]
lemma precompIdInv_app (F : LocallyDiscrete Γ ⥤ᵖ B) :
    (precompIdInv B Γ).app F = F.pullbackIdInv :=
  (rfl)

variable (B Γ) in
/-- Pulling back along the identity functor is equivalent to the identity pseudofunctor of the
bicategory of families indexed by `Γ`, through `precompIdHom` and `precompIdInv`. The unit and
counit have components the unitors `λ_ (𝟙 (F.obj x))`. -/
def precompIdEquiv :
    Bicategory.Equivalence (precomp B (𝟭 Γ).toPseudofunctor)
      (Pseudofunctor.id (LocallyDiscrete Γ ⥤ᵖ B)) :=
  Equivalence.mkOfAdjointifyCounit (f := precompIdHom B Γ) (g := precompIdInv B Γ)
    (StrongTrans.isoMk (fun (F : LocallyDiscrete Γ ⥤ᵖ B) =>
      StrongTrans.isoMk (fun (x : LocallyDiscrete Γ) => (λ_ (𝟙 (F.obj x))).symm)
      (fun φ => unitors_naturality_unit _))
      (fun η => by
        ext x
        exact unitors_naturality_unit (η.app x)))
    (StrongTrans.isoMk (fun (F : LocallyDiscrete Γ ⥤ᵖ B) =>
      StrongTrans.isoMk (fun (x : LocallyDiscrete Γ) => λ_ (𝟙 (F.obj x)))
      (fun φ => unitors_naturality_counit _))
      (fun η => by
        ext x
        exact unitors_naturality_counit (η.app x)))

@[simp]
lemma precompIdEquiv_hom : (precompIdEquiv B Γ).hom = precompIdHom B Γ :=
  (rfl)

@[simp]
lemma precompIdEquiv_inv : (precompIdEquiv B Γ).inv = precompIdInv B Γ :=
  (rfl)

/-! ### Pulling back along a composite functor -/

/-- The strong transformation from the pullback along `f ⋙ g` to the pullback along `g` and then
along `f`, with identity components and naturality isomorphisms given by the unitors. -/
-- The body is exposed so that the components and naturality isomorphisms of this transformation
-- can be stated by `simps`, and unfolded in the naturality conditions of the transformations
-- between precomposition pseudofunctors below.
@[expose, simps]
def pullbackCompHom (f : Γ ⥤ Λ) (g : Λ ⥤ Λ') (F : LocallyDiscrete Λ' ⥤ᵖ B) :
    (f ⋙ g).toPseudofunctor.comp F ⟶ f.toPseudofunctor.comp (g.toPseudofunctor.comp F) where
  app x := 𝟙 (F.obj ⟨g.obj (f.obj x.as)⟩)
  naturality φ := ρ_ (F.map (g.map (f.map φ.as)).toLoc) ≪≫ (λ_ _).symm
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    rw [Subsingleton.elim η (𝟙 _), PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]
    -- The two sides mention `F.map φ` and the definitionally equal image of `φ` under the
    -- pullback, so the identity is applied by unification.
    exact (by simp : ∀ {a b : B} (X : a ⟶ b),
      𝟙 X ▷ 𝟙 b ≫ (ρ_ X ≪≫ (λ_ X).symm).hom = (ρ_ X ≪≫ (λ_ X).symm).hom ≫ 𝟙 a ◁ 𝟙 X) _
  -- After identifying the unit and composition comparisons of the two pullbacks, the conditions
  -- are those of the identity transformation of the pullback along `f ⋙ g`.
  naturality_id x := by
    rw [← toPseudofunctor_comp_comp_mapId]
    exact (StrongTrans.id ((f ⋙ g).toPseudofunctor.comp F)).naturality_id x
  naturality_comp φ ψ := by
    rw [← toPseudofunctor_comp_comp_mapComp]
    exact (StrongTrans.id ((f ⋙ g).toPseudofunctor.comp F)).naturality_comp φ ψ

/-- The strong transformation from the pullback along `g` and then along `f` to the pullback
along `f ⋙ g`, with identity components and naturality isomorphisms given by the unitors. -/
-- The body is exposed so that the components and naturality isomorphisms of this transformation
-- can be stated by `simps`, and unfolded in the naturality conditions of the transformations
-- between precomposition pseudofunctors below.
@[expose, simps]
def pullbackCompInv (f : Γ ⥤ Λ) (g : Λ ⥤ Λ') (F : LocallyDiscrete Λ' ⥤ᵖ B) :
    f.toPseudofunctor.comp (g.toPseudofunctor.comp F) ⟶ (f ⋙ g).toPseudofunctor.comp F where
  app x := 𝟙 (F.obj ⟨g.obj (f.obj x.as)⟩)
  naturality φ := ρ_ (F.map (g.map (f.map φ.as)).toLoc) ≪≫ (λ_ _).symm
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    rw [Subsingleton.elim η (𝟙 _), PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]
    -- The two sides mention `F.map φ` and the definitionally equal image of `φ` under the
    -- pullback, so the identity is applied by unification.
    exact (by simp : ∀ {a b : B} (X : a ⟶ b),
      𝟙 X ▷ 𝟙 b ≫ (ρ_ X ≪≫ (λ_ X).symm).hom = (ρ_ X ≪≫ (λ_ X).symm).hom ≫ 𝟙 a ◁ 𝟙 X) _
  -- As in `pullbackCompHom`, with the roles of the two pullbacks exchanged.
  naturality_id x := by
    rw [toPseudofunctor_comp_comp_mapId]
    exact (StrongTrans.id (f.toPseudofunctor.comp (g.toPseudofunctor.comp F))).naturality_id x
  naturality_comp φ ψ := by
    rw [toPseudofunctor_comp_comp_mapComp]
    exact (StrongTrans.id
      (f.toPseudofunctor.comp (g.toPseudofunctor.comp F))).naturality_comp φ ψ

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
def precompCompHom (f : Γ ⥤ Λ) (g : Λ ⥤ Λ') :
    precomp B (f ⋙ g).toPseudofunctor ⟶
      (precomp B g.toPseudofunctor).comp (precomp B f.toPseudofunctor) where
  app F := pullbackCompHom f g F
  naturality {F G} η := isoMk (fun x => ρ_ (η.app ⟨g.obj (f.obj x.as)⟩) ≪≫ (λ_ _).symm)
    (fun φ => unitors_naturality_iso _ _ _ _ (η.naturality _))
  naturality_naturality Θ := by
    ext x
    exact unitors_naturality_whisker (Θ.as.app _)
  naturality_id F := by
    ext x
    exact unitors_naturality_id _ _ (precomp_comp_mapId_hom_as_app f g F x)
      (whiskerLeftId_hom_as_app _ _ _)
  naturality_comp η θ := by
    ext x
    exact unitors_naturality_comp _ _ _ _ (precomp_comp_mapComp_hom_as_app f g η θ x)
      (whiskerLeftComp_hom_as_app _ _ _ _)

@[simp]
lemma precompCompHom_app (f : Γ ⥤ Λ) (g : Λ ⥤ Λ') (F : LocallyDiscrete Λ' ⥤ᵖ B) :
    (precompCompHom B f g).app F = F.pullbackCompHom f g :=
  (rfl)

variable (B) in
/-- The strong transformation from the composite of pulling back along `g` and along `f` to
pulling back along `f ⋙ g`, with components `F.pullbackCompInv f g`. Its naturality
isomorphisms are given by the unitors. -/
def precompCompInv (f : Γ ⥤ Λ) (g : Λ ⥤ Λ') :
    (precomp B g.toPseudofunctor).comp (precomp B f.toPseudofunctor) ⟶
      precomp B (f ⋙ g).toPseudofunctor where
  app F := pullbackCompInv f g F
  naturality {F G} η := isoMk (fun x => ρ_ (η.app ⟨g.obj (f.obj x.as)⟩) ≪≫ (λ_ _).symm)
    (fun φ => unitors_naturality_iso _ _ _ _ (η.naturality _))
  naturality_naturality Θ := by
    ext x
    exact unitors_naturality_whisker (Θ.as.app _)
  naturality_id F := by
    ext x
    exact unitors_naturality_id _ _ (whiskerLeftId_hom_as_app _ _ _)
      (precomp_comp_mapId_hom_as_app f g F x)
  naturality_comp η θ := by
    ext x
    exact unitors_naturality_comp _ _ _ _ (whiskerLeftComp_hom_as_app _ _ _ _)
      (precomp_comp_mapComp_hom_as_app f g η θ x)

@[simp]
lemma precompCompInv_app (f : Γ ⥤ Λ) (g : Λ ⥤ Λ') (F : LocallyDiscrete Λ' ⥤ᵖ B) :
    (precompCompInv B f g).app F = F.pullbackCompInv f g :=
  (rfl)

variable (B) in
/-- Pulling back along a composite functor `f ⋙ g` is equivalent to pulling back along `g` and
then along `f`, through `precompCompHom` and `precompCompInv`. The unit and counit have
components the unitors. -/
def precompCompEquiv (f : Γ ⥤ Λ) (g : Λ ⥤ Λ') :
    Bicategory.Equivalence (precomp B (f ⋙ g).toPseudofunctor)
      ((precomp B g.toPseudofunctor).comp (precomp B f.toPseudofunctor)) :=
  Equivalence.mkOfAdjointifyCounit (f := precompCompHom B f g) (g := precompCompInv B f g)
    (StrongTrans.isoMk (fun (F : LocallyDiscrete Λ' ⥤ᵖ B) =>
      StrongTrans.isoMk (fun (x : LocallyDiscrete Γ) =>
        (λ_ (𝟙 (F.obj ⟨g.obj (f.obj x.as)⟩))).symm)
      (fun φ => unitors_naturality_unit _))
      (fun η => by
        ext x
        exact unitors_naturality_unit (η.app _)))
    (StrongTrans.isoMk (fun (F : LocallyDiscrete Λ' ⥤ᵖ B) =>
      StrongTrans.isoMk (fun (x : LocallyDiscrete Γ) => λ_ (𝟙 (F.obj ⟨g.obj (f.obj x.as)⟩)))
      (fun φ => unitors_naturality_counit _))
      (fun η => by
        ext x
        exact unitors_naturality_counit (η.app _)))

@[simp]
lemma precompCompEquiv_hom (f : Γ ⥤ Λ) (g : Λ ⥤ Λ') :
    (precompCompEquiv B f g).hom = precompCompHom B f g :=
  (rfl)

@[simp]
lemma precompCompEquiv_inv (f : Γ ⥤ Λ) (g : Λ ⥤ Λ') :
    (precompCompEquiv B f g).inv = precompCompInv B f g :=
  (rfl)

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
    Biequivalence (LocallyDiscrete Γ ⥤ᵖ B) (LocallyDiscrete Λ ⥤ᵖ B) where
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
