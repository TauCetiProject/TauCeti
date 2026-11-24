/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Normalized
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Cat
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import TauCeti.CategoryTheory.Groupoid.SingleObj

/-!
# Transport of an equivariant lift as a family of equivariant functors

Let `N : NormalizedTransport Γ actions` be normalized transport data for a family of categorical
actions `actions p : LocallyDiscrete (SingleObj H) ⥤ᵖ Cat` of a monoid `H`, indexed by a category
`Γ`. Its transport functors `E_g : C p ⥤ C q` come with isomorphisms
`T_a ⋙ E_g ≅ E_g ⋙ T_a` commuting them with the actions. This file packages these as equivariant
functors between the prescribed actions, coherently in `g`:

* `N.transportStrongTrans g : actions p ⟶ actions q` is the strong transformation with component
  `E_g` and naturality isomorphisms `N.transportCommIso g a`. Its unit and composition conditions
  are the mixed coherence conditions `transportCommIso_actId` and `transportCommIso_actComp` of `N`.
* `N.transportStrongTransId p` and `N.transportStrongTransComp g h gh hgh` are the invertible
  modifications `E_(𝟙 p) ≅ 𝟙` and `E_gh ≅ E_g ≫ E_h` given by the unit and composition
  isomorphisms of transport. That they are modifications, that is, compatible with the actions,
  is the content of `transportCommIso_id` and `transportCommIso_comp`.
* `N.equivariantTransport : LocallyDiscrete Γ ⥤ᵖ (LocallyDiscrete (SingleObj H) ⥤ᵖ Cat)` is the
  resulting pseudofunctor into the bicategory of pseudofunctors, strong transformations and
  modifications. It sends `p` to the prescribed action `actions p` itself and `g` to
  `N.transportStrongTrans g`. Its coherence is the associativity and unitality of the
  composition isomorphisms of transport.

Thus normalized transport data, which are equivalent to equivariant lifts by
`TauCeti.EquivariantGroupoidLift.normalizationBiequivalence`, give a coherent transport of the
prescribed `H`-categories along `Γ` by equivariant functors: a curried form of the joint
pseudofunctor on `Γ × SingleObj H`, with values the prescribed actions rather than the fibers of
the joint pseudofunctor.

For an isomorphism `g : p ≅ q` of `Γ`, `N.equivariantTransportEquivalence g` is an equivalence
`actions p ≌ actions q` in the bicategory of pseudofunctors, with inverse
`N.transportStrongTrans g.inv`: an equivariant equivalence between the prescribed actions at `p`
and at `q`. For a lift `L`, it is applied to `L.normalizedTransport`. When a lift is reindexed
along a functor `ψ : Λ ⥤ Γ`, for instance a quasi-inverse of an equivalence of parameter
groupoids in the descent of families of local categories, the prescribed actions `actions (ψ l)`
and `actions (ψ' l)` of two isomorphic reindexings `α : ψ ≅ ψ'` are compared by these
equivalences along `α.app l`.

Restricting `N.equivariantTransport` along the inclusion `SingleObj (End p) ⥤ Γ` gives
`N.equivariantEndAction p`: the endomorphism monoid of `p`, and so for a groupoid `Γ` the
isotropy group of `p`, acts on the categorical action `actions p` by equivariant transport.

## Main definitions

* `TauCeti.EquivariantGroupoidLift.NormalizedTransport.transportStrongTrans`: transport along an
  arrow of `Γ` as a strong transformation between the prescribed actions;
* `TauCeti.EquivariantGroupoidLift.NormalizedTransport.equivariantTransport`: the pseudofunctor
  from `Γ` to the bicategory of `H`-actions given by transport;
* `TauCeti.EquivariantGroupoidLift.NormalizedTransport.equivariantTransportEquivalence`: transport
  along an isomorphism of `Γ` as an equivalence of the prescribed actions;
* `TauCeti.EquivariantGroupoidLift.NormalizedTransport.equivariantEndAction`: the action of the
  endomorphism monoid of `p` on the prescribed action `actions p` by equivariant transport.

## References

* Edward Frenkel,
  [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  Cambridge Studies in Advanced Mathematics 103 (2007), §1.3: families of local categories over
  the groupoid of local Langlands parameters, with their loop group actions.
* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055), Chapter 4: pseudofunctors, strong
  transformations and modifications.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory Pseudofunctor.StrongTrans

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}

namespace NormalizedTransport

variable (N : NormalizedTransport Γ actions)

/-- Transport along `g : p ⟶ q` as an equivariant functor: the strong transformation
`actions p ⟶ actions q` with component `E_g` and naturality isomorphisms
`T_a ⋙ E_g ≅ E_g ⋙ T_a` given by `N.transportCommIso g a`. -/
-- The body is exposed so that its component and naturality isomorphisms are definitionally
-- `E_g` and `N.transportCommIso g a`: the statements of the component lemmas below, and of those
-- of `transportStrongTransId` and `transportStrongTransComp`, only typecheck with this unfolding.
@[expose] noncomputable def transportStrongTrans {p q : Γ} (g : p ⟶ q) :
    actions p ⟶ actions q where
  app _ := (N.transport g).toCatHom
  naturality f := Cat.Hom.isoMk (N.transportCommIso g f.as)
  naturality_naturality η :=
    Pseudofunctor.naturality_naturality_of_locallyDiscrete (actions p) (actions q)
      (fun _ ↦ (N.transport g).toCatHom) (fun f ↦ Cat.Hom.isoMk (N.transportCommIso g f.as)) η
  naturality_id a := by
    obtain rfl : a = ⟨SingleObj.star H⟩ := rfl
    ext X
    -- This is `transportCommIso_actId`, with the unit comparisons of the actions written as
    -- `mapId`.
    have := N.transportCommIso_actId g X
    have e : ∀ r, (actions r).mapId' (𝟙 (SingleObj.star H)).toLoc rfl =
        (actions r).mapId ⟨SingleObj.star H⟩ := fun r ↦ (actions r).mapId'_eq_mapId _
    rw [actId_hom_app, actId_hom_app, e, e] at this
    simp only [Cat.Hom.comp_toFunctor, Functor.toCatHom_toFunctor, Functor.comp_obj,
      Cat.Hom.id_toFunctor, Functor.id_obj, LocallyDiscrete.id_as, Cat.Hom.toNatTrans_comp,
      Cat.whiskerLeft_toNatTrans, NatTrans.comp_app, Functor.whiskerLeft_app,
      Cat.whiskerRight_toNatTrans, Cat.leftUnitor_hom_toNatTrans, Cat.rightUnitor_inv_toNatTrans,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
      Category.comp_id]
    exact this
  naturality_comp {a b c} f f' := by
    obtain rfl : a = ⟨SingleObj.star H⟩ := rfl
    obtain rfl : b = ⟨SingleObj.star H⟩ := rfl
    obtain rfl : c = ⟨SingleObj.star H⟩ := rfl
    ext X
    -- This is `transportCommIso_actComp`, with the composition comparisons of the actions written
    -- as `mapComp`.
    have := N.transportCommIso_actComp g f.as f'.as (f ≫ f').as rfl X
    rw [actComp_hom_app_eq_mapComp, actComp_hom_app_eq_mapComp] at this
    simp only [Cat.Hom.comp_toFunctor, Functor.toCatHom_toFunctor, Functor.comp_obj,
      LocallyDiscrete.comp_as, Cat.Hom.toNatTrans_comp, Cat.whiskerLeft_toNatTrans,
      NatTrans.comp_app, Functor.whiskerLeft_app, Cat.whiskerRight_toNatTrans,
      Cat.associator_hom_toNatTrans, Cat.associator_inv_toNatTrans, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id, Category.id_comp]
    exact this.symm

@[simp]
lemma transportStrongTrans_app {p q : Γ} (g : p ⟶ q) (a : LocallyDiscrete (SingleObj H)) :
    (N.transportStrongTrans g).app a = (N.transport g).toCatHom :=
  rfl

@[simp]
lemma transportStrongTrans_naturality_hom_app {p q : Γ} (g : p ⟶ q)
    {a b : LocallyDiscrete (SingleObj H)} (f : a ⟶ b) (X : fiber actions p) :
    ((N.transportStrongTrans g).naturality f).hom.toNatTrans.app X =
      (N.transportCommIso g f.as).hom.app X :=
  rfl

@[simp]
lemma transportStrongTrans_naturality_inv_app {p q : Γ} (g : p ⟶ q)
    {a b : LocallyDiscrete (SingleObj H)} (f : a ⟶ b) (X : fiber actions p) :
    ((N.transportStrongTrans g).naturality f).inv.toNatTrans.app X =
      (N.transportCommIso g f.as).inv.app X :=
  rfl

/-- The unit isomorphism `E_(𝟙 p) ≅ 𝟭` of transport, as an invertible modification
`N.transportStrongTrans (𝟙 p) ≅ 𝟙 (actions p)`. Its compatibility with the actions is
`transportCommIso_id`. -/
noncomputable def transportStrongTransId (p : Γ) :
    N.transportStrongTrans (𝟙 p) ≅ 𝟙 (actions p) :=
  isoMk (fun _ ↦ Cat.Hom.isoMk (N.transportId p)) (fun {a b} f ↦ by
    obtain rfl : a = ⟨SingleObj.star H⟩ := rfl
    obtain rfl : b = ⟨SingleObj.star H⟩ := rfl
    ext X
    rw [Cat.Hom₂.comp_app, Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app]
    -- The components of the unitors of `Cat` and of `Cat.Hom.isoMk` are definitionally identities
    -- and the given natural transformations, but the objects of the goal are only definitionally
    -- those of `fiber actions p`, so the component lemmas do not apply by rewriting.
    change (N.transportId p).hom.app ((act actions p f.as).obj X) ≫ (𝟙 _ ≫ 𝟙 _) =
      (N.transportCommIso (𝟙 p) f.as).hom.app X ≫
        (act actions p f.as).map ((N.transportId p).hom.app X)
    rw [Category.comp_id, Category.comp_id, N.transportCommIso_id])

/-- The composition isomorphism `E_g ⋙ E_h ≅ E_gh` of transport, inverted, as an invertible
modification `N.transportStrongTrans gh ≅ N.transportStrongTrans g ≫ N.transportStrongTrans h`
for `g ≫ h = gh`. Its compatibility with the actions is `transportCommIso_comp`. -/
noncomputable def transportStrongTransComp {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r)
    (gh : p ⟶ r) (hgh : g ≫ h = gh) :
    N.transportStrongTrans gh ≅ N.transportStrongTrans g ≫ N.transportStrongTrans h :=
  isoMk (fun _ ↦ Cat.Hom.isoMk (N.transportComp g h gh hgh).symm) (fun {a b} f ↦ by
    obtain rfl : a = ⟨SingleObj.star H⟩ := rfl
    obtain rfl : b = ⟨SingleObj.star H⟩ := rfl
    ext X
    rw [Cat.Hom₂.comp_app, Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Pseudofunctor.StrongTrans.comp_naturality_hom_app]
    -- As for `transportStrongTransId`: the components of `Cat.Hom.isoMk` are definitionally the
    -- given natural transformations, on objects only definitionally those of the fibers.
    change (N.transportComp g h gh hgh).inv.app ((act actions p f.as).obj X) ≫
        (N.transport h).map ((N.transportCommIso g f.as).hom.app X) ≫
          (N.transportCommIso h f.as).hom.app ((N.transport g).obj X) =
      (N.transportCommIso gh f.as).hom.app X ≫
        (act actions r f.as).map ((N.transportComp g h gh hgh).inv.app X)
    rw [← cancel_epi ((N.transportComp g h gh hgh).hom.app _), Iso.hom_inv_id_app_assoc,
      ← N.transportCommIso_comp_assoc g h gh hgh f.as X, ← Functor.map_comp,
      Iso.hom_inv_id_app]
    -- The remaining identity morphisms are typed through the category instance of the fibers,
    -- not the instance of `(actions r).obj a` that the composites use, so `Functor.map_id` and
    -- `Category.comp_id` do not rewrite them; we restate the first and apply the second by
    -- `congrArg`.
    rw [show (act actions r f.as).map (𝟙 ((N.transport g ⋙ N.transport h).obj X)) = 𝟙 _ from
      (act actions r f.as).map_id _]
    exact (congrArg (_ ≫ ·) (Category.comp_id _)).symm)

@[simp]
lemma transportStrongTransId_hom_as_app_toNatTrans_app (p : Γ)
    (a : LocallyDiscrete (SingleObj H)) (X : fiber actions p) :
    ((N.transportStrongTransId p).hom.as.app a).toNatTrans.app X = (N.transportId p).hom.app X :=
  (rfl)

@[simp]
lemma transportStrongTransId_inv_as_app_toNatTrans_app (p : Γ)
    (a : LocallyDiscrete (SingleObj H)) (X : fiber actions p) :
    ((N.transportStrongTransId p).inv.as.app a).toNatTrans.app X = (N.transportId p).inv.app X :=
  (rfl)

@[simp]
lemma transportStrongTransComp_hom_as_app_toNatTrans_app {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r)
    (gh : p ⟶ r) (hgh : g ≫ h = gh) (a : LocallyDiscrete (SingleObj H)) (X : fiber actions p) :
    ((N.transportStrongTransComp g h gh hgh).hom.as.app a).toNatTrans.app X =
      (N.transportComp g h gh hgh).inv.app X :=
  (rfl)

@[simp]
lemma transportStrongTransComp_inv_as_app_toNatTrans_app {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r)
    (gh : p ⟶ r) (hgh : g ≫ h = gh) (a : LocallyDiscrete (SingleObj H)) (X : fiber actions p) :
    ((N.transportStrongTransComp g h gh hgh).inv.as.app a).toNatTrans.app X =
      (N.transportComp g h gh hgh).hom.app X :=
  (rfl)

/-- Transport as a pseudofunctor from `Γ` to the bicategory of actions of `H` on categories: it
sends `p` to the prescribed action `actions p`, an arrow `g` to the equivariant functor
`N.transportStrongTrans g`, and its unit and composition comparisons are
`N.transportStrongTransId` and `N.transportStrongTransComp`. -/
-- The body is exposed so that its values and comparisons are definitionally those of
-- `transportStrongTrans`, `transportStrongTransId` and `transportStrongTransComp`: the statements
-- of `equivariantTransport_map`, `_mapId` and `_mapComp` only typecheck with this unfolding.
@[expose] noncomputable def equivariantTransport :
    LocallyDiscrete Γ ⥤ᵖ (LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}) :=
  LocallyDiscrete.mkPseudofunctor actions N.transportStrongTrans N.transportStrongTransId
    (fun g h ↦ N.transportStrongTransComp g h _ rfl)
    (fun f g h ↦ by
      ext a X
      obtain rfl : a = ⟨SingleObj.star H⟩ := rfl
      rw [Pseudofunctor.StrongTrans.eqToHom_as_app, Cat.eqToHom_app]
      -- Componentwise, the whiskerings of modifications are whiskerings in `Cat`, whose
      -- components are definitionally the stated ones, and the associator contributes an
      -- identity. The objects are only definitionally those of the fibers, so we use `change`.
      change (N.transportComp (f ≫ g) h _ rfl).inv.app X ≫
          ((N.transport h).map ((N.transportComp f g _ rfl).inv.app X) ≫
            (𝟙 _ ≫ ((N.transportComp g h _ rfl).hom.app ((N.transport f).obj X) ≫
              (N.transportComp f (g ≫ h) _ rfl).hom.app X))) = _
      rw [Category.id_comp]
      exact LocallyDiscrete.mapComp_associativity_eqToHom (obj := fun p ↦ fiber actions p)
        N.transport (fun g h gh hgh ↦ (N.transportComp g h gh hgh).symm)
        N.transportComp_inv_associativity f g h _ _ _ _ rfl rfl rfl rfl X _)
    (fun f ↦ by
      ext a X
      obtain rfl : a = ⟨SingleObj.star H⟩ := rfl
      rw [Pseudofunctor.StrongTrans.eqToHom_as_app, Cat.eqToHom_app]
      -- As for associativity; the left unitor of `Cat` contributes an identity, which is typed
      -- through the category instance of the fibers and so is removed by `congrArg`.
      change (N.transportComp (𝟙 _) f _ rfl).inv.app X ≫
          ((N.transport f).map ((N.transportId _).hom.app X) ≫ 𝟙 _) = _
      exact (congrArg (_ ≫ ·) (Category.comp_id _)).trans
        (LocallyDiscrete.mapComp_left_unitality_eqToHom (obj := fun p ↦ fiber actions p)
          N.transport N.transportId (fun g h gh hgh ↦ (N.transportComp g h gh hgh).symm)
          N.transportComp_inv_left_unitality f _ rfl X _))
    (fun f ↦ by
      ext a X
      obtain rfl : a = ⟨SingleObj.star H⟩ := rfl
      rw [Pseudofunctor.StrongTrans.eqToHom_as_app, Cat.eqToHom_app]
      -- As for associativity; the right unitor of `Cat` contributes an identity, which is typed
      -- through the category instance of the fibers and so is removed by `congrArg`.
      change (N.transportComp f (𝟙 _) _ rfl).inv.app X ≫
          ((N.transportId _).hom.app ((N.transport f).obj X) ≫ 𝟙 _) = _
      exact (congrArg (_ ≫ ·) (Category.comp_id _)).trans
        (LocallyDiscrete.mapComp_right_unitality_eqToHom (obj := fun p ↦ fiber actions p)
          N.transport N.transportId (fun g h gh hgh ↦ (N.transportComp g h gh hgh).symm)
          N.transportComp_inv_right_unitality f _ rfl X _))

@[simp]
lemma equivariantTransport_obj (b : LocallyDiscrete Γ) :
    N.equivariantTransport.obj b = actions b.as :=
  rfl

@[simp]
lemma equivariantTransport_map {b b' : LocallyDiscrete Γ} (g : b ⟶ b') :
    N.equivariantTransport.map g = N.transportStrongTrans g.as :=
  rfl

@[simp]
lemma equivariantTransport_mapId (b : LocallyDiscrete Γ) :
    N.equivariantTransport.mapId b = N.transportStrongTransId b.as :=
  rfl

@[simp]
lemma equivariantTransport_mapComp {b₀ b₁ b₂ : LocallyDiscrete Γ} (g : b₀ ⟶ b₁) (h : b₁ ⟶ b₂) :
    N.equivariantTransport.mapComp g h = N.transportStrongTransComp g.as h.as (g ≫ h).as rfl :=
  rfl

/-- Transport along an isomorphism `g : p ≅ q` of `Γ`, as an equivalence `actions p ≌ actions q`
in the bicategory of pseudofunctors: an equivariant equivalence between the prescribed actions at
`p` and at `q`. Its strong transformations are `N.transportStrongTrans g.hom` and
`N.transportStrongTrans g.inv`, and its unit and counit are built from the modifications
`N.transportStrongTransId` and `N.transportStrongTransComp`. -/
-- The body is exposed so that the statements of the component lemmas below, which type its
-- unit and counit at the composites of `N.transportStrongTrans g.hom` and
-- `N.transportStrongTrans g.inv`, typecheck.
@[expose] noncomputable def equivariantTransportEquivalence {p q : Γ} (g : p ≅ q) :
    Bicategory.Equivalence (actions p) (actions q) where
  hom := N.transportStrongTrans g.hom
  inv := N.transportStrongTrans g.inv
  unit := (N.transportStrongTransId p).symm ≪≫
    N.transportStrongTransComp g.hom g.inv (𝟙 p) g.hom_inv_id
  counit := (N.transportStrongTransComp g.inv g.hom (𝟙 q) g.inv_hom_id).symm ≪≫
    N.transportStrongTransId q
  left_triangle := by
    apply Iso.ext
    apply homCategory.ext
    intro a
    ext X
    simp only [comp_app, Cat.Hom.comp_toFunctor, Functor.comp_obj, leftZigzagIso_hom, leftZigzag,
      bicategoricalComp, Iso.trans_hom, Iso.symm_hom, comp_whiskerRight,
      BicategoricalCoherence.assoc_iso, BicategoricalCoherence.whiskerRight_iso,
      BicategoricalCoherence.refl_iso, whiskerRightIso_hom, Iso.refl_hom, whiskerRight_comp,
      id_whiskerRight, Category.id_comp, Iso.inv_hom_id, Category.comp_id, whiskerLeft_comp,
      Category.assoc, homCategory_comp_as_app, whiskerRight_as_app, associator_hom_as_app,
      whiskerLeft_as_app, Cat.Hom.toNatTrans_comp, Cat.whiskerRight_toNatTrans,
      Cat.associator_hom_toNatTrans, Cat.whiskerLeft_toNatTrans, NatTrans.comp_app,
      Functor.whiskerRight_app, transportStrongTransId_inv_as_app_toNatTrans_app,
      Functor.associator_hom_app, Functor.whiskerLeft_app,
      transportStrongTransId_hom_as_app_toNatTrans_app, leftUnitor_hom_as_app,
      rightUnitor_inv_as_app]
    -- The components of the whiskerings in `Cat` and of `Cat.Hom.isoMk`, and those of the unitors
    -- of `Cat`, are definitionally the stated ones, on objects only definitionally those of the
    -- fibers.
    change (N.transport g.hom).map ((N.transportId p).inv.app X) ≫
        (N.transport g.hom).map ((N.transportComp g.hom g.inv (𝟙 p) g.hom_inv_id).inv.app X) ≫
        (N.transportComp g.inv g.hom (𝟙 q) g.inv_hom_id).hom.app ((N.transport g.hom).obj X) ≫
          (N.transportId q).hom.app ((N.transport g.hom).obj X) = 𝟙 _ ≫ 𝟙 _
    -- The triangle identity follows from the associativity and unitality of `transportComp`.
    have h := N.transportComp_associativity g.hom g.inv g.hom (𝟙 p) (𝟙 q) g.hom
      g.hom_inv_id g.inv_hom_id (Category.id_comp _) (Category.comp_id _) X
    rw [N.transportComp_left_unitality, N.transportComp_right_unitality] at h
    rw [← h, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app_assoc,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.comp_id]

@[simp]
lemma equivariantTransportEquivalence_hom {p q : Γ} (g : p ≅ q) :
    (N.equivariantTransportEquivalence g).hom = N.transportStrongTrans g.hom :=
  rfl

@[simp]
lemma equivariantTransportEquivalence_inv {p q : Γ} (g : p ≅ q) :
    (N.equivariantTransportEquivalence g).inv = N.transportStrongTrans g.inv :=
  rfl

@[simp]
lemma equivariantTransportEquivalence_unit_hom_as_app_toNatTrans_app {p q : Γ} (g : p ≅ q)
    (a : LocallyDiscrete (SingleObj H)) (X : fiber actions p) :
    ((N.equivariantTransportEquivalence g).unit.hom.as.app a).toNatTrans.app X =
      (N.transportId p).inv.app X ≫ (N.transportComp g.hom g.inv (𝟙 p) g.hom_inv_id).inv.app X :=
  (rfl)

@[simp]
lemma equivariantTransportEquivalence_unit_inv_as_app_toNatTrans_app {p q : Γ} (g : p ≅ q)
    (a : LocallyDiscrete (SingleObj H)) (X : fiber actions p) :
    ((N.equivariantTransportEquivalence g).unit.inv.as.app a).toNatTrans.app X =
      (N.transportComp g.hom g.inv (𝟙 p) g.hom_inv_id).hom.app X ≫ (N.transportId p).hom.app X :=
  (rfl)

@[simp]
lemma equivariantTransportEquivalence_counit_hom_as_app_toNatTrans_app {p q : Γ} (g : p ≅ q)
    (a : LocallyDiscrete (SingleObj H)) (X : fiber actions q) :
    ((N.equivariantTransportEquivalence g).counit.hom.as.app a).toNatTrans.app X =
      (N.transportComp g.inv g.hom (𝟙 q) g.inv_hom_id).hom.app X ≫ (N.transportId q).hom.app X :=
  (rfl)

@[simp]
lemma equivariantTransportEquivalence_counit_inv_as_app_toNatTrans_app {p q : Γ} (g : p ≅ q)
    (a : LocallyDiscrete (SingleObj H)) (X : fiber actions q) :
    ((N.equivariantTransportEquivalence g).counit.inv.as.app a).toNatTrans.app X =
      (N.transportId q).inv.app X ≫ (N.transportComp g.inv g.hom (𝟙 q) g.inv_hom_id).inv.app X :=
  (rfl)

/-- The action of the endomorphism monoid `End p` on the prescribed categorical action
`actions p` by equivariant transport: the restriction of `N.equivariantTransport` along the
inclusion `Groupoid.singleObjFunctor p : SingleObj (End p) ⥤ Γ`. It sends `g` to the strong
transformation `N.transportStrongTrans g`, so `End p` acts on `C p` by functors commuting
coherently with the action of `H`. For a lift `L`, its component functors are those of
`L.endAction p`. -/
-- The body is exposed so that its values are definitionally `actions p` and its maps are
-- `N.transportStrongTrans`, as stated in the lemmas below.
@[expose] noncomputable def equivariantEndAction (p : Γ) :
    LocallyDiscrete (SingleObj (End p)) ⥤ᵖ (LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}) :=
  (Groupoid.singleObjFunctor p).toPseudofunctor.comp N.equivariantTransport

@[simp]
lemma equivariantEndAction_obj (p : Γ) (b : LocallyDiscrete (SingleObj (End p))) :
    (N.equivariantEndAction p).obj b = actions p :=
  rfl

@[simp]
lemma equivariantEndAction_map (p : Γ) {b b' : LocallyDiscrete (SingleObj (End p))}
    (g : b ⟶ b') : (N.equivariantEndAction p).map g = N.transportStrongTrans g.as.asHom :=
  rfl

@[simp]
lemma equivariantEndAction_mapId_hom_as_app_toNatTrans_app (p : Γ)
    (b : LocallyDiscrete (SingleObj (End p))) (a : LocallyDiscrete (SingleObj H))
    (X : fiber actions p) :
    (((N.equivariantEndAction p).mapId b).hom.as.app a).toNatTrans.app X =
      (N.transportId p).hom.app X :=
  Category.id_comp _

@[simp]
lemma equivariantEndAction_mapId_inv_as_app_toNatTrans_app (p : Γ)
    (b : LocallyDiscrete (SingleObj (End p))) (a : LocallyDiscrete (SingleObj H))
    (X : fiber actions p) :
    (((N.equivariantEndAction p).mapId b).inv.as.app a).toNatTrans.app X =
      (N.transportId p).inv.app X :=
  Category.comp_id _

@[simp]
lemma equivariantEndAction_mapComp_hom_as_app_toNatTrans_app (p : Γ)
    {b₀ b₁ b₂ : LocallyDiscrete (SingleObj (End p))} (g : b₀ ⟶ b₁) (h : b₁ ⟶ b₂)
    (a : LocallyDiscrete (SingleObj H)) (X : fiber actions p) :
    (((N.equivariantEndAction p).mapComp g h).hom.as.app a).toNatTrans.app X =
      (N.transportComp g.as.asHom h.as.asHom (g.as ≫ h.as).asHom rfl).inv.app X :=
  Category.id_comp _

@[simp]
lemma equivariantEndAction_mapComp_inv_as_app_toNatTrans_app (p : Γ)
    {b₀ b₁ b₂ : LocallyDiscrete (SingleObj (End p))} (g : b₀ ⟶ b₁) (h : b₁ ⟶ b₂)
    (a : LocallyDiscrete (SingleObj H)) (X : fiber actions p) :
    (((N.equivariantEndAction p).mapComp g h).inv.as.app a).toNatTrans.app X =
      (N.transportComp g.as.asHom h.as.asHom (g.as ≫ h.as).asHom rfl).hom.app X :=
  Category.comp_id _

end NormalizedTransport

end TauCeti.EquivariantGroupoidLift
