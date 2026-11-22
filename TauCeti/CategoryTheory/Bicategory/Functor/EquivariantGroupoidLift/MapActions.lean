/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Biequivalence
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Hom.Equivalence

/-!
# Changing the prescribed actions of an equivariant lift

Let `L : EquivariantGroupoidLift Γ actions` be a coherent equivariant lift along a category `Γ`
of a family of categorical actions `actions p : LocallyDiscrete (SingleObj H) ⥤ᵖ Cat` of a monoid
`H`, and let `φ p : actions p ⟶ actions' p` be strong transformations whose component functors
are equivalences of categories, that is, equivariant equivalences to a second family of actions.
Following each fiber comparison of `L` by `φ p` gives the lift `L.mapActions φ hφ` of `actions'`,
with the same joint pseudofunctor. Its transport functors on the new prescribed fibers are
intertwined with those of `L` by the components of `φ` (`mapActionsTransportIso`).

The construction applies to morphisms and compatible modifications of lifts without changing
their joint data, giving a pseudofunctor `mapActionsPseudofunctor` between the bicategories of
lifts; its coherence is automatic since the categories of morphisms of lifts are thin. Given
equivalences `e p : actions p ≌ actions' p` in the bicategory of pseudofunctors, the morphisms of
lifts with identity joint transformation whose fiber isomorphisms are built from the units and
counits of `e p` assemble into the unit and counit of a biequivalence
`mapActionsBiequivalence e` between the bicategories of lifts of `actions` and of `actions'`.

Reindexing a lift along two isomorphic functors `ψ ψ' : Λ ⥤ Γ`, as when descending a family of
local categories along two quasi-inverses of an equivalence of parameter groupoids, produces
lifts whose prescribed actions `actions (ψ l)` and `actions (ψ' l)` are related by equivariant
transport equivalences of the lift itself. Changing the prescribed actions along these
equivalences puts the two reindexed lifts in the same bicategory, where they can be compared.

## Main declarations

* `TauCeti.EquivariantGroupoidLift.mapActions`: following the fiber comparisons of a lift by
  equivariant equivalences;
* `TauCeti.EquivariantGroupoidLift.mapActionsTransportIso`: the intertwining
  `φ_p ⋙ E'_g ≅ E_g ⋙ φ_q` of the transport functors;
* `TauCeti.EquivariantGroupoidLift.mapActionsPseudofunctor`: the induced pseudofunctor between
  the bicategories of lifts;
* `TauCeti.EquivariantGroupoidLift.mapActionsUnitEquiv`,
  `TauCeti.EquivariantGroupoidLift.mapActionsCounitEquiv`: for isomorphisms `𝟙 ≅ φ ≫ ψ` and
  `ψ ≫ φ ≅ 𝟙`, the equivalences between the identity and the composite pseudofunctors;
* `TauCeti.EquivariantGroupoidLift.mapActionsBiequivalence`: the biequivalence induced by
  equivalences of the prescribed actions.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055): pseudofunctors, strong transformations,
  modifications and biequivalences.
* Edward Frenkel,
  [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  Cambridge Studies in Advanced Mathematics 103 (2007): families of local categories over the
  groupoid of local Langlands parameters, and their descent to local systems.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory CategoryTheory.Prod Pseudofunctor.StrongTrans

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions actions' : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}

/-- The lift of `actions'` with the joint pseudofunctor of `L` whose fiber comparison at `p` is
the fiber comparison of `L` followed by `φ p : actions p ⟶ actions' p`. -/
-- Exposed so that the joint pseudofunctor and fiber comparisons of `L.mapActions φ hφ` are
-- definitionally those of `L` and `L.comparison p ≫ φ p`, as the morphisms built on it require.
@[expose] noncomputable def mapActions (L : EquivariantGroupoidLift Γ actions)
    (φ : ∀ p, actions p ⟶ actions' p)
    (hφ : ∀ p, ((φ p).app ⟨SingleObj.star H⟩).toFunctor.IsEquivalence) :
    EquivariantGroupoidLift Γ actions' where
  joint := L.joint
  comparison p := L.comparison p ≫ φ p
  isEquivalence_comparison p := by
    have := L.isEquivalence_comparison p
    have := hφ p
    exact (inferInstance :
      (((L.comparison p).app ⟨SingleObj.star H⟩).toFunctor ⋙
        ((φ p).app ⟨SingleObj.star H⟩).toFunctor).IsEquivalence)

variable (L : EquivariantGroupoidLift Γ actions) (φ : ∀ p, actions p ⟶ actions' p)
  (hφ : ∀ p, ((φ p).app ⟨SingleObj.star H⟩).toFunctor.IsEquivalence)

@[simp]
lemma mapActions_joint : (L.mapActions φ hφ).joint = L.joint :=
  (rfl)

@[simp]
lemma mapActions_comparison (p : Γ) :
    (L.mapActions φ hφ).comparison p = L.comparison p ≫ φ p :=
  (rfl)

@[simp]
lemma mapActions_fiberEquivalence_functor (p : Γ) :
    ((L.mapActions φ hφ).fiberEquivalence p).functor =
      (L.fiberEquivalence p).functor ⋙ ((φ p).app ⟨SingleObj.star H⟩).toFunctor :=
  (rfl)

/-- The inverse fiber comparison of `L.mapActions φ hφ` after the component of `φ p` is the
inverse fiber comparison of `L`. -/
noncomputable def mapActionsInverseFiberIso (p : Γ) :
    ((φ p).app ⟨SingleObj.star H⟩).toFunctor ⋙ ((L.mapActions φ hφ).fiberEquivalence p).inverse ≅
      (L.fiberEquivalence p).inverse :=
  (Iso.isoCompInverse (H := (L.mapActions φ hφ).fiberEquivalence p)
    (Iso.inverseCompIso (G := L.fiberEquivalence p) (Iso.refl _))).symm

/-- The inverse fiber comparison of `L.mapActions φ hφ` is characterized by the counits of the
two fiber comparisons. -/
@[reassoc]
lemma functor_map_mapActionsInverseFiberIso_inv_app_comp_counit (p : Γ) (X : fiber actions p) :
    ((L.mapActions φ hφ).fiberEquivalence p).functor.map
        ((L.mapActionsInverseFiberIso φ hφ p).inv.app X) ≫
      ((L.mapActions φ hφ).fiberEquivalence p).counit.app
        (((φ p).app ⟨SingleObj.star H⟩).toFunctor.obj X) =
    ((φ p).app ⟨SingleObj.star H⟩).toFunctor.map ((L.fiberEquivalence p).counit.app X) := by
  -- The fiber comparison of `L.mapActions φ hφ` is `e_p ⋙ φ_p` only after unfolding, so the
  -- components of the isomorphisms built from it are computed by `erw`.
  erw [Iso.symm_inv, Iso.isoCompInverse_hom_app, Iso.inverseCompIso_hom_app, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp, Functor.map_comp, Category.assoc,
    ((L.mapActions φ hφ).fiberEquivalence p).counit_naturality,
    ((L.mapActions φ hφ).fiberEquivalence p).functor_unit_comp_assoc]
  rfl

/-- The transport functors of `L.mapActions φ hφ` are intertwined with those of `L` by the
components of `φ`. -/
noncomputable def mapActionsTransportIso {p q : Γ} (g : p ⟶ q) :
    ((φ p).app ⟨SingleObj.star H⟩).toFunctor ⋙ (L.mapActions φ hφ).transport g ≅
      L.transport g ⋙ ((φ q).app ⟨SingleObj.star H⟩).toFunctor :=
  Functor.isoWhiskerRight (L.mapActionsInverseFiberIso φ hφ p)
    (L.jointMap g ⋙ (L.fiberEquivalence q).functor ⋙ ((φ q).app ⟨SingleObj.star H⟩).toFunctor)

@[simp]
lemma mapActionsTransportIso_hom_app {p q : Γ} (g : p ⟶ q) (X : fiber actions p) :
    (L.mapActionsTransportIso φ hφ g).hom.app X =
      ((φ q).app ⟨SingleObj.star H⟩).toFunctor.map ((L.fiberEquivalence q).functor.map
        ((L.jointMap g).map ((L.mapActionsInverseFiberIso φ hφ p).hom.app X))) :=
  (rfl)

@[simp]
lemma mapActionsTransportIso_inv_app {p q : Γ} (g : p ⟶ q) (X : fiber actions p) :
    (L.mapActionsTransportIso φ hφ g).inv.app X =
      ((φ q).app ⟨SingleObj.star H⟩).toFunctor.map ((L.fiberEquivalence q).functor.map
        ((L.jointMap g).map ((L.mapActionsInverseFiberIso φ hφ p).inv.app X))) :=
  (rfl)

namespace Hom

/-- Whiskering a commutative triangle `x ▷ c ≫ m' = m` on the right by `d` gives a commutative
triangle with the associators inserted. -/
private lemma whiskerRight_comp_inv_associator_whiskerRight {B : Type*} [Bicategory B]
    {a b c d : B} {f g : a ⟶ b} {k : b ⟶ c} {e : a ⟶ c} {l : c ⟶ d} {x : f ⟶ g}
    {m : f ≫ k ⟶ e} {m' : g ≫ k ⟶ e} (h : x ▷ k ≫ m' = m) :
    x ▷ (k ≫ l) ≫ (α_ g k l).inv ≫ m' ▷ l = (α_ f k l).inv ≫ m ▷ l := by
  rw [← h, comp_whiskerRight]
  simp

variable {L L' L'' : EquivariantGroupoidLift Γ actions}

/-- A morphism of lifts of `actions` induces a morphism of the lifts of `actions'` obtained by
following the fiber comparisons by `φ`. The joint transformation is unchanged. -/
-- Exposed so that the joint transformation is definitionally `f.joint`, which the statements of
-- the compatible modifications and of `mapActions_fiberIso_hom_as_app` require.
@[expose] noncomputable def mapActions (f : L.Hom L') :
    (L.mapActions φ hφ).Hom (L'.mapActions φ hφ) where
  joint := f.joint
  fiberIso p := (α_ _ _ _).symm ≪≫ whiskerRightIso (f.fiberIso p) (φ p)

@[simp]
lemma mapActions_joint (f : L.Hom L') : (f.mapActions φ hφ).joint = f.joint :=
  (rfl)

@[simp]
lemma mapActions_fiberIso_hom_as_app (f : L.Hom L') (p : Γ)
    (a : LocallyDiscrete (SingleObj H)) :
    ((f.mapActions φ hφ).fiberIso p).hom.as.app a =
      (α_ _ _ _).inv ≫ (f.fiberIso p).hom.as.app a ▷ (φ p).app a :=
  (rfl)

@[simp]
lemma mapActions_fiberIso_inv_as_app (f : L.Hom L') (p : Γ)
    (a : LocallyDiscrete (SingleObj H)) :
    ((f.mapActions φ hφ).fiberIso p).inv.as.app a =
      (f.fiberIso p).inv.as.app a ▷ (φ p).app a ≫ (α_ _ _ _).hom :=
  (rfl)

/-- A compatible modification of morphisms of lifts of `actions` remains compatible after
following the fiber comparisons by `φ`. -/
noncomputable def Hom₂.mapActions {f f' : L.Hom L'} (Θ : f ⟶ f') :
    f.mapActions φ hφ ⟶ f'.mapActions φ hφ where
  joint := Θ.joint
  comm p a := whiskerRight_comp_inv_associator_whiskerRight (Θ.comm p a)

@[simp]
lemma Hom₂.mapActions_joint {f f' : L.Hom L'} (Θ : f ⟶ f') :
    (Hom₂.mapActions φ hφ Θ).joint = Θ.joint :=
  (rfl)

/-- The fiber isomorphism of a composite of lift morphisms, whiskered on the right, is the
composite of the whiskered fiber isomorphisms, up to the associators. -/
private lemma id_whiskerRight_associator_whiskerLeft_whiskerRight {B : Type*} [Bicategory B]
    {a b c d e : B} (x : a ⟶ b) (y : b ⟶ c) {k' : b ⟶ d} (k : c ⟶ d) (l : d ⟶ e)
    {t : a ⟶ d} (my : y ≫ k ⟶ k') (mx : x ≫ k' ⟶ t) :
    𝟙 (x ≫ y) ▷ (k ≫ l) ≫ (α_ x y (k ≫ l)).hom ≫ x ◁ ((α_ y k l).inv ≫ my ▷ l) ≫
        (α_ x k' l).inv ≫ mx ▷ l =
      (α_ (x ≫ y) k l).inv ≫ ((α_ x y k).hom ≫ x ◁ my ≫ mx) ▷ l := by
  simp

/-- Following the fiber comparisons by `φ` preserves the identity morphism of a lift. -/
noncomputable def mapActionsIdIso (L : EquivariantGroupoidLift Γ actions) :
    (id L).mapActions φ hφ ≅ id (L.mapActions φ hφ) :=
  isoMk (Iso.refl _) (fun p a ↦ by
    rw [id_fiberIso_hom_as_app, mapActions_fiberIso_hom_as_app, id_fiberIso_hom_as_app]
    exact (congrArg (· ≫ _) (id_whiskerRight _ _)).trans
      ((Category.id_comp _).trans (leftUnitor_comp _ _)))

variable {L'' : EquivariantGroupoidLift Γ actions} in
/-- Following the fiber comparisons by `φ` preserves composition of morphisms of lifts. -/
noncomputable def mapActionsCompIso (f : L.Hom L') (g : L'.Hom L'') :
    (f.comp g).mapActions φ hφ ≅ (f.mapActions φ hφ).comp (g.mapActions φ hφ) :=
  isoMk (Iso.refl _) (fun p a ↦ by
    rw [comp_fiberIso_hom_as_app, mapActions_fiberIso_hom_as_app, mapActions_fiberIso_hom_as_app,
      mapActions_fiberIso_hom_as_app, comp_fiberIso_hom_as_app]
    exact id_whiskerRight_associator_whiskerLeft_whiskerRight _ _ _ _ _ _)

end Hom

/-- Following the fiber comparisons by a family `φ p : actions p ⟶ actions' p` of strong
transformations with equivalence components, as a pseudofunctor between the bicategories of
lifts. It does not change joint pseudofunctors, joint transformations or joint modifications. -/
-- Exposed so that its values reduce to `mapActions`, `Hom.mapActions` and `Hom.Hom₂.mapActions`
-- in the types of the unit and counit transformations below.
@[expose, simps obj map map₂] noncomputable def mapActionsPseudofunctor :
    EquivariantGroupoidLift Γ actions ⥤ᵖ EquivariantGroupoidLift Γ actions' where
  obj L := L.mapActions φ hφ
  map f := Hom.mapActions φ hφ f
  map₂ Θ := Hom.Hom₂.mapActions φ hφ Θ
  mapId L := Hom.mapActionsIdIso φ hφ L
  mapComp f g := Hom.mapActionsCompIso φ hφ f g
  map₂_id _ := Subsingleton.elim _ _
  map₂_comp _ _ := Subsingleton.elim _ _
  map₂_whisker_left _ _ _ _ := Subsingleton.elim _ _
  map₂_whisker_right _ _ := Subsingleton.elim _ _
  map₂_associator _ _ _ := Subsingleton.elim _ _
  map₂_left_unitor _ := Subsingleton.elim _ _
  map₂_right_unitor _ := Subsingleton.elim _ _

section Unit

variable (ψ : ∀ p, actions' p ⟶ actions p)
  (hψ : ∀ p, ((ψ p).app ⟨SingleObj.star H⟩).toFunctor.IsEquivalence)

/-- For isomorphisms `𝟙 ≅ φ p ≫ ψ p`, the morphism from a lift `L` to the lift obtained by
following its fiber comparisons by `φ` and then by `ψ`. Its joint transformation is the
identity. -/
-- Exposed so that the joint transformation is definitionally `𝟙 L.joint`, which the statement of
-- `mapActionsUnitHom_fiberIso_hom_as_app` requires.
@[expose] noncomputable def mapActionsUnitHom (θ : ∀ p, 𝟙 (actions p) ≅ φ p ≫ ψ p) :
    L.Hom ((L.mapActions φ hφ).mapActions ψ hψ) where
  joint := 𝟙 L.joint
  fiberIso p :=
    whiskerLeftIso (B := LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w})
        ((Prod.sectR p (SingleObj H)).toPseudofunctor.whiskerLeft (𝟙 L.joint))
        (associator (B := LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w})
            (L.comparison p) (φ p) (ψ p) ≪≫
          whiskerLeftIso (B := LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}) (L.comparison p)
            (θ p).symm ≪≫ rightUnitor (B := LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w})
            (L.comparison p)) ≪≫
      (Hom.id L).fiberIso p

@[simp]
lemma mapActionsUnitHom_joint (θ : ∀ p, 𝟙 (actions p) ≅ φ p ≫ ψ p) :
    (L.mapActionsUnitHom φ hφ ψ hψ θ).joint = 𝟙 L.joint :=
  (rfl)

@[simp]
lemma mapActionsUnitHom_fiberIso_hom_as_app (θ : ∀ p, 𝟙 (actions p) ≅ φ p ≫ ψ p) (p : Γ)
    (a : LocallyDiscrete (SingleObj H)) :
    ((L.mapActionsUnitHom φ hφ ψ hψ θ).fiberIso p).hom.as.app a =
      (λ_ _).hom ≫ (α_ _ _ _).hom ≫ (L.comparison p).app a ◁ (θ p).inv.as.app a ≫
        (ρ_ ((L.comparison p).app a)).hom := by
  -- The target comparison is the composite `(c ≫ φ) ≫ ψ` only after unfolding `mapActions`,
  -- so the components of the composite isomorphism are computed by `erw`.
  erw [Iso.trans_hom, homCategory_comp_as_app, Hom.id_fiberIso_hom_as_app, whiskerLeftIso_hom,
    whiskerLeft_as_app, Iso.trans_hom, Iso.trans_hom, homCategory_comp_as_app,
    homCategory_comp_as_app, whiskerLeftIso_hom, whiskerLeft_as_app]
  exact leftUnitor_naturality _

/-- For isomorphisms `ψ p ≫ φ p ≅ 𝟙`, the morphism to a lift `L` of `actions'` from the lift
obtained by following its fiber comparisons by `ψ` and then by `φ`. Its joint transformation is
the identity. -/
-- Exposed so that the joint transformation is definitionally `𝟙 L.joint`, which the statement of
-- `mapActionsCounitHom_fiberIso_hom_as_app` requires.
@[expose] noncomputable def mapActionsCounitHom (L : EquivariantGroupoidLift Γ actions')
    (θ : ∀ p, ψ p ≫ φ p ≅ 𝟙 (actions' p)) :
    ((L.mapActions ψ hψ).mapActions φ hφ).Hom L where
  joint := 𝟙 L.joint
  fiberIso p :=
    (Hom.id L).fiberIso p ≪≫
      (associator (B := LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w})
          (L.comparison p) (ψ p) (φ p) ≪≫
        whiskerLeftIso (B := LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}) (L.comparison p)
          (θ p) ≪≫ rightUnitor (B := LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w})
          (L.comparison p)).symm

@[simp]
lemma mapActionsCounitHom_joint (L : EquivariantGroupoidLift Γ actions')
    (θ : ∀ p, ψ p ≫ φ p ≅ 𝟙 (actions' p)) :
    (L.mapActionsCounitHom φ hφ ψ hψ θ).joint = 𝟙 L.joint :=
  (rfl)

@[simp]
lemma mapActionsCounitHom_fiberIso_hom_as_app (L : EquivariantGroupoidLift Γ actions')
    (θ : ∀ p, ψ p ≫ φ p ≅ 𝟙 (actions' p)) (p : Γ) (a : LocallyDiscrete (SingleObj H)) :
    ((L.mapActionsCounitHom φ hφ ψ hψ θ).fiberIso p).hom.as.app a =
      (λ_ _).hom ≫ (ρ_ ((L.comparison p).app a)).inv ≫
        (L.comparison p).app a ◁ (θ p).inv.as.app a ≫ (α_ _ _ _).inv := by
  -- The target comparison is the composite `(c ≫ ψ) ≫ φ` only after unfolding `mapActions`,
  -- so the components of the composite isomorphism are computed by `erw`.
  erw [Iso.trans_hom, homCategory_comp_as_app, Hom.id_fiberIso_hom_as_app, Iso.symm_hom,
    Iso.trans_inv, Iso.trans_inv, homCategory_comp_as_app, homCategory_comp_as_app,
    whiskerLeftIso_inv, whiskerLeft_as_app]
  exact congrArg (_ ≫ ·) (Category.assoc _ _ _)

/-- The coherence condition on the naturality isomorphisms of `mapActionsUnit`, in an arbitrary
bicategory: `F` is the component of a joint transformation, `mf` its fiber isomorphism, and `t`
the inverse of the unit `𝟙 ≅ φ ≫ ψ`. -/
private lemma mapActionsUnit_naturality_comm {B : Type*} [Bicategory B] {X X' A A' : B}
    (F : X ⟶ X') (c : X ⟶ A) (c' : X' ⟶ A) (mf : F ≫ c' ⟶ c) (φa : A ⟶ A') (ψa : A' ⟶ A)
    (t : φa ≫ ψa ⟶ 𝟙 A) :
    ((ρ_ F).hom ≫ (λ_ F).inv) ▷ ((c' ≫ φa) ≫ ψa) ≫ (α_ (𝟙 X) F ((c' ≫ φa) ≫ ψa)).hom ≫
      𝟙 X ◁ ((α_ F (c' ≫ φa) ψa).inv ≫ ((α_ F c' φa).inv ≫ mf ▷ φa) ▷ ψa) ≫
      ((λ_ ((c ≫ φa) ≫ ψa)).hom ≫ (α_ c φa ψa).hom ≫ c ◁ t ≫ (ρ_ c).hom) =
    (α_ F (𝟙 X') ((c' ≫ φa) ≫ ψa)).hom ≫
      F ◁ ((λ_ ((c' ≫ φa) ≫ ψa)).hom ≫ (α_ c' φa ψa).hom ≫ c' ◁ t ≫ (ρ_ c').hom) ≫ mf := by
  simp only [whiskerRight_comp, comp_whiskerRight, leftUnitor_inv_whiskerRight, Category.assoc,
    pentagon_inv_inv_hom_hom_inv, id_whiskerLeft, Iso.inv_hom_id_assoc, whiskerLeft_comp,
    Iso.hom_inv_id_assoc, hom_inv_whiskerRight_assoc, whiskerLeft_rightUnitor, triangle_assoc,
    pentagon_assoc, Iso.cancel_iso_inv_left]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc]
  simp

/-- The strong transformation from the identity to following fiber comparisons by `φ` and then
by `ψ`, with components `mapActionsUnitHom`. -/
noncomputable def mapActionsUnit (θ : ∀ p, 𝟙 (actions p) ≅ φ p ≫ ψ p) :
    Pseudofunctor.StrongTrans (Pseudofunctor.id (EquivariantGroupoidLift Γ actions))
      ((mapActionsPseudofunctor φ hφ).comp (mapActionsPseudofunctor ψ hψ)) where
  app L := L.mapActionsUnitHom φ hφ ψ hψ θ
  naturality {L L'} f := Hom.isoMk (ρ_ f.joint ≪≫ (λ_ f.joint).symm) (fun p a ↦ by
    -- The fiber isomorphisms of composites with `mapActions` reduce only after unfolding.
    erw [Hom.comp_fiberIso_hom_as_app f (L'.mapActionsUnitHom φ hφ ψ hψ θ) p a,
      Hom.comp_fiberIso_hom_as_app (L.mapActionsUnitHom φ hφ ψ hψ θ)
        ((Hom.mapActions φ hφ f).mapActions ψ hψ) p a,
      mapActionsUnitHom_fiberIso_hom_as_app L φ hφ ψ hψ θ p a,
      mapActionsUnitHom_fiberIso_hom_as_app L' φ hφ ψ hψ θ p a,
      Hom.mapActions_fiberIso_hom_as_app ψ hψ (Hom.mapActions φ hφ f) p a,
      Hom.mapActions_fiberIso_hom_as_app φ hφ f p a]
    exact mapActionsUnit_naturality_comm _ _ _ _ _ _ _)
  naturality_naturality _ := Subsingleton.elim _ _
  naturality_id _ := Subsingleton.elim _ _
  naturality_comp _ _ := Subsingleton.elim _ _

@[simp]
lemma mapActionsUnit_app (θ : ∀ p, 𝟙 (actions p) ≅ φ p ≫ ψ p)
    (L : EquivariantGroupoidLift Γ actions) :
    (mapActionsUnit φ hφ ψ hψ θ).app L = L.mapActionsUnitHom φ hφ ψ hψ θ :=
  (rfl)

/-- The coherence condition on the naturality isomorphisms of `mapActionsCounit`, in an
arbitrary bicategory: `F` is the component of a joint transformation, `mf` its fiber isomorphism,
and `t` the inverse of the counit `ψ ≫ φ ≅ 𝟙`. -/
private lemma mapActionsCounit_naturality_comm {B : Type*} [Bicategory B] {X X' A A' : B}
    (F : X ⟶ X') (c : X ⟶ A') (c' : X' ⟶ A') (mf : F ≫ c' ⟶ c) (ψa : A' ⟶ A) (φa : A ⟶ A')
    (t : 𝟙 A' ⟶ ψa ≫ φa) :
    ((ρ_ F).hom ≫ (λ_ F).inv) ▷ c' ≫ (α_ (𝟙 X) F c').hom ≫ 𝟙 X ◁ mf ≫
      ((λ_ c).hom ≫ (ρ_ c).inv ≫ c ◁ t ≫ (α_ c ψa φa).inv) =
    (α_ F (𝟙 X') c').hom ≫
      F ◁ ((λ_ c').hom ≫ (ρ_ c').inv ≫ c' ◁ t ≫ (α_ c' ψa φa).inv) ≫
      ((α_ F (c' ≫ ψa) φa).inv ≫ ((α_ F c' ψa).inv ≫ mf ▷ ψa) ▷ φa) := by
  simp only [comp_whiskerRight, leftUnitor_inv_whiskerRight, id_whiskerLeft, Category.assoc,
    Iso.inv_hom_id_assoc, whiskerLeft_comp, whiskerLeft_rightUnitor_inv, pentagon_inv_assoc,
    triangle_assoc]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc, associator_inv_naturality_left]
  simp

/-- The strong transformation to the identity from following fiber comparisons by `ψ` and then
by `φ`, with components `mapActionsCounitHom`. -/
noncomputable def mapActionsCounit (θ : ∀ p, ψ p ≫ φ p ≅ 𝟙 (actions' p)) :
    Pseudofunctor.StrongTrans
      ((mapActionsPseudofunctor ψ hψ).comp (mapActionsPseudofunctor φ hφ))
      (Pseudofunctor.id (EquivariantGroupoidLift Γ actions')) where
  app L := L.mapActionsCounitHom φ hφ ψ hψ θ
  naturality {L L'} f := Hom.isoMk (ρ_ f.joint ≪≫ (λ_ f.joint).symm) (fun p a ↦ by
    -- The fiber isomorphisms of composites with `mapActions` reduce only after unfolding.
    erw [Hom.comp_fiberIso_hom_as_app (L.mapActionsCounitHom φ hφ ψ hψ θ) f p a,
      Hom.comp_fiberIso_hom_as_app ((Hom.mapActions ψ hψ f).mapActions φ hφ)
        (L'.mapActionsCounitHom φ hφ ψ hψ θ) p a,
      mapActionsCounitHom_fiberIso_hom_as_app φ hφ ψ hψ L θ p a,
      mapActionsCounitHom_fiberIso_hom_as_app φ hφ ψ hψ L' θ p a,
      Hom.mapActions_fiberIso_hom_as_app φ hφ (Hom.mapActions ψ hψ f) p a,
      Hom.mapActions_fiberIso_hom_as_app ψ hψ f p a]
    exact mapActionsCounit_naturality_comm _ _ _ _ _ _ _)
  naturality_naturality _ := Subsingleton.elim _ _
  naturality_id _ := Subsingleton.elim _ _
  naturality_comp _ _ := Subsingleton.elim _ _

@[simp]
lemma mapActionsCounit_app (θ : ∀ p, ψ p ≫ φ p ≅ 𝟙 (actions' p))
    (L : EquivariantGroupoidLift Γ actions') :
    (mapActionsCounit φ hφ ψ hψ θ).app L = L.mapActionsCounitHom φ hφ ψ hψ θ :=
  (rfl)

/-- For isomorphisms `𝟙 ≅ φ p ≫ ψ p`, the identity of the bicategory of lifts of `actions` is
equivalent to following fiber comparisons by `φ` and then by `ψ`. -/
noncomputable def mapActionsUnitEquiv (θ : ∀ p, 𝟙 (actions p) ≅ φ p ≫ ψ p) :
    Bicategory.Equivalence (Pseudofunctor.id (EquivariantGroupoidLift Γ actions))
      ((mapActionsPseudofunctor φ hφ).comp (mapActionsPseudofunctor ψ hψ)) :=
  (mapActionsUnit φ hφ ψ hψ θ).equivalenceMk
    (fun L ↦ (L.mapActionsUnitHom φ hφ ψ hψ θ).equivalence.inv)
    (fun L ↦ (L.mapActionsUnitHom φ hφ ψ hψ θ).equivalence.unit)
    (fun L ↦ (L.mapActionsUnitHom φ hφ ψ hψ θ).equivalence.counit)
    (fun L ↦ (L.mapActionsUnitHom φ hφ ψ hψ θ).equivalence.left_triangle)

/-- For isomorphisms `ψ p ≫ φ p ≅ 𝟙`, following fiber comparisons by `ψ` and then by `φ` is
equivalent to the identity of the bicategory of lifts of `actions'`. -/
noncomputable def mapActionsCounitEquiv (θ : ∀ p, ψ p ≫ φ p ≅ 𝟙 (actions' p)) :
    Bicategory.Equivalence
      ((mapActionsPseudofunctor ψ hψ).comp (mapActionsPseudofunctor φ hφ))
      (Pseudofunctor.id (EquivariantGroupoidLift Γ actions')) :=
  (mapActionsCounit φ hφ ψ hψ θ).equivalenceMk
    (fun L ↦ (L.mapActionsCounitHom φ hφ ψ hψ θ).equivalence.inv)
    (fun L ↦ (L.mapActionsCounitHom φ hφ ψ hψ θ).equivalence.unit)
    (fun L ↦ (L.mapActionsCounitHom φ hφ ψ hψ θ).equivalence.counit)
    (fun L ↦ (L.mapActionsCounitHom φ hφ ψ hψ θ).equivalence.left_triangle)

@[simp]
lemma mapActionsUnitEquiv_hom (θ : ∀ p, 𝟙 (actions p) ≅ φ p ≫ ψ p) :
    (mapActionsUnitEquiv φ hφ ψ hψ θ).hom = mapActionsUnit φ hφ ψ hψ θ :=
  (rfl)

@[simp]
lemma mapActionsCounitEquiv_hom (θ : ∀ p, ψ p ≫ φ p ≅ 𝟙 (actions' p)) :
    (mapActionsCounitEquiv φ hφ ψ hψ θ).hom = mapActionsCounit φ hφ ψ hψ θ :=
  (rfl)

end Unit

/-- Equivalences `actions p ≌ actions' p` of the prescribed actions induce a biequivalence of
the bicategories of lifts, whose pseudofunctors follow the fiber comparisons by the forward and
by the inverse equivalences. -/
-- Exposed so that the unit and counit equivalences are typed against the stated pseudofunctors.
@[expose] noncomputable def mapActionsBiequivalence
    (e : ∀ p, Bicategory.Equivalence (actions p) (actions' p)) :
    TauCeti.Biequivalence (EquivariantGroupoidLift Γ actions)
      (EquivariantGroupoidLift Γ actions') where
  functor := mapActionsPseudofunctor (fun p ↦ (e p).hom) (fun p ↦ (e p).isEquivalence_hom_app _)
  inverse := mapActionsPseudofunctor (fun p ↦ (e p).inv) (fun p ↦ (e p).isEquivalence_inv_app _)
  unitEquiv := mapActionsUnitEquiv _ _ _ _ (fun p ↦ (e p).unit)
  counitEquiv := mapActionsCounitEquiv _ _ _ _ (fun p ↦ (e p).counit)

section Biequivalence

variable (e : ∀ p, Bicategory.Equivalence (actions p) (actions' p))

@[simp]
lemma mapActionsBiequivalence_functor :
    (mapActionsBiequivalence e).functor =
      mapActionsPseudofunctor (fun p ↦ (e p).hom) (fun p ↦ (e p).isEquivalence_hom_app _) :=
  (rfl)

@[simp]
lemma mapActionsBiequivalence_inverse :
    (mapActionsBiequivalence e).inverse =
      mapActionsPseudofunctor (fun p ↦ (e p).inv) (fun p ↦ (e p).isEquivalence_inv_app _) :=
  (rfl)

@[simp]
lemma mapActionsBiequivalence_unitEquiv :
    (mapActionsBiequivalence e).unitEquiv =
      mapActionsUnitEquiv _ _ _ _ (fun p ↦ (e p).unit) :=
  (rfl)

@[simp]
lemma mapActionsBiequivalence_counitEquiv :
    (mapActionsBiequivalence e).counitEquiv =
      mapActionsCounitEquiv _ _ _ _ (fun p ↦ (e p).counit) :=
  (rfl)

end Biequivalence

end TauCeti.EquivariantGroupoidLift
