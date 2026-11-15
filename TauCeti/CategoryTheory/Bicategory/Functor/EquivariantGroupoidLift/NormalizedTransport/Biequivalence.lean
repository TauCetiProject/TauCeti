/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Biequivalence
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.NormalizedTransport.Counit
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.NormalizedTransport.Unit

/-!
# The biequivalence of equivariant groupoid lifts with normalized transport

Every coherent equivariant lift `L` of prescribed categorical actions `actions` is equivalent to
the lift `L.normalizedTransport.toLift` reconstructed from its normalized fiber transport, via
`L.normalizationEquivalence` with inverse `L.normalizationInv`. This file proves that these
objectwise equivalences are pseudonatural in morphisms `φ : L ⟶ L'` of lifts, and assembles them
with `normalizationPseudofunctor`, `reconstructionPseudofunctor` and `normalizationCounitEquiv`
into a biequivalence between `EquivariantGroupoidLift Γ actions` and the locally discrete
bicategory `LocallyDiscrete (NormalizedTransport Γ actions)`.

For a morphism `φ : L ⟶ L'`, the reconstructed normalized comparison
`φ.normalizedTransportHom.toLiftHom` has identity fiber components, whereas `L.normalizationInv`
and `L'.normalizationInv` have the chosen inverse fiber equivalences as components. On each joint
fiber, their composites are compared by the inverse-fiber comparison `φ.inverseFiberIso p` induced
as the mate of `φ.fiberFunctorIso p`. Along a joint arrow `(g, a)`, this comparison intertwines the
reconstructed-to-original comparisons `normalizationJointIso` with `φ.transportIso g` and
`φ.joint.naturality`, giving an invertible modification `φ.normalizationJointInvNaturality` and a
compatible `2`-isomorphism `φ.normalizationInvNaturality` of lift morphisms.

Passing to mates across `L.normalizationEquivalence` and `L'.normalizationEquivalence` produces the
forward naturality `2`-isomorphisms `φ.normalizationHomNaturality`. Since compatible modifications
between parallel morphisms of lifts are unique, the coherence axioms of strong transformations,
modifications and adjoint equivalences hold automatically, yielding `normalizationUnitInv`,
`normalizationUnitHom`, `normalizationUnitEquiv` and `normalizationBiequivalence`.

Normalizing `L.normalizationInv` recovers `(toLiftNormalizedTransportIso L.normalizedTransport).hom`
on the nose. Consequently, two parallel morphisms of lifts are `2`-isomorphic if and only if they
induce the same morphism of normalized transports, and every morphism of normalized transports
lifts to a morphism between the original lifts.

## Main declarations

* `TauCeti.EquivariantGroupoidLift.Hom.inverseFiberIso_hom_app_comp_normalizationJointIso`: the
  inverse-fiber comparisons intertwine `normalizationJointIso` along joint arrows;
* `TauCeti.EquivariantGroupoidLift.Hom.normalizationInvNaturality`,
  `TauCeti.EquivariantGroupoidLift.Hom.normalizationHomNaturality`: pseudonaturality `2`-cells for
  the inverse and forward components of `normalizationEquivalence`;
* `TauCeti.EquivariantGroupoidLift.Hom.equivalence_inv_normalizedTransportHom`,
  `TauCeti.EquivariantGroupoidLift.Hom.equivalence_inv_transportIso`,
  `TauCeti.EquivariantGroupoidLift.normalizationInv_normalizedTransportHom`,
  `TauCeti.EquivariantGroupoidLift.normalizationEquivalence_hom_normalizedTransportHom`:
  normalization sends quasi-inverses to groupoid inverses and sends the unit equivalences to the
  return comparisons of normalized transport;
* `TauCeti.EquivariantGroupoidLift.normalizationUnitHom`,
  `TauCeti.EquivariantGroupoidLift.normalizationUnitInv`,
  `TauCeti.EquivariantGroupoidLift.normalizationUnitEquiv`: the unit strong transformations and
  their adjoint equivalence;
* `TauCeti.EquivariantGroupoidLift.normalizationBiequivalence`: the biequivalence between
  `EquivariantGroupoidLift Γ actions` and `LocallyDiscrete (NormalizedTransport Γ actions)`;
* `TauCeti.EquivariantGroupoidLift.Hom.isoOfNormalizedTransportHomEq`,
  `TauCeti.EquivariantGroupoidLift.Hom.nonempty_iso_iff_normalizedTransportHom_eq`,
  `TauCeti.EquivariantGroupoidLift.Hom.liftNormalizedTransportHom`,
  `TauCeti.EquivariantGroupoidLift.Hom.liftNormalizedTransportHomIso`,
  `TauCeti.EquivariantGroupoidLift.toLiftNormalizationInvIso`: full and faithful reflection of
  `1`-morphisms up to `2`-isomorphism by normalization.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055), Chapters 4 and 6: strong transformations,
  modifications, adjoint equivalences and biequivalences.
* Edward Frenkel,
  [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  Cambridge Studies in Advanced Mathematics 103 (2007): families of local categories over the
  groupoid of local Langlands parameters, with their loop group actions.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory CategoryTheory.Prod Pseudofunctor.StrongTrans NormalizedTransport

section BicategoricalMates

private def mateIsoOfInv {B : Type*} [Bicategory B] {X₁ Y₁ X₂ Y₂ : B}
    (e₁ : X₁ ≌ Y₁) (e₂ : X₂ ≌ Y₂) {f : X₁ ⟶ X₂} {g : Y₁ ⟶ Y₂}
    (α : g ≫ e₂.inv ≅ e₁.inv ≫ f) :
    f ≫ e₂.hom ≅ e₁.hom ≫ g :=
  (λ_ (f ≫ e₂.hom)).symm ≪≫
    whiskerRightIso e₁.unit (f ≫ e₂.hom) ≪≫
    α_ e₁.hom e₁.inv (f ≫ e₂.hom) ≪≫
    whiskerLeftIso e₁.hom
      ((α_ e₁.inv f e₂.hom).symm ≪≫
        whiskerRightIso α.symm e₂.hom ≪≫
        α_ g e₂.inv e₂.hom ≪≫
        whiskerLeftIso g e₂.counit ≪≫
        ρ_ g)

private def cancelEquivalenceInvLeft {B : Type*} [Bicategory B] {X Y Z : B}
    (e : X ≌ Y) {f g : X ⟶ Z} (α : e.inv ≫ f ≅ e.inv ≫ g) :
    f ≅ g :=
  (λ_ f).symm ≪≫
    whiskerRightIso e.unit f ≪≫
    α_ e.hom e.inv f ≪≫
    whiskerLeftIso e.hom α ≪≫
    (α_ e.hom e.inv g).symm ≪≫
    whiskerRightIso e.unit.symm g ≪≫
    λ_ g

private def isoOfMateEq {B : Type*} [Bicategory B] {X₁ Y₁ X₂ Y₂ : B}
    (e₁ : X₁ ≌ Y₁) {e₂Inv : Y₂ ⟶ X₂} {f₁ f₂ : X₁ ⟶ X₂} {g₁ g₂ : Y₁ ⟶ Y₂}
    (α₁ : g₁ ≫ e₂Inv ≅ e₁.inv ≫ f₁) (α₂ : g₂ ≫ e₂Inv ≅ e₁.inv ≫ f₂) (h : g₁ = g₂) :
    f₁ ≅ f₂ :=
  cancelEquivalenceInvLeft e₁
    (α₁.symm ≪≫ whiskerRightIso (eqToIso h) e₂Inv ≪≫ α₂)

private lemma cat_whiskerRight_comp_associator_eq {C D D' : Cat.{v, w}}
    {F₀ : C ⟶ C} {I' : C ⟶ D'} {I : C ⟶ D} {Φ : D ⟶ D'} {E' : D' ⟶ C} {E : D ⟶ C}
    (α : F₀ ≫ I' ⟶ I ≫ Φ) (i : Φ ≫ E' ⟶ E)
    (ε : I ≫ E ⟶ F₀) (ε' : I' ≫ E' ⟶ F₀) (u : F₀ ≫ F₀ ⟶ F₀)
    (h : ∀ x : C, E'.toFunctor.map (α.toNatTrans.app x) ≫
      i.toNatTrans.app (I.toFunctor.obj x) ≫ ε.toNatTrans.app x =
        ε'.toNatTrans.app (F₀.toFunctor.obj x) ≫ u.toNatTrans.app x) :
    α ▷ E' ≫ ((α_ I Φ E').hom ≫ I ◁ i ≫ ε) =
      (α_ F₀ I' E').hom ≫ F₀ ◁ ε' ≫ u := by
  ext x
  simpa using h x

end BicategoricalMates

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}

namespace Hom

variable {L L' : EquivariantGroupoidLift Γ actions} (φ : L.Hom L')

private lemma inverseFiberIso_comp_inverse_map_transportIso {p q : Γ} (g : p ⟶ q)
    (x : fiber actions p) :
    (φ.inverseFiberIso q).hom.app ((L.transport g).obj x) ≫
        (L'.fiberEquivalence q).inverse.map ((φ.transportIso g).hom.app x) ≫
        (L'.fiberEquivalence q).unitInv.app
          ((L'.jointMap g).obj ((L'.fiberEquivalence p).inverse.obj x)) =
      (φ.jointFunctor q).map
          ((L.fiberEquivalence q).unitInv.app
            ((L.jointMap g).obj ((L.fiberEquivalence p).inverse.obj x))) ≫
        (φ.jointMapIso g).hom.app ((L.fiberEquivalence p).inverse.obj x) ≫
        (L'.jointMap g).map ((φ.inverseFiberIso p).hom.app x) := by
  rw [φ.transportIso_hom_app]
  dsimp only [EquivariantGroupoidLift.transport_obj, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  erw [(L'.fiberEquivalence q).unitInv_naturality,
    (L'.fiberEquivalence q).unitInv_naturality_assoc]
  simp only [Functor.id_obj]
  rw [φ.inverseFiberIso_hom_app_comp_unitInv_assoc q
    ((L.jointMap g).obj ((L.fiberEquivalence p).inverse.obj x))]

@[reassoc]
private lemma map_mapComp'_inv_comp_joint_naturality {p q : Γ} (g : p ⟶ q)
    (a : SingleObj.star H ⟶ SingleObj.star H) (y : L.jointFiber p) :
    (φ.jointFunctor q).map
        ((L.joint.mapComp' (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
          (g ×ₘ a).toLoc (by simp [← Quiver.Hom.comp_toLoc])).inv.toNatTrans.app y) ≫
        (φ.joint.naturality (g ×ₘ a).toLoc).hom.toNatTrans.app y =
      (φ.jointMapIso g).hom.app ((L.jointAct p a).obj y) ≫
        (L'.jointMap g).map ((φ.jointActIso p a).hom.app y) ≫
        (L'.joint.mapComp' (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
          (g ×ₘ a).toLoc (by simp [← Quiver.Hom.comp_toLoc])).inv.toNatTrans.app
            ((φ.jointFunctor p).obj y) := by
  have hc := φ.joint.naturality_comp'_hom_app
    (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ a).toLoc
    (by simp [← Quiver.Hom.comp_toLoc]) y
  rw [hc]
  simp only [jointMapIso_hom_app, jointActIso_hom_app, ← Functor.map_comp_assoc,
    Cat.Hom.inv_hom_id_toNatTrans_app]
  simp [jointAct]

/-- Along any joint arrow `(g, a)`, the inverse-fiber comparisons `φ.inverseFiberIso` intertwine
the reconstructed-to-original comparisons `normalizationJointIso` with `φ.transportIso g` on the
reconstructed source and `φ.joint.naturality` on the original target. -/
@[reassoc]
lemma inverseFiberIso_hom_app_comp_normalizationJointIso {p q : Γ} (g : p ⟶ q)
    (a : SingleObj.star H ⟶ SingleObj.star H) (x : fiber actions p) :
    (φ.inverseFiberIso q).hom.app
        ((L.normalizedTransport.jointFunctor (g ×ₘ a)).obj x) ≫
      (L'.fiberEquivalence q).inverse.map
        ((φ.transportIso g).hom.app ((act actions p a).obj x)) ≫
      (L'.normalizationJointIso (g ×ₘ a)).hom.app x =
    (φ.jointFunctor q).map ((L.normalizationJointIso (g ×ₘ a)).hom.app x) ≫
      (φ.joint.naturality (g ×ₘ a).toLoc).hom.toNatTrans.app
        ((L.fiberEquivalence p).inverse.obj x) ≫
      (L'.joint.map (g ×ₘ a).toLoc).toFunctor.map ((φ.inverseFiberIso p).hom.app x) := by
  dsimp only [NormalizedTransport.jointFunctor, normalizedTransport,
    EquivariantGroupoidLift.transport_obj, Functor.comp_obj]
  rw [L.normalizationJointIso_hom_app, L'.normalizationJointIso_hom_app]
  dsimp only [EquivariantGroupoidLift.transport_obj, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  have htr := φ.inverseFiberIso_comp_inverse_map_transportIso g ((act actions p a).obj x)
  dsimp only [EquivariantGroupoidLift.transport_obj, Functor.comp_obj] at htr
  rw [reassoc_of% htr]
  apply congrArg ((φ.jointFunctor q).map _ ≫ ·)
  rw [φ.map_mapComp'_inv_comp_joint_naturality_assoc g a
    ((L.fiberEquivalence p).inverse.obj x)]
  erw [← (L'.joint.mapComp' (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
    (g ×ₘ a).toLoc (by simp [← Quiver.Hom.comp_toLoc])).inv.toNatTrans.naturality]
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_map]
  simp only [← Category.assoc]
  apply congrArg (· ≫ _)
  simp only [Category.assoc]
  have hn := (φ.jointMapIso g).hom.naturality ((L.actInverseIso p a).hom.app x)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  apply congrArg ((φ.jointMapIso g).hom.app _ ≫ ·)
  simp only [← (L'.jointMap g).map_comp]
  exact congrArg (L'.jointMap g).map (φ.inverseFiberIso_actInverseIso p a x).symm

/-- The invertible modification comparing the joint strong transformations of
`φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv` and `L.normalizationInv ≫ φ`. Its
component at `(p, ⋆)` is the left unitor followed by `(φ.inverseFiberIso p).symm`. -/
noncomputable def normalizationJointInvNaturality :
    φ.normalizedTransportHom.jointHom ≫ L'.normalizationJointInv ≅
      L.normalizationJointInv ≫ φ.joint :=
  Pseudofunctor.StrongTrans.isoMk
    (fun X ↦
      λ_ ((L'.fiberEquivalence X.as.1).inverse.toCatHom) ≪≫
        Cat.Hom.isoMk (φ.inverseFiberIso X.as.1).symm)
    (fun {X Y} f ↦ by
      obtain ⟨p, ⟨⟩⟩ := X
      obtain ⟨q, ⟨⟩⟩ := Y
      let g : p ⟶ q := f.as.1
      let a : SingleObj.star H ⟶ SingleObj.star H := f.as.2
      refine Cat.whiskerLeft_comp_eq_comp_whiskerRight _ _ _ _ fun (x : fiber actions p) ↦ ?_
      have app_eq (r : Γ) (y : fiber actions r) :
          (λ_ ((L'.fiberEquivalence r).inverse.toCatHom) ≪≫
            Cat.Hom.isoMk (φ.inverseFiberIso r).symm).hom.toNatTrans.app y =
            (φ.inverseFiberIso r).inv.app y := by
        simp
      have hgoal : (φ.inverseFiberIso q).inv.app
            ((L.normalizedTransport.jointFunctor (g ×ₘ a)).obj x) ≫
          (φ.jointFunctor q).map ((L.normalizationJointIso (g ×ₘ a)).hom.app x) ≫
          (φ.joint.naturality (g ×ₘ a).toLoc).hom.toNatTrans.app
            ((L.fiberEquivalence p).inverse.obj x) =
        ((L'.fiberEquivalence q).inverse.map
              ((φ.normalizedTransportHom.transportIso g).hom.app ((act actions p a).obj x)) ≫
            (L'.normalizationJointIso (g ×ₘ a)).hom.app x) ≫
          (L'.joint.map (g ×ₘ a).toLoc).toFunctor.map
            ((φ.inverseFiberIso p).inv.app x) := by
        rw [← cancel_epi ((φ.inverseFiberIso q).hom.app
          ((L.normalizedTransport.jointFunctor (g ×ₘ a)).obj x)),
          Iso.hom_inv_id_app_assoc]
        have h := congrArg
          (· ≫ (L'.joint.map (g ×ₘ a).toLoc).toFunctor.map
            ((φ.inverseFiberIso p).inv.app x))
          (φ.inverseFiberIso_hom_app_comp_normalizationJointIso g a x).symm
        rw [← normalizedTransportHom_transportIso] at h
        simp only [Functor.comp_obj, Category.assoc, ← CategoryTheory.Functor.map_comp,
          Iso.hom_inv_id_app, CategoryTheory.Functor.map_id] at h
        exact (congrArg (_ ≫ ·) (Category.comp_id _)).symm.trans h
      erw [app_eq q ((L.normalizedTransport.jointFunctor (g ×ₘ a)).obj x),
        app_eq p x,
        Pseudofunctor.StrongTrans.comp_naturality_hom_app,
        Pseudofunctor.StrongTrans.comp_naturality_hom_app,
        NormalizedTransport.Hom.jointHom_naturality_hom_app,
        L.normalizationJointInv_naturality_hom_app,
        L'.normalizationJointInv_naturality_hom_app]
      exact hgoal)

lemma normalizationJointInvNaturality_hom_as_app (X : LocallyDiscrete (Γ × SingleObj H)) :
    φ.normalizationJointInvNaturality.hom.as.app X =
      (λ_ ((L'.fiberEquivalence X.as.1).inverse.toCatHom) ≪≫
        Cat.Hom.isoMk (φ.inverseFiberIso X.as.1).symm).hom :=
  (rfl)

lemma normalizationJointInvNaturality_inv_as_app (X : LocallyDiscrete (Γ × SingleObj H)) :
    φ.normalizationJointInvNaturality.inv.as.app X =
      (λ_ ((L'.fiberEquivalence X.as.1).inverse.toCatHom) ≪≫
        Cat.Hom.isoMk (φ.inverseFiberIso X.as.1).symm).inv :=
  (rfl)

lemma normalizationJointInvNaturality_hom_app (p : Γ) (x : fiber actions p) :
    (φ.normalizationJointInvNaturality.hom.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.app x =
      (φ.inverseFiberIso p).inv.app x := by
  simp [normalizationJointInvNaturality_hom_as_app]
  rfl

lemma normalizationJointInvNaturality_inv_app (p : Γ) (x : fiber actions p) :
    (φ.normalizationJointInvNaturality.inv.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.app x =
      (φ.inverseFiberIso p).hom.app x := by
  simp [normalizationJointInvNaturality_inv_as_app]
  rfl

/-- The morphisms `L.normalizationInv` are pseudonatural in lift morphisms `φ : L ⟶ L'`:
reconstructing the normalized comparison `φ.normalizedTransportHom` and applying
`L'.normalizationInv` is `2`-isomorphic to applying `L.normalizationInv` and then `φ`, through the
inverse-fiber comparisons `φ.inverseFiberIso`. -/
noncomputable def normalizationInvNaturality :
    φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv ≅ L.normalizationInv ≫ φ :=
  isoMk φ.normalizationJointInvNaturality fun p a ↦ by
    obtain ⟨⟨⟩⟩ := a
    rw [EquivariantGroupoidLift.comp_fiberIso, EquivariantGroupoidLift.comp_fiberIso,
      comp_fiberIso_hom_as_app, comp_fiberIso_hom_as_app,
      NormalizedTransport.Hom.toLiftHom_fiberIso_hom_as_app,
      L.normalizationInv_fiberIso_hom_as_app, L'.normalizationInv_fiberIso_hom_as_app]
    refine cat_whiskerRight_comp_associator_eq
      (φ.normalizationJointInvNaturality.hom.as.app ⟨(p, SingleObj.star H)⟩)
      ((φ.fiberIso p).hom.as.app ⟨SingleObj.star H⟩)
      (Cat.Hom.isoMk (L.fiberEquivalence p).counitIso).hom
      (Cat.Hom.isoMk (L'.fiberEquivalence p).counitIso).hom
      (λ_ (𝟙 (fiber actions p))).hom fun (x : fiber actions p) ↦ ?_
    have hi : ((φ.fiberIso p).hom.as.app ⟨SingleObj.star H⟩).toNatTrans.app
        ((L.fiberEquivalence p).inverse.obj x) =
        (φ.fiberFunctorIso p).hom.app ((L.fiberEquivalence p).inverse.obj x) :=
      (φ.fiberFunctorIso_hom_app p _).symm
    have hε : (Cat.Hom.isoMk (L.fiberEquivalence p).counitIso).hom.toNatTrans.app x =
        (L.fiberEquivalence p).counit.app x := (rfl)
    have hε' : (Cat.Hom.isoMk (L'.fiberEquivalence p).counitIso).hom.toNatTrans.app x =
        (L'.fiberEquivalence p).counit.app x := (rfl)
    have hu : (λ_ (𝟙 (fiber actions p))).hom.toNatTrans.app x = 𝟙 x := by simp
    have hgoal : (L'.fiberEquivalence p).functor.map ((φ.inverseFiberIso p).inv.app x) ≫
        (φ.fiberFunctorIso p).hom.app ((L.fiberEquivalence p).inverse.obj x) ≫
        (L.fiberEquivalence p).counit.app x =
      (L'.fiberEquivalence p).counit.app x := by
      rw [← cancel_epi ((L'.fiberEquivalence p).functor.map ((φ.inverseFiberIso p).hom.app x)),
        ← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
        CategoryTheory.Functor.map_id, Category.id_comp]
      exact (φ.functor_map_inverseFiberIso_hom_app_comp_counit p x).symm
    erw [φ.normalizationJointInvNaturality_hom_app p x, hi, hε, hε', hu]
    exact hgoal.trans (Category.comp_id _).symm

-- Keep these dependent joint-projection equations named without `@[simp]`: their composed
-- strong-transformation endpoints are not definitionally equal at reducible transparency in
-- importing modules.
lemma normalizationInvNaturality_hom_joint :
    φ.normalizationInvNaturality.hom.joint = φ.normalizationJointInvNaturality.hom :=
  isoMk_hom_joint _ _

lemma normalizationInvNaturality_inv_joint :
    φ.normalizationInvNaturality.inv.joint = φ.normalizationJointInvNaturality.inv :=
  isoMk_inv_joint _ _

lemma normalizationInvNaturality_hom_app (p : Γ) (x : fiber actions p) :
    (φ.normalizationInvNaturality.hom.joint.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.app x =
      (φ.inverseFiberIso p).inv.app x := by
  rw [normalizationInvNaturality_hom_joint]
  exact φ.normalizationJointInvNaturality_hom_app p x

lemma normalizationInvNaturality_inv_app (p : Γ) (x : fiber actions p) :
    (φ.normalizationInvNaturality.inv.joint.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.app x =
      (φ.inverseFiberIso p).hom.app x := by
  rw [normalizationInvNaturality_inv_joint]
  exact φ.normalizationJointInvNaturality_inv_app p x

/-- The forward equivalences `L.normalizationEquivalence.hom` are pseudonatural in lift morphisms
`φ : L ⟶ L'`, via the mate of `φ.normalizationInvNaturality` across `L.normalizationEquivalence`
and `L'.normalizationEquivalence`. -/
noncomputable def normalizationHomNaturality :
    φ ≫ L'.normalizationEquivalence.hom ≅
      L.normalizationEquivalence.hom ≫ φ.normalizedTransportHom.toLiftHom :=
  mateIsoOfInv L.normalizationEquivalence L'.normalizationEquivalence
    (f := φ) (g := φ.normalizedTransportHom.toLiftHom) φ.normalizationInvNaturality

/-- Normalizing the chosen quasi-inverse `φ.equivalence.inv` of a lift morphism `φ` gives the
groupoid inverse of `φ.normalizedTransportHom`. -/
@[simp]
lemma equivalence_inv_normalizedTransportHom :
    φ.equivalence.inv.normalizedTransportHom = CategoryTheory.inv φ.normalizedTransportHom := by
  refine (IsIso.inv_eq_of_hom_inv_id ?_).symm
  nth_rw 1 [← φ.equivalence_hom]
  rw [← comp_normalizedTransportHom, ← id_normalizedTransportHom]
  exact φ.equivalence.unit.symm.hom.normalizedTransportHom_eq

/-- The canonical transport isomorphism of `φ.equivalence.inv` along `g` is
`(φ.transportIso g).symm`. -/
@[simp]
lemma equivalence_inv_transportIso {p q : Γ} (g : p ⟶ q) :
    φ.equivalence.inv.transportIso g = (φ.transportIso g).symm := by
  rw [← normalizedTransportHom_transportIso, equivalence_inv_normalizedTransportHom,
    NormalizedTransport.inv_transportIso, normalizedTransportHom_transportIso]
  rfl

end Hom

section NormalizationOfUnit

variable (L : EquivariantGroupoidLift Γ actions)

private lemma normalizationInv_inverseFiberIso_hom_app (p : Γ) (x : fiber actions p) :
    (L.normalizationInv.inverseFiberIso p).hom.app x =
      (L.fiberEquivalence p).inverse.map
        ((L.normalizedTransport.toLift.fiberEquivalence p).counit.app x) := by
  apply (L.fiberEquivalence p).functor.map_injective
  apply (cancel_mono ((L.fiberEquivalence p).counit.app x)).mp
  rw [L.normalizationInv.functor_map_inverseFiberIso_hom_app_comp_counit]
  have hf : (L.normalizationInv.fiberFunctorIso p).hom.app
      ((L.normalizedTransport.toLift.fiberEquivalence p).inverse.obj x) =
      (L.fiberEquivalence p).counit.app
        ((L.normalizedTransport.toLift.fiberEquivalence p).inverse.obj x) := by
    rw [Hom.fiberFunctorIso_hom_app, L.normalizationInv_fiberIso_hom_as_app]
    rfl
  rw [hf]
  exact ((L.fiberEquivalence p).counit_naturality
    ((L.normalizedTransport.toLift.fiberEquivalence p).counit.app x)).symm

-- Keep this equation named without `@[simp]`: `EquivariantGroupoidLift.transport` and
-- `NormalizedTransport.transport` match via `@[expose]`, not reducible transparency, in importing
-- modules; `@[simp] normalizationInv_normalizedTransportHom` gives the confluent `Hom`-level rule.
/-- Normalizing `L.normalizationInv` along a parameter arrow `g` recovers the canonical return
isomorphism `L.normalizedTransport.toLiftTransportIso g`. -/
lemma normalizationInv_transportIso {p q : Γ} (g : p ⟶ q) :
    L.normalizationInv.transportIso g = L.normalizedTransport.toLiftTransportIso g := by
  ext x
  let y : fiber actions p := (L.normalizedTransport.toLift.fiberEquivalence p).inverse.obj x
  let ε : y ⟶ x := (L.normalizedTransport.toLift.fiberEquivalence p).counit.app x
  rw [Hom.transportIso_hom_app, NormalizedTransport.toLiftTransportIso_hom_app,
    L.normalizationInv_inverseFiberIso_hom_app p x]
  simp only [L.normalizationInv_fiberIso_inv_as_app, Hom.fiberFunctorIso_inv_app,
    Hom.jointMapIso_hom_app]
  erw [L.normalizationJointInv_naturality_hom_app]
  -- Reconstructed joint maps along `(g, 1)` are `T_1 ⋙ E_g` on the prescribed fibers, and
  -- `Cat.Hom.isoMk` on `counitIso` evaluates to `counitInv`.
  change (L.fiberEquivalence q).counitInv.app
        ((L.transport g).obj ((act actions p (𝟙 (SingleObj.star H))).obj y)) ≫
      (L.fiberEquivalence q).functor.map
        ((L.normalizationJointIso (g ×ₘ 𝟙 (SingleObj.star H))).hom.app y) ≫
      (L.fiberEquivalence q).functor.map
        ((L.jointMap g).map ((L.fiberEquivalence p).inverse.map ε)) =
    (L.transport g).map ((act actions p (𝟙 (SingleObj.star H))).map ε) ≫
      (L.transport g).map ((actId actions p).hom.app x)
  rw [L.normalizationJointIso_hom_app]
  dsimp only [transport_obj, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc, Equivalence.counitInv_functor_comp_assoc]
  simp only [← prod_id, Quiver.Hom.id_toLoc]
  rw [Pseudofunctor.mapComp'_id_comp_inv_app]
  have hinner : (L.actInverseIso p (𝟙 (SingleObj.star H))).hom.app y ≫
      (L.joint.mapId ⟨(p, SingleObj.star H)⟩).hom.toNatTrans.app
        ((L.fiberEquivalence p).inverse.obj y) ≫
      (L.fiberEquivalence p).inverse.map ε =
      (L.fiberEquivalence p).inverse.map
        ((act actions p (𝟙 (SingleObj.star H))).map ε ≫ (actId actions p).hom.app x) := by
    have hid : (L.joint.mapId ⟨(p, SingleObj.star H)⟩).hom.toNatTrans.app
        ((L.fiberEquivalence p).inverse.obj y) =
        (L.jointMapId p).hom.app ((L.fiberEquivalence p).inverse.obj y) := by
      simp only [jointMapId_hom_app, ← prod_id, Quiver.Hom.id_toLoc,
        Pseudofunctor.mapId'_eq_mapId]
    have hact := L.actInverseIso_actId_assoc p y ((L.fiberEquivalence p).inverse.map ε)
    have hnat : (actId actions p).hom.app y ≫ ε =
        (act actions p (𝟙 (SingleObj.star H))).map ε ≫ (actId actions p).hom.app x :=
      ((actId actions p).hom.naturality ε).symm
    erw [hid]
    exact hact.trans (by rw [← Functor.map_comp, hnat])
  simp only [transport_map, ← CategoryTheory.Functor.map_comp]
  refine Eq.trans ?_
    (congrArg (fun m ↦ (L.fiberEquivalence q).functor.map ((L.jointMap g).map m)) hinner)
  simp only [CategoryTheory.Functor.map_comp]
  apply congrArg (_ ≫ ·)
  exact ((congrArg (L.fiberEquivalence q).functor.map ((L.jointMap g).map_comp _ _)).trans
    ((L.fiberEquivalence q).functor.map_comp _ _)).symm

/-- Normalizing `L.normalizationInv` gives the forward return isomorphism
`(toLiftNormalizedTransportIso L.normalizedTransport).hom` of normalized transport. -/
@[simp]
lemma normalizationInv_normalizedTransportHom :
    L.normalizationInv.normalizedTransportHom =
      (toLiftNormalizedTransportIso L.normalizedTransport).hom := by
  refine NormalizedTransport.Hom.ext fun p q g ↦ ?_
  rw [Hom.normalizedTransportHom_transportIso, toLiftNormalizedTransportIso_hom_transportIso,
    L.normalizationInv_transportIso]

-- Keep this named equation without `@[simp]`: `L.normalizationEquivalence_hom` simplifies its
-- left-hand side to `L.normalizationInv.equivalence.inv.normalizedTransportHom`, which `simp`
-- reduces to `(toLiftNormalizedTransportIso L.normalizedTransport).inv` via
-- `Hom.equivalence_inv_normalizedTransportHom` and `normalizationInv_normalizedTransportHom`.
/-- Normalizing `L.normalizationEquivalence.hom` gives the inverse return isomorphism
`(toLiftNormalizedTransportIso L.normalizedTransport).inv` of normalized transport. -/
lemma normalizationEquivalence_hom_normalizedTransportHom :
    L.normalizationEquivalence.hom.normalizedTransportHom =
      (toLiftNormalizedTransportIso L.normalizedTransport).inv := by
  simp

end NormalizationOfUnit

section Biequivalence

variable (actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w})

/-- The strong transformation from normalization followed by reconstruction to the identity
pseudofunctor on `EquivariantGroupoidLift Γ actions`, with components `L.normalizationInv` and
naturality `2`-isomorphisms `Hom.normalizationInvNaturality`. -/
-- Expose the strong-transformation carrier so the component and naturality equations stay typed by
-- the literal `L.normalizationInv` morphisms in importing modules.
@[expose] noncomputable def normalizationUnitInv :
    (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) ⟶
      Pseudofunctor.id (EquivariantGroupoidLift Γ actions) where
  app L := L.normalizationInv
  naturality φ := φ.normalizationInvNaturality
  naturality_naturality _ := Subsingleton.elim _ _
  naturality_id _ := Subsingleton.elim _ _
  naturality_comp _ _ := Subsingleton.elim _ _

-- Keep the dependent `.app` equations named without `@[simp]`: their pseudofunctor-evaluation
-- endpoints match at default (`@[expose]`) rather than reducible transparency in importing modules.
lemma normalizationUnitInv_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitInv actions).app L = L.normalizationInv :=
  (rfl)

lemma normalizationUnitInv_naturality {L L' : EquivariantGroupoidLift Γ actions} (φ : L ⟶ L') :
    (normalizationUnitInv actions).naturality φ = φ.normalizationInvNaturality :=
  (rfl)

/-- The strong transformation from the identity pseudofunctor on
`EquivariantGroupoidLift Γ actions` to normalization followed by reconstruction, with components
`L.normalizationEquivalence.hom` and naturality `2`-isomorphisms
`Hom.normalizationHomNaturality`. -/
-- Expose the strong-transformation carrier so the component and naturality equations stay typed by
-- the literal `L.normalizationEquivalence.hom` morphisms in importing modules.
@[expose] noncomputable def normalizationUnitHom :
    Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ⟶
      (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) where
  app L := L.normalizationEquivalence.hom
  naturality φ := φ.normalizationHomNaturality
  naturality_naturality _ := Subsingleton.elim _ _
  naturality_id _ := Subsingleton.elim _ _
  naturality_comp _ _ := Subsingleton.elim _ _

lemma normalizationUnitHom_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitHom actions).app L = L.normalizationEquivalence.hom :=
  (rfl)

lemma normalizationUnitHom_naturality {L L' : EquivariantGroupoidLift Γ actions} (φ : L ⟶ L') :
    (normalizationUnitHom actions).naturality φ = φ.normalizationHomNaturality :=
  (rfl)

/-- The identity pseudofunctor of `EquivariantGroupoidLift Γ actions` is equivalent to
normalization followed by reconstruction, through `normalizationUnitHom` and
`normalizationUnitInv`. Its unit and counit modifications have components the units and counits of
`L.normalizationEquivalence`. -/
-- Expose the equivalence record so the unit and counit component equations stay typed by
-- `normalizationUnitHom` and `normalizationUnitInv` in importing modules.
@[expose] noncomputable def normalizationUnitEquiv :
    Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ≌
      (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) where
  hom := normalizationUnitHom actions
  inv := normalizationUnitInv actions
  unit := Pseudofunctor.StrongTrans.isoMk (fun L ↦ L.normalizationEquivalence.unit)
    (fun _ ↦ Subsingleton.elim _ _)
  counit := Pseudofunctor.StrongTrans.isoMk (fun L ↦ L.normalizationEquivalence.counit)
    (fun _ ↦ Subsingleton.elim _ _)
  left_triangle := Iso.ext <| homCategory.ext fun _ ↦ Subsingleton.elim _ _

@[simp]
lemma normalizationUnitEquiv_hom :
    (normalizationUnitEquiv actions).hom = normalizationUnitHom actions :=
  (rfl)

@[simp]
lemma normalizationUnitEquiv_inv :
    (normalizationUnitEquiv actions).inv = normalizationUnitInv actions :=
  (rfl)

lemma normalizationUnitEquiv_unit_hom_as_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitEquiv actions).unit.hom.as.app L = L.normalizationEquivalence.unit.hom :=
  (rfl)

lemma normalizationUnitEquiv_unit_inv_as_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitEquiv actions).unit.inv.as.app L = L.normalizationEquivalence.unit.inv :=
  (rfl)

lemma normalizationUnitEquiv_counit_hom_as_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitEquiv actions).counit.hom.as.app L = L.normalizationEquivalence.counit.hom :=
  (rfl)

lemma normalizationUnitEquiv_counit_inv_as_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitEquiv actions).counit.inv.as.app L = L.normalizationEquivalence.counit.inv :=
  (rfl)

/-- The biequivalence between the bicategory of coherent equivariant groupoid lifts and the locally
discrete bicategory of normalized transports on the prescribed fibers. Its forward pseudofunctor
normalizes transport by conjugating the joint functors by chosen inverses to the fiber comparisons,
and its inverse reconstructs lifts using identity fiber comparisons. -/
-- Expose the biequivalence record so its pseudofunctor and equivalence fields align definitionally
-- with `normalizationPseudofunctor`, `reconstructionPseudofunctor`, `normalizationUnitEquiv` and
-- `normalizationCounitEquiv` in importing modules.
@[expose] noncomputable def normalizationBiequivalence :
    TauCeti.Biequivalence (EquivariantGroupoidLift Γ actions)
      (LocallyDiscrete (NormalizedTransport Γ actions)) where
  functor := normalizationPseudofunctor actions
  inverse := reconstructionPseudofunctor actions
  unitEquiv := normalizationUnitEquiv actions
  counitEquiv := normalizationCounitEquiv actions

@[simp]
lemma normalizationBiequivalence_functor :
    (normalizationBiequivalence actions).functor = normalizationPseudofunctor actions :=
  (rfl)

@[simp]
lemma normalizationBiequivalence_inverse :
    (normalizationBiequivalence actions).inverse = reconstructionPseudofunctor actions :=
  (rfl)

-- Keep the dependent `unitEquiv` and `counitEquiv` equations named without `@[simp]`: their types
-- depend on `functor` and `inverse`, which unfold at default (`@[expose]`) transparency.
lemma normalizationBiequivalence_unitEquiv :
    (normalizationBiequivalence actions).unitEquiv = normalizationUnitEquiv actions :=
  (rfl)

lemma normalizationBiequivalence_counitEquiv :
    (normalizationBiequivalence actions).counitEquiv = normalizationCounitEquiv actions :=
  (rfl)

end Biequivalence

namespace Hom

variable {L L' : EquivariantGroupoidLift Γ actions}

/-- Two parallel morphisms of lifts inducing the same morphism of normalized transports are
`2`-isomorphic. -/
noncomputable def isoOfNormalizedTransportHomEq {φ ψ : L ⟶ L'}
    (h : φ.normalizedTransportHom = ψ.normalizedTransportHom) : φ ≅ ψ :=
  isoOfMateEq L.normalizationEquivalence
    φ.normalizationInvNaturality ψ.normalizationInvNaturality
    (congrArg NormalizedTransport.Hom.toLiftHom h)

/-- Two parallel morphisms of lifts are `2`-isomorphic if and only if they induce the same
morphism of normalized transports on the prescribed fibers. -/
lemma nonempty_iso_iff_normalizedTransportHom_eq (φ ψ : L ⟶ L') :
    Nonempty (φ ≅ ψ) ↔ φ.normalizedTransportHom = ψ.normalizedTransportHom :=
  ⟨fun ⟨e⟩ ↦ e.hom.normalizedTransportHom_eq, fun h ↦ ⟨isoOfNormalizedTransportHomEq h⟩⟩

/-- Two parallel morphisms of lifts admit a compatible modification if and only if they induce
the same morphism of normalized transports. -/
lemma nonempty_hom_iff_normalizedTransportHom_eq (φ ψ : L ⟶ L') :
    Nonempty (φ ⟶ ψ) ↔ φ.normalizedTransportHom = ψ.normalizedTransportHom :=
  ⟨fun ⟨Θ⟩ ↦ Θ.normalizedTransportHom_eq, fun h ↦ ⟨(isoOfNormalizedTransportHomEq h).hom⟩⟩

/-- Lift a morphism of normalized transports between `L.normalizedTransport` and
`L'.normalizedTransport` to a morphism `L ⟶ L'` of equivariant lifts by conjugating its
reconstructed lift morphism with the normalization equivalences. -/
noncomputable def liftNormalizedTransportHom
    (f : L.normalizedTransport ⟶ L'.normalizedTransport) : L ⟶ L' :=
  L.normalizationEquivalence.hom ≫ f.toLiftHom ≫ L'.normalizationInv

/-- Normalizing `Hom.liftNormalizedTransportHom f` recovers `f` on the nose. -/
@[simp]
lemma liftNormalizedTransportHom_normalizedTransportHom
    (f : L.normalizedTransport ⟶ L'.normalizedTransport) :
    (liftNormalizedTransportHom f).normalizedTransportHom = f := by
  simp only [liftNormalizedTransportHom, Hom.comp_normalizedTransportHom,
    normalizationEquivalence_hom_normalizedTransportHom,
    normalizationInv_normalizedTransportHom, toLiftNormalizedTransportIso_hom_naturality,
    Iso.inv_hom_id_assoc]

/-- Lifting the normalized comparison induced by a lift morphism `φ : L ⟶ L'` recovers `φ` up to
a compatible `2`-isomorphism. -/
noncomputable def liftNormalizedTransportHomIso (φ : L ⟶ L') :
    liftNormalizedTransportHom φ.normalizedTransportHom ≅ φ :=
  isoOfNormalizedTransportHomEq (liftNormalizedTransportHom_normalizedTransportHom _)

end Hom

/-- On a reconstructed lift `N.toLift`, the inverse unit morphism `N.toLift.normalizationInv` is
`2`-isomorphic to the reconstructed forward return comparison
`(toLiftNormalizedTransportIso N).hom.toLiftHom`. -/
noncomputable def toLiftNormalizationInvIso (N : NormalizedTransport Γ actions) :
    N.toLift.normalizationInv ≅ (toLiftNormalizedTransportIso N).hom.toLiftHom :=
  Hom.isoOfNormalizedTransportHomEq <| by
    apply (cancel_mono (toLiftNormalizedTransportIso N).hom).mp
    rw [N.toLift.normalizationInv_normalizedTransportHom,
      toLiftNormalizedTransportIso_hom_naturality]

end TauCeti.EquivariantGroupoidLift
