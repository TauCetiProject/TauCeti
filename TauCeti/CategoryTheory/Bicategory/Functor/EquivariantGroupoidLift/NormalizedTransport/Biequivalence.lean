/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Biequivalence
public import TauCeti.CategoryTheory.Bicategory.FunctorBicategory.Equivalence
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.NormalizedTransport.Counit
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.NormalizedTransport.Unit

/-!
# The biequivalence between equivariant groupoid lifts and normalized transport

Fix a category `Γ`, a monoid `H` and a family `actions p` of categorical actions of `H` on
prescribed fiber categories. Every equivariant groupoid lift `L` is equivalent to the
reconstruction of its normalized transport through `L.normalizationEquivalence`, whose inverse
`L.normalizationInv : L.normalizedTransport.toLift ⟶ L` uses the inverse fiber equivalences of `L`
and their counits.

This file proves that `L.normalizationInv` is pseudonatural in morphisms of lifts `φ : L ⟶ L'`:
reconstructing the normalized comparison `φ.normalizedTransportHom` and composing with
`L'.normalizationInv` is isomorphic, by a compatible modification of lifts, to composing
`L.normalizationInv` with `φ`. Its components on the joint fibers are the inverse-fiber
comparisons `φ.inverseFiberIso`. Because compatible modifications between fixed morphisms of lifts
are unique, these naturality isomorphisms satisfy the unit, composition and `2`-naturality laws
automatically, assembling into a strong transformation `normalizationUnitInv actions`. Extending
it by the component adjoint equivalences `L.normalizationInv.equivalence` and taking the symmetric
equivalence produces the unit `normalizationUnitEquiv actions`; together with
`normalizationCounitEquiv actions` it yields the biequivalence

`normalizationBiequivalence actions :
  TauCeti.Biequivalence
    (EquivariantGroupoidLift Γ actions)
    (LocallyDiscrete (NormalizedTransport Γ actions))`

between coherent equivariant groupoid lifts and normalized transport data on the prescribed
fibers.

Normalizing `L.normalizationInv` gives the return comparison
`(toLiftNormalizedTransportIso L.normalizedTransport).hom` on the nose. Consequently, conjugating a
reconstructed morphism `α.toLiftHom` by `L.normalizationEquivalence.hom` and `L'.normalizationInv`
recovers `α` after normalization, two parallel morphisms of lifts admit a compatible modification
if and only if their normalizations coincide, and `(normalizationPseudofunctor actions).mapFunctor`
is an equivalence on every hom-category.

## Main declarations

* `TauCeti.EquivariantGroupoidLift.Hom.normalizationInvNaturality`: naturality of
  `normalizationInv` with respect to a morphism of lifts;
* `TauCeti.EquivariantGroupoidLift.normalizationUnitInv`,
  `TauCeti.EquivariantGroupoidLift.normalizationUnitHom`: the inverse and forward unit strong
  transformations between the identity of `EquivariantGroupoidLift Γ actions` and normalization
  followed by reconstruction;
* `TauCeti.EquivariantGroupoidLift.normalizationUnitEquiv`: the unit adjoint equivalence of
  pseudofunctors;
* `TauCeti.EquivariantGroupoidLift.normalizationBiequivalence`: the biequivalence between
  `EquivariantGroupoidLift Γ actions` and `LocallyDiscrete (NormalizedTransport Γ actions)`;
* `TauCeti.EquivariantGroupoidLift.normalizationInv_normalizedTransportHom`,
  `TauCeti.EquivariantGroupoidLift.liftNormalizedTransportHom`,
  `TauCeti.EquivariantGroupoidLift.lift_normalizedTransportHom`: the triangle identity for
  normalizing `normalizationInv` and the section construction on morphisms of normalized
  transports;
* `TauCeti.EquivariantGroupoidLift.Hom.isoOfNormalizedTransportHomEq`,
  `TauCeti.EquivariantGroupoidLift.Hom.nonempty_hom₂_iff`,
  `TauCeti.EquivariantGroupoidLift.normalizationHomEquivalence`: classification of `2`-morphisms
  and equivalence of hom-categories under normalization.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055), Chapter 4: strong transformations,
  modifications and biequivalences.
* Edward Frenkel,
  [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  Cambridge Studies in Advanced Mathematics 103 (2007): families of local categories over a
  parameter groupoid with equivariant fiber identifications.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory CategoryTheory.Prod Pseudofunctor.StrongTrans NormalizedTransport

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}

private lemma normalizationInv_fiberFunctorIso_hom_app (L : EquivariantGroupoidLift Γ actions)
    (p : Γ) (y : L.normalizedTransport.toLift.jointFiber p) :
    (L.normalizationInv.fiberFunctorIso p).hom.app y = (L.fiberEquivalence p).counit.app y := by
  rw [Hom.fiberFunctorIso_hom_app, L.normalizationInv_fiberIso_hom_as_app]
  rfl

namespace Hom

variable {L L' : EquivariantGroupoidLift Γ actions}

/-- Componentwise naturality of the inverse-fiber comparisons along a joint arrow `(g, a)`:
comparing inverse fibers at the target and applying the normalized transport comparison agrees
with applying the source normalization comparison, the joint naturality cell of `φ`, and the
inverse-fiber comparison at the source. -/
private lemma normalizationInvJointNaturality_app (φ : L ⟶ L') {p q : Γ} (g : p ⟶ q)
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
  dsimp only [NormalizedTransport.jointFunctor, normalizedTransport, transport_obj,
    Functor.comp_obj]
  rw [transportIso_hom_app, L'.normalizationJointIso_hom_app, L.normalizationJointIso_hom_app]
  simp only [Functor.map_comp, Category.assoc]
  -- Move the two target functor-inverse maps past `unitInv` to expose the unit cancellation.
  rw [(L'.fiberEquivalence q).unitInv_naturality_assoc,
    (L'.fiberEquivalence q).unitInv_naturality_assoc,
    φ.inverseFiberIso_hom_app_comp_unitInv_assoc]
  apply congrArg ((φ.jointFunctor q).map ((L.fiberEquivalence q).unitInv.app _) ≫ ·)
  -- Rewrite the equivariance of `inverseFiberIso` along `a` inside `L'.jointMap g`.
  rw [← Functor.map_comp_assoc (L'.jointMap g), ← φ.inverseFiberIso_actInverseIso p a x]
  simp only [Functor.map_comp, Category.assoc]
  -- Commute `jointMapIso` past `actInverseIso` on the left, and `mapComp'.inv` past
  -- `inverseFiberIso` on the right.
  have hjm := (φ.jointMapIso g).hom.naturality ((L.actInverseIso p a).hom.app x)
  dsimp only [Functor.comp_obj, Functor.comp_map, jointMap] at hjm ⊢
  rw [reassoc_of% hjm.symm]
  apply congrArg ((φ.jointFunctor q).map
    ((L.joint.map (g ×ₘ 𝟙 (SingleObj.star H)).toLoc).toFunctor.map
      ((L.actInverseIso p a).hom.app x)) ≫ ·)
  let hfac : (𝟙 p ×ₘ a).toLoc ≫ (g ×ₘ 𝟙 (SingleObj.star H)).toLoc = (g ×ₘ a).toLoc := by
    apply congrArg Quiver.Hom.toLoc
    exact Prod.ext (Category.id_comp _) (Category.comp_id _)
  have hc' := (L'.joint.mapComp' (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
    (g ×ₘ a).toLoc hfac).inv.toNatTrans.naturality ((φ.inverseFiberIso p).hom.app x)
  dsimp only [Cat.Hom.comp_toFunctor, Functor.comp_obj, Functor.comp_map] at hc'
  dsimp only [jointAct]
  rw [hc']
  -- Combine the remaining naturality cells of `φ.joint` along the factored joint arrow.
  have hcomp := φ.joint.naturality_comp'_hom_app (𝟙 p ×ₘ a).toLoc
    (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ a).toLoc hfac
    ((L.fiberEquivalence p).inverse.obj x)
  rw [hcomp]
  simp only [Category.assoc]
  dsimp only [jointFunctor]
  rw [← Functor.map_comp_assoc]
  simp [jointMapIso_hom_app, jointActIso_hom_app, Cat.Hom.inv_hom_id_toNatTrans_app]

private lemma isoMk_trans_leftUnitor_symm_hom_app {C D : Type w} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (e : G ≅ F) (x : C) :
    (Cat.Hom.isoMk e ≪≫ (λ_ F.toCatHom).symm).hom.toNatTrans.app x = e.hom.app x := by
  simp

/-- The inverse naturality isomorphism `(L.normalizationInv ≫ φ).joint ≅
(φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv).joint` on joint pseudofunctors, with
components `φ.inverseFiberIso`. -/
noncomputable def normalizationInvJointSymmIso (φ : L ⟶ L') :
    (L.normalizationInv ≫ φ).joint ≅
      ((φ.normalizedTransportHom.toLiftHom :
          L.normalizedTransport.toLift ⟶ L'.normalizedTransport.toLift) ≫
        L'.normalizationInv).joint :=
  Pseudofunctor.StrongTrans.isoMk
    (fun X ↦ Cat.Hom.isoMk (φ.inverseFiberIso X.as.1) ≪≫
      (λ_ (L'.fiberEquivalence X.as.1).inverse.toCatHom).symm)
    (fun {X Y} f ↦ by
      obtain ⟨p, ⟨⟩⟩ := X
      obtain ⟨q, ⟨⟩⟩ := Y
      refine Cat.whiskerLeft_comp_eq_comp_whiskerRight _ _ _ _ (fun (x : fiber actions p) ↦ ?_)
      let y : fiber actions q := (L.normalizedTransport.jointFunctor f.as).obj x
      have hq := isoMk_trans_leftUnitor_symm_hom_app (φ.inverseFiberIso q) y
      have hp := isoMk_trans_leftUnitor_symm_hom_app (φ.inverseFiberIso p) x
      have h₁ : (((φ.normalizedTransportHom.toLiftHom :
            L.normalizedTransport.toLift ⟶ L'.normalizedTransport.toLift) ≫
            L'.normalizationInv).joint.naturality f).hom.toNatTrans.app x =
          (L'.fiberEquivalence q).inverse.map
            ((φ.transportIso f.as.1).hom.app ((act actions p f.as.2).obj x)) ≫
            (L'.normalizationJointIso f.as).hom.app x :=
        (Pseudofunctor.StrongTrans.comp_naturality_hom_app
          (φ.normalizedTransportHom.toLiftHom :
            L.normalizedTransport.toLift ⟶ L'.normalizedTransport.toLift).joint
          L'.normalizationInv.joint f x).trans
          (congrArg₂ (· ≫ ·)
            (congrArg (L'.fiberEquivalence q).inverse.map
              ((NormalizedTransport.Hom.jointHom_naturality_hom_app
                φ.normalizedTransportHom f x).trans
                (congrArg (fun i ↦ i.hom.app ((act actions p f.as.2).obj x))
                  (normalizedTransportHom_transportIso φ f.as.1))))
            (L'.normalizationJointInv_naturality_hom_app f x))
      have h₂ : ((L.normalizationInv ≫ φ).joint.naturality f).hom.toNatTrans.app x =
          (φ.jointFunctor q).map ((L.normalizationJointIso f.as).hom.app x) ≫
            (φ.joint.naturality f).hom.toNatTrans.app
              ((L.fiberEquivalence p).inverse.obj x) :=
        (Pseudofunctor.StrongTrans.comp_naturality_hom_app
          L.normalizationInv.joint φ.joint f x).trans
          (congrArg (· ≫ _)
            (congrArg (φ.jointFunctor q).map (L.normalizationJointInv_naturality_hom_app f x)))
      exact (congrArg₂ (· ≫ ·) hq h₁).trans
        ((φ.normalizationInvJointNaturality_app f.as.1 f.as.2 x).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg₂ (· ≫ ·) h₂ (congrArg (L'.joint.map f).toFunctor.map hp)).symm)))

@[simp]
lemma normalizationInvJointSymmIso_hom_as_app (φ : L ⟶ L')
    (X : LocallyDiscrete (Γ × SingleObj H)) :
    (normalizationInvJointSymmIso φ).hom.as.app X =
      (Cat.Hom.isoMk (φ.inverseFiberIso X.as.1)).hom ≫
        (λ_ (L'.fiberEquivalence X.as.1).inverse.toCatHom).inv :=
  (rfl)

@[simp]
lemma normalizationInvJointSymmIso_inv_as_app (φ : L ⟶ L')
    (X : LocallyDiscrete (Γ × SingleObj H)) :
    (normalizationInvJointSymmIso φ).inv.as.app X =
      (λ_ (L'.fiberEquivalence X.as.1).inverse.toCatHom).hom ≫
        (Cat.Hom.isoMk (φ.inverseFiberIso X.as.1)).inv :=
  (rfl)

/-- Naturality of `normalizationInv` with respect to a morphism of lifts `φ : L ⟶ L'`:
reconstructing `φ.normalizedTransportHom` and composing with `L'.normalizationInv` is isomorphic
to composing `L.normalizationInv` with `φ`, via the inverse-fiber comparisons of `φ`. -/
@[expose] noncomputable def normalizationInvNaturality (φ : L ⟶ L') :
    (φ.normalizedTransportHom.toLiftHom :
      L.normalizedTransport.toLift ⟶ L'.normalizedTransport.toLift) ≫ L'.normalizationInv ≅
    L.normalizationInv ≫ φ :=
  (isoMk (normalizationInvJointSymmIso φ) (fun p a ↦ by
    obtain ⟨u⟩ := a
    obtain rfl : u = SingleObj.star H := Subsingleton.elim _ _
    -- Give restricted components their joint-fiber endpoints before simplifying in `Cat`.
    let ψ₁ : L.normalizedTransport.toLift ⟶ L' := L.normalizationInv ≫ φ
    let ψ₂ : L.normalizedTransport.toLift ⟶ L' :=
      (φ.normalizedTransportHom.toLiftHom :
        L.normalizedTransport.toLift ⟶ L'.normalizedTransport.toLift) ≫ L'.normalizationInv
    let F : L.normalizedTransport.toLift.jointFiber p ⟶ L'.jointFiber p :=
      ψ₁.joint.app ⟨(p, SingleObj.star H)⟩
    let G : L.normalizedTransport.toLift.jointFiber p ⟶ L'.jointFiber p :=
      ψ₂.joint.app ⟨(p, SingleObj.star H)⟩
    let E' : L'.jointFiber p ⟶ fiber actions p := (L'.comparison p).app ⟨SingleObj.star H⟩
    let E : L.normalizedTransport.toLift.jointFiber p ⟶ fiber actions p :=
      (L.normalizedTransport.toLift.comparison p).app ⟨SingleObj.star H⟩
    let α : F ⟶ G := (normalizationInvJointSymmIso φ).hom.as.app ⟨(p, SingleObj.star H)⟩
    let β : G ≫ E' ⟶ E := (ψ₂.fiberIso p).hom.as.app ⟨SingleObj.star H⟩
    let γ : F ≫ E' ⟶ E := (ψ₁.fiberIso p).hom.as.app ⟨SingleObj.star H⟩
    change α ▷ E' ≫ β = γ
    apply Cat.Hom₂.ext
    apply NatTrans.ext
    funext x
    simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app]
    have hα : α.toNatTrans.app x = (φ.inverseFiberIso p).hom.app x :=
      isoMk_trans_leftUnitor_symm_hom_app (φ.inverseFiberIso p) x
    have hβ : β.toNatTrans.app x = (L'.fiberEquivalence p).counit.app x := by
      refine (congrArg (fun i ↦ (i.hom.as.app ⟨SingleObj.star H⟩).toNatTrans.app x)
        (EquivariantGroupoidLift.comp_fiberIso
          (φ.normalizedTransportHom.toLiftHom :
            L.normalizedTransport.toLift ⟶ L'.normalizedTransport.toLift)
          L'.normalizationInv p)).trans ?_
      refine (fiberFunctorIso_hom_app _ p x).symm.trans ?_
      rw [comp_fiberFunctorIso_hom_app, L'.normalizationInv_fiberFunctorIso_hom_app,
        fiberFunctorIso_hom_app, NormalizedTransport.Hom.toLiftHom_fiberIso_hom_as_app]
      exact Category.comp_id ((L'.fiberEquivalence p).counit.app (x : fiber actions p))
    have hγ : γ.toNatTrans.app x =
        (φ.fiberFunctorIso p).hom.app ((L.fiberEquivalence p).inverse.obj x) ≫
          (L.fiberEquivalence p).counit.app x := by
      refine (congrArg (fun i ↦ (i.hom.as.app ⟨SingleObj.star H⟩).toNatTrans.app x)
        (EquivariantGroupoidLift.comp_fiberIso L.normalizationInv φ p)).trans ?_
      refine (fiberFunctorIso_hom_app _ p x).symm.trans ?_
      exact (comp_fiberFunctorIso_hom_app L.normalizationInv φ p x).trans
        (congrArg (_ ≫ ·) (L.normalizationInv_fiberFunctorIso_hom_app p x))
    exact (congrArg₂ (· ≫ ·) (congrArg E'.toFunctor.map hα) hβ).trans
      ((φ.functor_map_inverseFiberIso_hom_app_comp_counit p x).trans hγ.symm))).symm

lemma normalizationInvNaturality_hom_joint_as_app (φ : L ⟶ L')
    (X : LocallyDiscrete (Γ × SingleObj H)) :
    (normalizationInvNaturality φ).hom.joint.as.app X =
      (λ_ (L'.fiberEquivalence X.as.1).inverse.toCatHom).hom ≫
        (Cat.Hom.isoMk (φ.inverseFiberIso X.as.1)).inv := by
  simp [normalizationInvNaturality]
  rfl

lemma normalizationInvNaturality_inv_joint_as_app (φ : L ⟶ L')
    (X : LocallyDiscrete (Γ × SingleObj H)) :
    (normalizationInvNaturality φ).inv.joint.as.app X =
      (Cat.Hom.isoMk (φ.inverseFiberIso X.as.1)).hom ≫
        (λ_ (L'.fiberEquivalence X.as.1).inverse.toCatHom).inv := by
  simp [normalizationInvNaturality]
  rfl

end Hom

section Biequivalence

variable (actions)

/-- The strong transformation from normalization followed by reconstruction to the identity
pseudofunctor of `EquivariantGroupoidLift Γ actions`, with components `L.normalizationInv` and
naturality cells `Hom.normalizationInvNaturality`. Its coherence axioms hold by uniqueness of
compatible modifications of lifts. -/
@[expose] noncomputable def normalizationUnitInv :
    (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) ⟶
      Pseudofunctor.id (EquivariantGroupoidLift Γ actions) where
  app L := L.normalizationInv
  naturality φ := Hom.normalizationInvNaturality φ
  naturality_naturality _ := Subsingleton.elim _ _
  naturality_id _ := Subsingleton.elim _ _
  naturality_comp _ _ := Subsingleton.elim _ _

@[simp]
lemma normalizationUnitInv_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitInv actions).app L = L.normalizationInv :=
  (rfl)

@[simp]
lemma normalizationUnitInv_naturality {L L' : EquivariantGroupoidLift Γ actions} (φ : L ⟶ L') :
    (normalizationUnitInv actions).naturality φ = Hom.normalizationInvNaturality φ :=
  (rfl)

/-- The adjoint equivalence from normalization followed by reconstruction to the identity
pseudofunctor, extending `normalizationUnitInv` by the component adjoint equivalences
`L.normalizationInv.equivalence`. -/
@[expose] noncomputable def normalizationUnitSymmEquiv :
    (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) ≌
      Pseudofunctor.id (EquivariantGroupoidLift Γ actions) :=
  (normalizationUnitInv actions).equivalenceOfComponents
    (fun L ↦ L.normalizationEquivalence.hom)
    (fun L ↦ L.normalizationInv.equivalence.unit)
    (fun L ↦ L.normalizationInv.equivalence.counit)
    (fun L ↦ L.normalizationInv.equivalence.left_triangle)

@[simp]
lemma normalizationUnitSymmEquiv_hom :
    (normalizationUnitSymmEquiv actions).hom = normalizationUnitInv actions :=
  (rfl)

/-- The forward unit strong transformation from the identity pseudofunctor of
`EquivariantGroupoidLift Γ actions` to normalization followed by reconstruction, with components
`L.normalizationEquivalence.hom`. -/
@[expose] noncomputable def normalizationUnitHom :
    Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ⟶
      (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) :=
  (normalizationUnitSymmEquiv actions).inv

@[simp]
lemma normalizationUnitSymmEquiv_inv :
    (normalizationUnitSymmEquiv actions).inv = normalizationUnitHom actions :=
  (rfl)

@[simp]
lemma normalizationUnitHom_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitHom actions).app L = L.normalizationEquivalence.hom :=
  (rfl)

/-- The unit adjoint equivalence of normalization: the identity pseudofunctor of
`EquivariantGroupoidLift Γ actions` is equivalent to normalization followed by reconstruction. -/
@[expose] noncomputable def normalizationUnitEquiv :
    Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ≌
      (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) :=
  (normalizationUnitSymmEquiv actions).symm

@[simp]
lemma normalizationUnitEquiv_hom :
    (normalizationUnitEquiv actions).hom = normalizationUnitHom actions :=
  (rfl)

@[simp]
lemma normalizationUnitEquiv_inv :
    (normalizationUnitEquiv actions).inv = normalizationUnitInv actions :=
  (rfl)

-- Keep the dependent unit and counit modification equations named, matching `Unit.lean`.
lemma normalizationUnitEquiv_unit_hom_as_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitEquiv actions).unit.hom.as.app L = L.normalizationEquivalence.unit.hom :=
  (rfl)

lemma normalizationUnitEquiv_unit_inv_as_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitEquiv actions).unit.inv.as.app L = L.normalizationEquivalence.unit.inv :=
  (rfl)

lemma normalizationUnitEquiv_counit_hom_as_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitEquiv actions).counit.hom.as.app L = L.normalizationEquivalence.counit.hom :=
  Subsingleton.elim _ _

lemma normalizationUnitEquiv_counit_inv_as_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitEquiv actions).counit.inv.as.app L = L.normalizationEquivalence.counit.inv :=
  Subsingleton.elim _ _

/-- The biequivalence between the bicategory of coherent equivariant groupoid lifts and the locally
discrete bicategory of normalized transports on the prescribed fibers. -/
@[expose] noncomputable def normalizationBiequivalence :
    TauCeti.Biequivalence
      (EquivariantGroupoidLift Γ actions)
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

@[simp]
lemma normalizationBiequivalence_unitEquiv :
    (normalizationBiequivalence actions).unitEquiv = normalizationUnitEquiv actions :=
  (rfl)

@[simp]
lemma normalizationBiequivalence_counitEquiv :
    (normalizationBiequivalence actions).counitEquiv = normalizationCounitEquiv actions :=
  (rfl)

end Biequivalence

/-! ### Triangle identities and classification of lift morphisms -/

private lemma normalizationInv_fiberFunctorIso_inv_app (L : EquivariantGroupoidLift Γ actions)
    (p : Γ) (y : L.normalizedTransport.toLift.jointFiber p) :
    (L.normalizationInv.fiberFunctorIso p).inv.app y =
      (L.fiberEquivalence p).counitInv.app y := by
  rw [Hom.fiberFunctorIso_inv_app, L.normalizationInv_fiberIso_inv_as_app]
  rfl

private lemma normalizationInv_jointMapIso_hom_app (L : EquivariantGroupoidLift Γ actions)
    {p q : Γ} (g : p ⟶ q) (y : L.normalizedTransport.toLift.jointFiber p) :
    (L.normalizationInv.jointMapIso g).hom.app y =
      (L.normalizationJointIso (g ×ₘ 𝟙 (SingleObj.star H))).hom.app y := by
  rw [Hom.jointMapIso_hom_app]
  exact L.normalizationJointInv_naturality_hom_app (g ×ₘ 𝟙 (SingleObj.star H)).toLoc y

/-- The inverse-fiber comparison of `L.normalizationInv` maps the counit of the reconstructed fiber
equivalence by the inverse fiber equivalence of `L`. -/
lemma normalizationInv_inverseFiberIso_hom_app (L : EquivariantGroupoidLift Γ actions) (p : Γ)
    (x : fiber actions p) :
    (L.normalizationInv.inverseFiberIso p).hom.app x =
      (L.fiberEquivalence p).inverse.map
        ((L.normalizedTransport.toLift.fiberEquivalence p).counit.app x :
          (L.normalizedTransport.toLift.fiberEquivalence p).inverse.obj x ⟶ x) := by
  let y : L.normalizedTransport.toLift.jointFiber p :=
    (L.normalizedTransport.toLift.fiberEquivalence p).inverse.obj x
  let ε : (y : fiber actions p) ⟶ x :=
    (L.normalizedTransport.toLift.fiberEquivalence p).counit.app x
  apply (L.fiberEquivalence p).functor.map_injective
  apply (cancel_mono ((L.fiberEquivalence p).counit.app x)).mp
  rw [L.normalizationInv.functor_map_inverseFiberIso_hom_app_comp_counit]
  have hc := (L.fiberEquivalence p).counit.naturality ε
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hc
  exact (congrArg (· ≫ ε) (L.normalizationInv_fiberFunctorIso_hom_app p y)).trans hc.symm

private lemma normalizationInv_transportIso_hom_app (L : EquivariantGroupoidLift Γ actions)
    {p q : Γ} (g : p ⟶ q) (x : fiber actions p) :
    (L.normalizationInv.transportIso g).hom.app x =
      let y : fiber actions p := (L.normalizedTransport.toLift.fiberEquivalence p).inverse.obj x
      let ε : y ⟶ x := (L.normalizedTransport.toLift.fiberEquivalence p).counit.app x
      (L.fiberEquivalence q).counitInv.app
          ((L.normalizedTransport.jointFunctor (g ×ₘ 𝟙 (SingleObj.star H))).obj y) ≫
        (L.fiberEquivalence q).functor.map
          ((L.normalizationJointIso (g ×ₘ 𝟙 (SingleObj.star H))).hom.app y) ≫
        (L.fiberEquivalence q).functor.map
          ((L.jointMap g).map ((L.fiberEquivalence p).inverse.map ε)) := by
  rw [Hom.transportIso_hom_app, L.normalizationInv_fiberFunctorIso_inv_app,
    L.normalizationInv_jointMapIso_hom_app]
  erw [L.normalizationInv_inverseFiberIso_hom_app]
  rfl

/-- Normalizing `L.normalizationInv` gives the canonical return comparison
`(toLiftNormalizedTransportIso L.normalizedTransport).hom`. -/
@[simp]
lemma normalizationInv_normalizedTransportHom (L : EquivariantGroupoidLift Γ actions) :
    L.normalizationInv.normalizedTransportHom =
      (toLiftNormalizedTransportIso L.normalizedTransport).hom := by
  refine NormalizedTransport.Hom.ext fun p q g ↦ Iso.ext (NatTrans.ext (funext fun x ↦ ?_))
  let y : fiber actions p := (L.normalizedTransport.toLift.fiberEquivalence p).inverse.obj x
  let ε : y ⟶ x := (L.normalizedTransport.toLift.fiberEquivalence p).counit.app x
  rw [Hom.normalizedTransportHom_transportIso, toLiftNormalizedTransportIso_hom_transportIso,
    L.normalizationInv_transportIso_hom_app, L.normalizedTransport.toLiftTransportIso_hom_app]
  change (L.fiberEquivalence q).counitInv.app
        ((L.normalizedTransport.jointFunctor (g ×ₘ 𝟙 (SingleObj.star H))).obj y) ≫
      (L.fiberEquivalence q).functor.map
        ((L.normalizationJointIso (g ×ₘ 𝟙 (SingleObj.star H))).hom.app y) ≫
      (L.fiberEquivalence q).functor.map
        ((L.jointMap g).map ((L.fiberEquivalence p).inverse.map ε)) =
    (L.normalizedTransport.transport g).map ((act actions p (𝟙 (SingleObj.star H))).map ε) ≫
      (L.normalizedTransport.transport g).map ((actId actions p).hom.app x)
  -- Simplify the left-unitor compositor at `(𝟙 p, 𝟙 ⋆)` and combine it with `actInverseIso_actId`.
  have hmid : (L.jointMap g).map ((L.actInverseIso p (𝟙 (SingleObj.star H))).hom.app y) ≫
        (L.joint.mapComp' (𝟙 p ×ₘ 𝟙 (SingleObj.star H)).toLoc
          (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
          (by
            apply congrArg Quiver.Hom.toLoc
            exact Prod.ext (Category.id_comp _) (Category.comp_id _))).inv.toNatTrans.app
            ((L.fiberEquivalence p).inverse.obj y) =
      (L.jointMap g).map ((L.fiberEquivalence p).inverse.map ((actId actions p).hom.app y)) := by
    have h := L.joint.mapComp'_id_comp_inv_app (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
      ((L.fiberEquivalence p).inverse.obj y)
    have ha := L.actInverseIso_actId p y
    simp only [jointAct, jointMap, ← prod_id, Quiver.Hom.id_toLoc,
      Cat.Hom.comp_toFunctor, Functor.comp_obj] at h ⊢
    simp only [jointMapId_hom_app, ← prod_id, Quiver.Hom.id_toLoc,
      Pseudofunctor.mapId'_eq_mapId] at ha
    rw [h, ← Functor.map_comp]
    exact congrArg (L.joint.map (g ×ₘ 𝟙 (SingleObj.star H)).toLoc).toFunctor.map ha
  have hj : (L.normalizationJointIso (g ×ₘ 𝟙 (SingleObj.star H))).hom.app y =
      (L.fiberEquivalence q).unitInv.app
        ((L.jointMap g).obj
          ((L.fiberEquivalence p).inverse.obj ((act actions p (𝟙 (SingleObj.star H))).obj y))) ≫
      (L.jointMap g).map ((L.fiberEquivalence p).inverse.map ((actId actions p).hom.app y)) :=
    (L.normalizationJointIso_hom_app (g ×ₘ 𝟙 (SingleObj.star H)) y).trans (congrArg (_ ≫ ·) hmid)
  rw [hj]
  dsimp only [NormalizedTransport.jointFunctor, normalizedTransport, transport_obj,
    transport_map, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  -- Cancel the target counit-unit zigzag and commute `actId` past `ε`.
  erw [← (L.fiberEquivalence q).counit_app_functor]
  simp only [Iso.inv_hom_id_app_assoc, ← Functor.map_comp, (actId actions p).hom.naturality ε,
    Functor.id_map]

/-- Normalizing the chosen inverse `L.normalizationInv.equivalence.inv` gives the inverse return
comparison `(toLiftNormalizedTransportIso L.normalizedTransport).inv`. -/
@[simp]
lemma normalizationInv_equivalence_inv_normalizedTransportHom
    (L : EquivariantGroupoidLift Γ actions) :
    L.normalizationInv.equivalence.inv.normalizedTransportHom =
      (toLiftNormalizedTransportIso L.normalizedTransport).inv := by
  have h := L.normalizationInv.equivalence.counit.hom.normalizedTransportHom_eq
  rw [Hom.id_normalizedTransportHom, Hom.comp_normalizedTransportHom,
    Hom.equivalence_hom, L.normalizationInv_normalizedTransportHom] at h
  exact (cancel_mono (toLiftNormalizedTransportIso L.normalizedTransport).hom).mp
    (h.trans (toLiftNormalizedTransportIso L.normalizedTransport).inv_hom_id.symm)

/-- Normalizing the forward equivalence `L.normalizationEquivalence.hom` gives the inverse return
comparison `(toLiftNormalizedTransportIso L.normalizedTransport).inv`. -/
lemma normalizationEquivalence_hom_normalizedTransportHom
    (L : EquivariantGroupoidLift Γ actions) :
    L.normalizationEquivalence.hom.normalizedTransportHom =
      (toLiftNormalizedTransportIso L.normalizedTransport).inv := by
  simp

/-- Conjugating a reconstructed comparison `α.toLiftHom` by `L.normalizationEquivalence.hom` and
`L'.normalizationInv` produces a morphism of lifts whose normalization is `α`. -/
lemma lift_normalizedTransportHom {L L' : EquivariantGroupoidLift Γ actions}
    (α : L.normalizedTransport ⟶ L'.normalizedTransport) :
    (L.normalizationEquivalence.hom ≫
      (α.toLiftHom : L.normalizedTransport.toLift ⟶ L'.normalizedTransport.toLift) ≫
      L'.normalizationInv).normalizedTransportHom = α := by
  rw [Hom.comp_normalizedTransportHom, Hom.comp_normalizedTransportHom,
    L.normalizationEquivalence_hom_normalizedTransportHom,
    L'.normalizationInv_normalizedTransportHom,
    toLiftNormalizedTransportIso_hom_naturality, Iso.inv_hom_id_assoc]

/-- Lift a morphism of normalized transports `α : L.normalizedTransport ⟶ L'.normalizedTransport`
to a morphism of equivariant lifts `L ⟶ L'` by conjugating `α.toLiftHom` with the unit
equivalences at `L` and `L'`. -/
noncomputable def liftNormalizedTransportHom {L L' : EquivariantGroupoidLift Γ actions}
    (α : L.normalizedTransport ⟶ L'.normalizedTransport) : L ⟶ L' :=
  L.normalizationEquivalence.hom ≫
    (α.toLiftHom : L.normalizedTransport.toLift ⟶ L'.normalizedTransport.toLift) ≫
    L'.normalizationInv

lemma liftNormalizedTransportHom_eq {L L' : EquivariantGroupoidLift Γ actions}
    (α : L.normalizedTransport ⟶ L'.normalizedTransport) :
    liftNormalizedTransportHom α =
      L.normalizationEquivalence.hom ≫
        (α.toLiftHom : L.normalizedTransport.toLift ⟶ L'.normalizedTransport.toLift) ≫
        L'.normalizationInv :=
  (rfl)

@[simp]
lemma liftNormalizedTransportHom_normalizedTransportHom
    {L L' : EquivariantGroupoidLift Γ actions}
    (α : L.normalizedTransport ⟶ L'.normalizedTransport) :
    (liftNormalizedTransportHom α).normalizedTransportHom = α :=
  lift_normalizedTransportHom α

namespace Hom

variable {L L' : EquivariantGroupoidLift Γ actions}

private def cancelLeftEquivIso {B : Type*} [Bicategory B] {a b c : B} (e : a ≌ b)
    {f g : b ⟶ c} (i : e.hom ≫ f ≅ e.hom ≫ g) : f ≅ g :=
  (λ_ f).symm ≪≫ whiskerRightIso e.counit.symm f ≪≫ α_ e.inv e.hom f ≪≫
    whiskerLeftIso e.inv i ≪≫ (α_ e.inv e.hom g).symm ≪≫ whiskerRightIso e.counit g ≪≫ λ_ g

/-- Two parallel morphisms of lifts with equal normalizations are isomorphic by a unique compatible
modification, obtained by cancelling `L.normalizationInv` across `normalizationInvNaturality`. -/
noncomputable def isoOfNormalizedTransportHomEq {φ ψ : L ⟶ L'}
    (h : φ.normalizedTransportHom = ψ.normalizedTransportHom) : φ ≅ ψ :=
  cancelLeftEquivIso L.normalizationInv.equivalence
    ((normalizationInvNaturality φ).symm ≪≫
      whiskerRightIso
        (eqToIso (congrArg
          (fun α : L.normalizedTransport ⟶ L'.normalizedTransport ↦
            (α.toLiftHom : L.normalizedTransport.toLift ⟶ L'.normalizedTransport.toLift)) h))
        L'.normalizationInv ≪≫
      normalizationInvNaturality ψ)

/-- Two parallel morphisms of equivariant groupoid lifts admit a compatible modification if and
only if they induce the same comparison of normalized transports on the prescribed fibers. -/
lemma nonempty_hom₂_iff {φ ψ : L ⟶ L'} :
    Nonempty (φ ⟶ ψ) ↔ φ.normalizedTransportHom = ψ.normalizedTransportHom :=
  ⟨fun ⟨Θ⟩ ↦ Θ.normalizedTransportHom_eq, fun h ↦ ⟨(isoOfNormalizedTransportHomEq h).hom⟩⟩

end Hom

private def conjugateHomFunctor {B : Type*} [Bicategory B] {a₀ a b b₀ : B}
    (u : a₀ ⟶ a) (v : b ⟶ b₀) : (a ⟶ b) ⥤ (a₀ ⟶ b₀) where
  obj f := u ≫ f ≫ v
  map η := u ◁ (η ▷ v)

/-- The inverse functor on hom-categories sending a morphism of normalized transports to the
reconstructed lift morphism conjugated by `normalizationEquivalence.hom` and `normalizationInv`. -/
noncomputable def normalizationHomInverse (L L' : EquivariantGroupoidLift Γ actions) :
    ((normalizationPseudofunctor actions).obj L ⟶
      (normalizationPseudofunctor actions).obj L') ⥤ (L ⟶ L') :=
  (reconstructionPseudofunctor actions).mapFunctor
      ((normalizationPseudofunctor actions).obj L) ((normalizationPseudofunctor actions).obj L') ⋙
    conjugateHomFunctor L.normalizationEquivalence.hom L'.normalizationInv

@[simp]
lemma normalizationHomInverse_obj (L L' : EquivariantGroupoidLift Γ actions)
    (α : (normalizationPseudofunctor actions).obj L ⟶
      (normalizationPseudofunctor actions).obj L') :
    (normalizationHomInverse L L').obj α = liftNormalizedTransportHom α.as :=
  (rfl)

private lemma mapFunctor_normalizationHomInverse_obj (L L' : EquivariantGroupoidLift Γ actions)
    (α : (normalizationPseudofunctor actions).obj L ⟶
      (normalizationPseudofunctor actions).obj L') :
    ((normalizationPseudofunctor actions).mapFunctor L L').obj
        ((normalizationHomInverse L L').obj α) = α :=
  congrArg Quiver.Hom.toLoc (liftNormalizedTransportHom_normalizedTransportHom α.as)

/-- Normalization induces an equivalence of categories between the groupoid of morphisms `L ⟶ L'`
and the discrete category of comparisons `L.normalizedTransport ⟶ L'.normalizedTransport`. -/
noncomputable def normalizationHomEquivalence
    (L L' : EquivariantGroupoidLift Γ actions) :
    (L ⟶ L') ≌
      ((normalizationPseudofunctor actions).obj L ⟶
        (normalizationPseudofunctor actions).obj L') where
  functor := (normalizationPseudofunctor actions).mapFunctor L L'
  inverse := normalizationHomInverse L L'
  unitIso := NatIso.ofComponents
    (fun φ ↦ Hom.isoOfNormalizedTransportHomEq
      (liftNormalizedTransportHom_normalizedTransportHom φ.normalizedTransportHom).symm)
    (fun _ ↦ Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents
    (fun α ↦ eqToIso (mapFunctor_normalizationHomInverse_obj L L' α))
    (fun _ ↦ Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

@[simp]
lemma normalizationHomEquivalence_functor (L L' : EquivariantGroupoidLift Γ actions) :
    (normalizationHomEquivalence L L').functor =
      (normalizationPseudofunctor actions).mapFunctor L L' :=
  (rfl)

@[simp]
lemma normalizationHomEquivalence_inverse (L L' : EquivariantGroupoidLift Γ actions) :
    (normalizationHomEquivalence L L').inverse = normalizationHomInverse L L' :=
  (rfl)

/-- Normalization is locally an equivalence of categories on every hom-category of equivariant
groupoid lifts. -/
instance isEquivalence_normalizationPseudofunctor_mapFunctor
    (L L' : EquivariantGroupoidLift Γ actions) :
    ((normalizationPseudofunctor actions).mapFunctor L L').IsEquivalence :=
  (normalizationHomEquivalence L L').isEquivalence_functor

end TauCeti.EquivariantGroupoidLift
