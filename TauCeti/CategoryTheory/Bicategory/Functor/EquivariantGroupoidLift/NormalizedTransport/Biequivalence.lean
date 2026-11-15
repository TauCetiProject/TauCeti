/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Biequivalence
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.NormalizedTransport.Counit
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.NormalizedTransport.Unit
import Mathlib.CategoryTheory.Bicategory.Functor.Cat

/-!
# The biequivalence of equivariant lifts with normalized transport

Every lift `L` is equivalent to the reconstruction `L.normalizedTransport.toLift` of its
normalized transport through `L.normalizationEquivalence`, whose inverse morphism is
`L.normalizationInv : L.normalizedTransport.toLift ⟶ L`. Here we prove that these comparisons are
pseudonatural in lift morphisms `φ : L ⟶ L'` and assemble them with `normalizationCounitEquiv`
into a biequivalence between the bicategory of equivariant lifts and the locally discrete
bicategory of normalized transports.

Specifically, for `φ : L ⟶ L'`, the inverse-fiber comparisons `φ.inverseFiberIso` intertwine the
joint comparisons `normalizationJointIso` with `φ.transportIso` and the joint naturality of `φ`,
and their action-compatible counits satisfy the fiber modification condition. This yields an
invertible compatible modification

`φ.normalizationInvIso :
  φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv ≅ L.normalizationInv ≫ φ`

and, by pasting with the unit of `L.normalizationEquivalence` and counit of
`L'.normalizationEquivalence`, the forward naturality modification

`φ.normalizationHomIso :
  φ ≫ L'.normalizationEquivalence.hom ≅
    L.normalizationEquivalence.hom ≫ φ.normalizedTransportHom.toLiftHom`.

Because compatible modifications between parallel lift morphisms are unique and invertible, and
every morphism of lifts is already an equivalence, no restriction to a sub-bicategory is needed:
these modifications assemble directly into strong transformations `normalizationUnitInv` and
`normalizationUnitHom` and an adjoint equivalence

`normalizationUnitEquiv actions :
  Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ≌
    (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions)`,

giving `normalizationBiequivalence actions`.

We also prove the coherent triangle identities relating the unit and counit comparisons:
normalizing `L.normalizationInv` recovers the counit isomorphism
`toLiftNormalizedTransportIso L.normalizedTransport`, and reconstructing the counit isomorphism of
any normalized transport `N` is isomorphic to `N.toLift.normalizationInv`. Consequently,
normalization and reconstruction induce equivalences on all hom-categories, two parallel lift
morphisms admit a compatible modification precisely when they induce the same comparison of
normalized transports, and two lifts are equivalent precisely when their normalized transports are
isomorphic.

## Main declarations

* `TauCeti.EquivariantGroupoidLift.Hom.inverseFiberIso_normalizationJointIso`: the inverse-fiber
  comparisons intertwine `normalizationJointIso` with `transportIso` and joint naturality;
* `TauCeti.EquivariantGroupoidLift.Hom.normalizationInvIso`,
  `TauCeti.EquivariantGroupoidLift.Hom.normalizationHomIso`: the naturality compatible
  modifications of `normalizationInv` and `normalizationEquivalence.hom`;
* `TauCeti.EquivariantGroupoidLift.normalizationUnitHom`,
  `TauCeti.EquivariantGroupoidLift.normalizationUnitInv`,
  `TauCeti.EquivariantGroupoidLift.normalizationUnitEquiv`: the unit strong transformations and
  equivalence of pseudofunctors;
* `TauCeti.EquivariantGroupoidLift.normalizationBiequivalence`: the biequivalence between
  `EquivariantGroupoidLift Γ actions` and `LocallyDiscrete (NormalizedTransport Γ actions)`;
* `TauCeti.EquivariantGroupoidLift.normalizationInv_normalizedTransportHom`,
  `TauCeti.EquivariantGroupoidLift.NormalizedTransport.toLiftNormalizedTransportIsoHomIso`: the
  two triangle comparisons of the biequivalence;
* `TauCeti.EquivariantGroupoidLift.Hom.isoOfNormalizedTransportHomEq`,
  `TauCeti.EquivariantGroupoidLift.Hom.nonempty_hom₂_iff`: compatible modifications between lift
  morphisms correspond to equalities of normalized transport comparisons;
* `TauCeti.EquivariantGroupoidLift.isEquivalence_normalizationPseudofunctor_mapFunctor`,
  `TauCeti.EquivariantGroupoidLift.isEquivalence_reconstructionPseudofunctor_mapFunctor`,
  `TauCeti.EquivariantGroupoidLift.normalizationMapEquivalence`,
  `TauCeti.EquivariantGroupoidLift.reconstructionMapEquivalence`: local equivalence instances and
  bundled equivalences on hom-categories induced by normalization and reconstruction;
* `TauCeti.EquivariantGroupoidLift.nonempty_equivalence_iff`: two equivariant lifts are equivalent
  if and only if their normalized transports are isomorphic.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055), Chapter 4: strong transformations,
  modifications and biequivalences.
* Edward Frenkel,
  [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  Cambridge Studies in Advanced Mathematics 103 (2007): families of local categories over the
  groupoid of local Langlands parameters, with their loop group actions.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory CategoryTheory.Prod Pseudofunctor.StrongTrans

namespace Hom

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  {L L' : EquivariantGroupoidLift Γ actions}

/-- The inverse-fiber comparisons of a lift morphism `φ : L ⟶ L'` intertwine the joint
normalization comparisons `normalizationJointIso` with `φ.transportIso` and the joint naturality
of `φ`. -/
@[reassoc]
lemma inverseFiberIso_normalizationJointIso (φ : L.Hom L') {X Y : Γ × SingleObj H} (f : X ⟶ Y)
    (x : fiber actions X.1) :
    (φ.inverseFiberIso Y.1).hom.app ((L.normalizedTransport.jointFunctor f).obj x) ≫
        (L'.fiberEquivalence Y.1).inverse.map
          ((φ.transportIso f.1).hom.app ((act actions X.1 f.2).obj x)) ≫
        (L'.normalizationJointIso f).hom.app x =
      (φ.jointFunctor Y.1).map ((L.normalizationJointIso f).hom.app x) ≫
        (φ.joint.naturality f.toLoc).hom.toNatTrans.app
          ((L.fiberEquivalence X.1).inverse.obj x) ≫
        (L'.joint.map f.toLoc).toFunctor.map ((φ.inverseFiberIso X.1).hom.app x) := by
  obtain ⟨p, ⟨⟩⟩ := X
  obtain ⟨q, ⟨⟩⟩ := Y
  obtain ⟨g, a⟩ := f
  have hga : (g, a) = (g ×ₘ a : (p, SingleObj.star H) ⟶ (q, SingleObj.star H)) := rfl
  rw [hga]
  dsimp only [NormalizedTransport.jointFunctor, normalizedTransport, transport, Functor.comp_obj]
  simp only [transportIso_hom_app, normalizationJointIso_hom_app, Functor.map_comp, Category.assoc]
  -- Move the mapped comparison on `L'.jointFiber q` past `unitInv` to expose the unit mate at `q`.
  have hunit := (L'.fiberEquivalence q).unitInv.naturality
    ((φ.jointMapIso g).hom.app ((L.fiberEquivalence p).inverse.obj ((act actions p a).obj x)) ≫
      (L'.jointMap g).map ((φ.inverseFiberIso p).hom.app ((act actions p a).obj x)))
  dsimp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hunit
  simp only [Functor.map_comp] at hunit
  rw [reassoc_of% hunit, φ.inverseFiberIso_hom_app_comp_unitInv_assoc]
  -- Combine the source inverse-fiber comparison with the action comparison on `p`.
  rw [← (L'.jointMap g).map_comp_assoc, ← φ.inverseFiberIso_actInverseIso]
  simp only [Functor.map_comp, Category.assoc]
  have hmap := (φ.jointMapIso g).hom.naturality ((L.actInverseIso p a).hom.app x)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hmap
  rw [reassoc_of% hmap.symm]
  -- Move the source inverse-fiber comparison past the compositor of `L'.joint`.
  have hprod :
      (𝟙 p ×ₘ a).toLoc ≫ (g ×ₘ 𝟙 (SingleObj.star H)).toLoc = (g ×ₘ a).toLoc := by
    apply congrArg Quiver.Hom.toLoc
    exact Prod.ext (Category.id_comp _) (Category.comp_id _)
  have hc' := (L'.joint.mapComp' (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
    (g ×ₘ a).toLoc hprod).inv.toNatTrans.naturality ((φ.inverseFiberIso p).hom.app x)
  dsimp only [Cat.Hom.comp_toFunctor, Functor.comp_obj, Functor.comp_map] at hc'
  -- Factor the joint naturality of `φ` at `(g, a)` into its symmetry and parameter parts.
  have hnat := φ.joint.naturality_comp'_hom_app
    (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ a).toLoc
    hprod ((L.fiberEquivalence p).inverse.obj x)
  simp only [jointMapIso_hom_app, jointActIso_hom_app, jointMap, jointAct, jointFunctor]
  rw [hc', hnat]
  simp only [Category.assoc]
  rw [← ((φ.joint.app ⟨(q, SingleObj.star H)⟩).toFunctor).map_comp_assoc
    ((L.joint.mapComp' _ _ _ _).inv.toNatTrans.app _)]
  erw [Cat.Hom.inv_hom_id_toNatTrans_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

private lemma isoMk_trans_leftUnitor_symm_hom_app {C D : Cat.{v, w}} {F G : C ⥤ D}
    (e : F ≅ G) (z : C) :
    (Cat.Hom.isoMk e ≪≫ (λ_ G.toCatHom).symm).hom.toNatTrans.app z = e.hom.app z :=
  Category.comp_id _

private lemma isoMk_trans_leftUnitor_symm_inv_app {C D : Cat.{v, w}} {F G : C ⥤ D}
    (e : F ≅ G) (z : C) :
    (Cat.Hom.isoMk e ≪≫ (λ_ G.toCatHom).symm).inv.toNatTrans.app z = e.inv.app z :=
  Category.id_comp _

private lemma normalizationInv_fiberFunctorIso_hom_app (L : EquivariantGroupoidLift Γ actions)
    (p : Γ) (x : fiber actions p) :
    (L.normalizationInv.fiberFunctorIso p).hom.app x = (L.fiberEquivalence p).counit.app x := by
  erw [fiberFunctorIso_hom_app, normalizationInv_fiberIso_hom_as_app, Cat.Hom.isoMk_hom]
  rfl

private lemma toLiftHom_fiberFunctorIso_hom_app {N N' : NormalizedTransport Γ actions}
    (α : N ⟶ N') (p : Γ) (x : fiber actions p) :
    (α.toLiftHom.fiberFunctorIso p).hom.app x = 𝟙 x := by
  erw [fiberFunctorIso_hom_app, NormalizedTransport.Hom.toLiftHom_fiberIso_hom_as_app]
  rfl

private lemma compNormalizationInvJointIso_naturality (φ : L.Hom L') {p q : Γ}
    (f : (p, SingleObj.star H) ⟶ (q, SingleObj.star H)) :
    L.normalizedTransport.toLift.joint.map f.toLoc ◁
        (Cat.Hom.isoMk (φ.inverseFiberIso q) ≪≫
          (λ_ (L'.normalizationInv.joint.app ⟨(q, SingleObj.star H)⟩)).symm).hom ≫
      ((φ.normalizedTransportHom.toLiftHom.comp
          L'.normalizationInv).joint.naturality f.toLoc).hom =
    ((L.normalizationInv.comp φ).joint.naturality f.toLoc).hom ≫
      (Cat.Hom.isoMk (φ.inverseFiberIso p) ≪≫
          (λ_ (L'.normalizationInv.joint.app ⟨(p, SingleObj.star H)⟩)).symm).hom ▷
        L'.joint.map f.toLoc := by
  refine Cat.whiskerLeft_comp_eq_comp_whiskerRight _ _ _ _ (fun x ↦ ?_)
  let x₀ : fiber actions p := x
  let ψ := φ.normalizedTransportHom.toLiftHom
  have hLHS₁ :
      ((ψ.comp L'.normalizationInv).joint.naturality f.toLoc).hom.toNatTrans.app x =
        (L'.fiberEquivalence q).inverse.map
            ((φ.transportIso f.1).hom.app ((act actions p f.2).obj x₀)) ≫
          (L'.normalizationJointIso f).hom.app x₀ := by
    have hc := Pseudofunctor.StrongTrans.comp_naturality_hom_app
      ψ.joint L'.normalizationInv.joint f.toLoc x
    have hψ : (ψ.joint.naturality f.toLoc).hom.toNatTrans.app x =
        (φ.transportIso f.1).hom.app ((act actions p f.2).obj x₀) :=
      (NormalizedTransport.Hom.jointHom_naturality_hom_app
        φ.normalizedTransportHom f.toLoc x₀).trans
        (by rw [normalizedTransportHom_transportIso]; rfl)
    have hL' : (L'.normalizationInv.joint.naturality f.toLoc).hom.toNatTrans.app
        ((ψ.joint.app ⟨(p, SingleObj.star H)⟩).toFunctor.obj x) =
        (L'.normalizationJointIso f).hom.app x₀ :=
      L'.normalizationJointInv_naturality_hom_app f.toLoc x₀
    exact hc.trans (congrArg₂ (@CategoryStruct.comp (L'.jointFiber q) _ _ _ _)
      (congrArg (L'.fiberEquivalence q).inverse.map hψ) hL')
  have hRHS₀ :
      ((L.normalizationInv.comp φ).joint.naturality f.toLoc).hom.toNatTrans.app x =
        (φ.jointFunctor q).map ((L.normalizationJointIso f).hom.app x₀) ≫
          (φ.joint.naturality f.toLoc).hom.toNatTrans.app
            ((L.fiberEquivalence p).inverse.obj x₀) := by
    have hc := Pseudofunctor.StrongTrans.comp_naturality_hom_app
      L.normalizationInv.joint φ.joint f.toLoc x
    have hL : (L.normalizationInv.joint.naturality f.toLoc).hom.toNatTrans.app x =
        (L.normalizationJointIso f).hom.app x₀ :=
      L.normalizationJointInv_naturality_hom_app f.toLoc x₀
    exact hc.trans (congrArg
      (· ≫ (φ.joint.naturality f.toLoc).hom.toNatTrans.app
        ((L.fiberEquivalence p).inverse.obj x₀))
      (congrArg (φ.jointFunctor q).map hL))
  exact (congrArg₂ (@CategoryStruct.comp (L'.jointFiber q) _ _ _ _)
      (isoMk_trans_leftUnitor_symm_hom_app (φ.inverseFiberIso q)
        ((L.normalizedTransport.jointFunctor f).obj x₀))
      hLHS₁).trans
    ((φ.inverseFiberIso_normalizationJointIso f x₀).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg₂ (@CategoryStruct.comp (L'.jointFiber q) _ _ _ _) hRHS₀.symm
          (congrArg (L'.joint.map f.toLoc).toFunctor.map
            (isoMk_trans_leftUnitor_symm_hom_app (φ.inverseFiberIso p) x₀)).symm)))

/-- Invertible modification of joint strong transformations comparing `L.normalizationInv ≫ φ`
with `φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv`, with components induced by
`φ.inverseFiberIso`. -/
noncomputable def compNormalizationInvJointIso (φ : L.Hom L') :
    (L.normalizationInv.comp φ).joint ≅
      (φ.normalizedTransportHom.toLiftHom.comp L'.normalizationInv).joint :=
  Pseudofunctor.StrongTrans.isoMk
    (fun ⟨(p, ⟨⟩)⟩ ↦ Cat.Hom.isoMk (φ.inverseFiberIso p) ≪≫
      (λ_ (L'.normalizationInv.joint.app ⟨(p, SingleObj.star H)⟩)).symm)
    (fun {X Y} f ↦ by
      obtain ⟨p, ⟨⟩⟩ := X
      obtain ⟨q, ⟨⟩⟩ := Y
      obtain ⟨f⟩ := f
      exact φ.compNormalizationInvJointIso_naturality f)

/-- Forward component of `φ.compNormalizationInvJointIso` at `(p, ⋆)`. -/
lemma compNormalizationInvJointIso_hom_as_app (φ : L.Hom L') (p : Γ) :
    φ.compNormalizationInvJointIso.hom.as.app ⟨(p, SingleObj.star H)⟩ =
      (Cat.Hom.isoMk (φ.inverseFiberIso p) ≪≫
        (λ_ (L'.normalizationInv.joint.app ⟨(p, SingleObj.star H)⟩)).symm).hom :=
  (rfl)

/-- Inverse component of `φ.compNormalizationInvJointIso` at `(p, ⋆)`. -/
lemma compNormalizationInvJointIso_inv_as_app (φ : L.Hom L') (p : Γ) :
    φ.compNormalizationInvJointIso.inv.as.app ⟨(p, SingleObj.star H)⟩ =
      (Cat.Hom.isoMk (φ.inverseFiberIso p) ≪≫
        (λ_ (L'.normalizationInv.joint.app ⟨(p, SingleObj.star H)⟩)).symm).inv :=
  (rfl)

private lemma compNormalizationInvHomIso_comm (φ : L.Hom L') (p : Γ)
    (a : LocallyDiscrete (SingleObj H)) :
    φ.compNormalizationInvJointIso.hom.as.app
        ((Prod.sectR p (SingleObj H)).toPseudofunctor.obj a) ▷
        (L'.comparison p).app a ≫
      ((φ.normalizedTransportHom.toLiftHom.comp L'.normalizationInv).fiberIso p).hom.as.app a =
    ((L.normalizationInv.comp φ).fiberIso p).hom.as.app a := by
  obtain ⟨⟨⟩⟩ := a
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext x
  let M := L.normalizedTransport.toLift
  let x₁ : M.jointFiber p := x
  let x₀ : fiber actions p := x
  let ψ := φ.normalizedTransportHom.toLiftHom
  have hcomp := Cat.Hom₂.comp_app
    (φ.compNormalizationInvJointIso.hom.as.app
      ((Prod.sectR p (SingleObj H)).toPseudofunctor.obj ⟨SingleObj.star H⟩) ▷
      (L'.comparison p).app ⟨SingleObj.star H⟩)
    (((ψ.comp L'.normalizationInv).fiberIso p).hom.as.app ⟨SingleObj.star H⟩) x
  have hLHS₁ :
      (φ.compNormalizationInvJointIso.hom.as.app
          ((Prod.sectR p (SingleObj H)).toPseudofunctor.obj ⟨SingleObj.star H⟩) ▷
          (L'.comparison p).app ⟨SingleObj.star H⟩).toNatTrans.app x =
        (L'.fiberEquivalence p).functor.map ((φ.inverseFiberIso p).hom.app x₀) :=
    (Cat.whiskerRight_app ((L'.comparison p).app ⟨SingleObj.star H⟩)
      (φ.compNormalizationInvJointIso.hom.as.app
        ((Prod.sectR p (SingleObj H)).toPseudofunctor.obj ⟨SingleObj.star H⟩)) x).trans
      (congrArg (L'.fiberEquivalence p).functor.map
        (isoMk_trans_leftUnitor_symm_hom_app (φ.inverseFiberIso p) x₀))
  have hLHS₂ :
      (((ψ.comp L'.normalizationInv).fiberIso p).hom.as.app
          ⟨SingleObj.star H⟩).toNatTrans.app x =
        (L'.fiberEquivalence p).counit.app x₀ :=
    (fiberFunctorIso_hom_app (ψ.comp L'.normalizationInv) p x₁).symm.trans
      ((comp_fiberFunctorIso_hom_app ψ L'.normalizationInv p x₁).trans
        ((congrArg₂ (@CategoryStruct.comp (fiber actions p) _ _ _ _)
          (normalizationInv_fiberFunctorIso_hom_app L' p x₀)
          (toLiftHom_fiberFunctorIso_hom_app φ.normalizedTransportHom p x₀)).trans
          (Category.comp_id _)))
  have hRHS :
      (((L.normalizationInv.comp φ).fiberIso p).hom.as.app
          ⟨SingleObj.star H⟩).toNatTrans.app x =
        (φ.fiberFunctorIso p).hom.app ((L.fiberEquivalence p).inverse.obj x₀) ≫
          (L.fiberEquivalence p).counit.app x₀ :=
    (fiberFunctorIso_hom_app (L.normalizationInv.comp φ) p x₁).symm.trans
      ((comp_fiberFunctorIso_hom_app L.normalizationInv φ p x₁).trans
        (congrArg
          ((φ.fiberFunctorIso p).hom.app ((L.fiberEquivalence p).inverse.obj x₀) ≫ ·)
          (normalizationInv_fiberFunctorIso_hom_app L p x₀)))
  exact hcomp.trans
    ((congrArg₂ (@CategoryStruct.comp (fiber actions p) _ _ _ _) hLHS₁ hLHS₂).trans
      ((φ.functor_map_inverseFiberIso_hom_app_comp_counit p x₀).trans hRHS.symm))

private noncomputable def compNormalizationInvHomIso (φ : L.Hom L') :
    L.normalizationInv.comp φ ≅
      φ.normalizedTransportHom.toLiftHom.comp L'.normalizationInv :=
  isoMk φ.compNormalizationInvJointIso φ.compNormalizationInvHomIso_comm

private lemma compNormalizationInvHomIso_hom_joint (φ : L.Hom L') :
    φ.compNormalizationInvHomIso.hom.joint = φ.compNormalizationInvJointIso.hom :=
  isoMk_hom_joint _ _

private lemma compNormalizationInvHomIso_inv_joint (φ : L.Hom L') :
    φ.compNormalizationInvHomIso.inv.joint = φ.compNormalizationInvJointIso.inv :=
  isoMk_inv_joint _ _

/-- Naturality modification comparing
`(φ.normalizedTransportHom.toLiftHom : _ ⟶ _) ≫ L'.normalizationInv` with
`L.normalizationInv ≫ (φ : L ⟶ L')`, with joint components induced by
`(φ.inverseFiberIso _).symm`. -/
noncomputable def normalizationInvIso (φ : L.Hom L') :
    (φ.normalizedTransportHom.toLiftHom :
        L.normalizedTransport.toLift ⟶ L'.normalizedTransport.toLift) ≫
      L'.normalizationInv ≅ L.normalizationInv ≫ (φ : L ⟶ L') where
  hom := φ.compNormalizationInvHomIso.inv
  inv := φ.compNormalizationInvHomIso.hom
  hom_inv_id := φ.compNormalizationInvHomIso.inv_hom_id
  inv_hom_id := φ.compNormalizationInvHomIso.hom_inv_id

/-- Evaluating the forward joint modification of `φ.normalizationInvIso` at `x` gives
`(φ.inverseFiberIso X.as.1).inv.app x`. -/
lemma normalizationInvIso_hom_joint_as_app (φ : L.Hom L')
    (X : LocallyDiscrete (Γ × SingleObj H)) (x : fiber actions X.as.1) :
    ((φ.normalizationInvIso.hom.joint.as.app X).toNatTrans.app x) =
      (φ.inverseFiberIso X.as.1).inv.app x := by
  obtain ⟨p, ⟨⟩⟩ := X
  let x₁ : L.normalizedTransport.toLift.jointFiber p := x
  exact (congrArg (fun m ↦ (m.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.app x₁)
    (compNormalizationInvHomIso_inv_joint φ)).trans
    (isoMk_trans_leftUnitor_symm_inv_app (φ.inverseFiberIso p) x)

/-- Evaluating the inverse joint modification of `φ.normalizationInvIso` at `x` gives
`(φ.inverseFiberIso X.as.1).hom.app x`. -/
lemma normalizationInvIso_inv_joint_as_app (φ : L.Hom L')
    (X : LocallyDiscrete (Γ × SingleObj H)) (x : fiber actions X.as.1) :
    ((φ.normalizationInvIso.inv.joint.as.app X).toNatTrans.app x) =
      (φ.inverseFiberIso X.as.1).hom.app x := by
  obtain ⟨p, ⟨⟩⟩ := X
  let x₁ : L.normalizedTransport.toLift.jointFiber p := x
  exact (congrArg (fun m ↦ (m.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.app x₁)
    (compNormalizationInvHomIso_hom_joint φ)).trans
    (isoMk_trans_leftUnitor_symm_hom_app (φ.inverseFiberIso p) x)

/-- Forward naturality modification comparing `φ ≫ L'.normalizationEquivalence.hom` with
`L.normalizationEquivalence.hom ≫ φ.normalizedTransportHom.toLiftHom`, obtained as the mate of
`φ.normalizationInvIso.symm` along `L.normalizationEquivalence` and
`L'.normalizationEquivalence`. -/
noncomputable def normalizationHomIso (φ : L.Hom L') :
    φ ≫ L'.normalizationEquivalence.hom ≅
      L.normalizationEquivalence.hom ≫ φ.normalizedTransportHom.toLiftHom :=
  let φ' : L ⟶ L' := φ
  let ψ : L.normalizedTransport.toLift ⟶ L'.normalizedTransport.toLift :=
    φ.normalizedTransportHom.toLiftHom
  (λ_ (φ' ≫ L'.normalizationEquivalence.hom)).symm ≪≫
    whiskerRightIso L.normalizationInv.equivalence.counit.symm
      (φ' ≫ L'.normalizationEquivalence.hom) ≪≫
    α_ L.normalizationEquivalence.hom L.normalizationInv
      (φ' ≫ L'.normalizationEquivalence.hom) ≪≫
    whiskerLeftIso L.normalizationEquivalence.hom
      ((α_ L.normalizationInv φ' L'.normalizationEquivalence.hom).symm ≪≫
        whiskerRightIso φ.normalizationInvIso.symm L'.normalizationEquivalence.hom ≪≫
        α_ ψ L'.normalizationInv L'.normalizationEquivalence.hom ≪≫
        whiskerLeftIso ψ L'.normalizationInv.equivalence.unit.symm ≪≫
        ρ_ ψ)

end Hom

section Biequivalence

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  (actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w})

/-- The inverse normalization comparisons `L.normalizationInv` assemble into a strong
transformation from normalization followed by reconstruction to the identity pseudofunctor.
All 2-morphism coherence conditions hold automatically because compatible modifications of lifts
are unique. -/
noncomputable def normalizationUnitInv :
    (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) ⟶
      Pseudofunctor.id (EquivariantGroupoidLift Γ actions) where
  app L := L.normalizationInv
  naturality φ := φ.normalizationInvIso
  naturality_naturality _ := Subsingleton.elim _ _
  naturality_id _ := Subsingleton.elim _ _
  naturality_comp _ _ := Subsingleton.elim _ _

@[simp]
lemma normalizationUnitInv_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitInv actions).app L = L.normalizationInv :=
  (rfl)

/-- The forward normalization equivalences `L.normalizationEquivalence.hom` assemble into a strong
transformation from the identity pseudofunctor to normalization followed by reconstruction. -/
noncomputable def normalizationUnitHom :
    Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ⟶
      (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) where
  app L := L.normalizationEquivalence.hom
  naturality φ := φ.normalizationHomIso
  naturality_naturality _ := Subsingleton.elim _ _
  naturality_id _ := Subsingleton.elim _ _
  naturality_comp _ _ := Subsingleton.elim _ _

@[simp]
lemma normalizationUnitHom_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitHom actions).app L = L.normalizationEquivalence.hom :=
  (rfl)

/-- The identity pseudofunctor on equivariant lifts is equivalent to normalization followed by
reconstruction, with objectwise equivalences `L.normalizationEquivalence`. -/
noncomputable def normalizationUnitEquiv :
    Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ≌
      (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) where
  hom := normalizationUnitHom actions
  inv := normalizationUnitInv actions
  unit := Pseudofunctor.StrongTrans.isoMk
    (fun L ↦ L.normalizationInv.equivalence.counit.symm)
    (fun _ ↦ Subsingleton.elim _ _)
  counit := Pseudofunctor.StrongTrans.isoMk
    (fun L ↦ L.normalizationInv.equivalence.unit.symm)
    (fun _ ↦ Subsingleton.elim _ _)
  left_triangle := by
    apply Iso.ext
    apply homCategory.ext
    intro L
    exact Subsingleton.elim _ _

@[simp]
lemma normalizationUnitEquiv_hom :
    (normalizationUnitEquiv actions).hom = normalizationUnitHom actions :=
  (rfl)

@[simp]
lemma normalizationUnitEquiv_inv :
    (normalizationUnitEquiv actions).inv = normalizationUnitInv actions :=
  (rfl)

/-- The biequivalence between the bicategory of equivariant groupoid lifts and the locally
discrete bicategory of normalized transports on the prescribed fibers. -/
-- Expose the record so projection equations for `unitEquiv` and `counitEquiv` have the literal
-- functor and inverse pseudofunctors in their types.
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

@[simp]
lemma normalizationBiequivalence_unitEquiv :
    (normalizationBiequivalence actions).unitEquiv = normalizationUnitEquiv actions :=
  (rfl)

@[simp]
lemma normalizationBiequivalence_counitEquiv :
    (normalizationBiequivalence actions).counitEquiv = normalizationCounitEquiv actions :=
  (rfl)

end Biequivalence

/-! ### Coherent triangle identities and local equivalences -/

section Consequences

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}

private lemma normalizationInv_inverseFiberIso_hom_app (L : EquivariantGroupoidLift Γ actions)
    (p : Γ) (x : fiber actions p) :
    (L.normalizationInv.inverseFiberIso p).hom.app x =
      (L.fiberEquivalence p).inverse.map
        ((L.normalizedTransport.toLift.fiberEquivalence p).counit.app x) := by
  apply (L.fiberEquivalence p).functor.map_injective
  apply (cancel_mono ((L.fiberEquivalence p).counit.app x)).mp
  rw [L.normalizationInv.functor_map_inverseFiberIso_hom_app_comp_counit,
    Hom.fiberFunctorIso_hom_app, normalizationInv_fiberIso_hom_as_app, Cat.Hom.isoMk_hom]
  exact ((L.fiberEquivalence p).counit.naturality _).symm

private lemma normalizationInv_transportIso_aux (L : EquivariantGroupoidLift Γ actions)
    {p q : Γ} (g : p ⟶ q) {y₀ x : fiber actions p} (ε : y₀ ⟶ x) :
    (L.fiberEquivalence q).counitInv.app
        ((L.normalizedTransport.jointFunctor (g ×ₘ 𝟙 (SingleObj.star H))).obj y₀) ≫
      (L.fiberEquivalence q).functor.map
        ((L.normalizationJointIso (g ×ₘ 𝟙 (SingleObj.star H))).hom.app y₀) ≫
      (L.fiberEquivalence q).functor.map
        ((L.jointMap g).map ((L.fiberEquivalence p).inverse.map ε)) =
    (L.normalizedTransport.transport g).map ((act actions p (𝟙 (SingleObj.star H))).map ε) ≫
      (L.normalizedTransport.transport g).map ((actId actions p).hom.app x) := by
  rw [normalizationJointIso_hom_app]
  have hcomp :
      (L.joint.mapComp' (𝟙 p ×ₘ 𝟙 (SingleObj.star H)).toLoc
        (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
        (by
          apply congrArg Quiver.Hom.toLoc
          exact Prod.ext (Category.id_comp _) (Category.comp_id _))).inv.toNatTrans.app
        ((L.fiberEquivalence p).inverse.obj y₀) =
      (L.jointMap g).map ((L.jointMapId p).hom.app ((L.fiberEquivalence p).inverse.obj y₀)) := by
    have h0 := L.joint.mapComp'_id_comp_inv_app (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
      ((L.fiberEquivalence p).inverse.obj y₀)
    simp only [jointMapId_hom_app, ← prod_id, Quiver.Hom.id_toLoc,
      Pseudofunctor.mapId'_eq_mapId] at h0 ⊢
    exact h0
  rw [hcomp]
  dsimp only [NormalizedTransport.jointFunctor, normalizedTransport, transport,
    Functor.comp_obj, Functor.comp_map]
  simp only [Functor.map_comp, Category.assoc, Equivalence.counitInv_functor_comp_assoc]
  rw [← Functor.map_comp_assoc (L.fiberEquivalence q).functor,
    ← (L.jointMap g).map_comp, L.actInverseIso_actId]
  simp only [← Functor.map_comp, (actId actions p).hom.naturality, Functor.id_map]

/-- Normalizing `L.normalizationInv` along a parameter arrow `g` recovers the canonical return
isomorphism `toLiftTransportIso g` of `L.normalizedTransport`. -/
@[simp]
lemma normalizationInv_transportIso (L : EquivariantGroupoidLift Γ actions) {p q : Γ}
    (g : p ⟶ q) :
    L.normalizationInv.transportIso g = L.normalizedTransport.toLiftTransportIso g := by
  ext x
  let M := L.normalizedTransport.toLift
  let y : M.jointFiber p := (M.fiberEquivalence p).inverse.obj x
  let y₀ : fiber actions p := y
  let ε : y₀ ⟶ x := (M.fiberEquivalence p).counit.app x
  have hj : (L.normalizationInv.jointMapIso g).hom.app y =
      (L.normalizationJointIso (g ×ₘ 𝟙 (SingleObj.star H))).hom.app y₀ :=
    (Hom.jointMapIso_hom_app L.normalizationInv g y).trans
      (L.normalizationJointInv_naturality_hom_app (g ×ₘ 𝟙 (SingleObj.star H)).toLoc y₀)
  have hf : (L.normalizationInv.fiberFunctorIso q).inv.app ((M.jointMap g).obj y) =
      (L.fiberEquivalence q).counitInv.app
        ((L.normalizedTransport.jointFunctor (g ×ₘ 𝟙 (SingleObj.star H))).obj y₀) := by
    rw [Hom.fiberFunctorIso_inv_app, normalizationInv_fiberIso_inv_as_app, Cat.Hom.isoMk_inv]
    rfl
  have hLHS :
      (L.normalizationInv.transportIso g).hom.app x =
        (L.fiberEquivalence q).counitInv.app
            ((L.normalizedTransport.jointFunctor (g ×ₘ 𝟙 (SingleObj.star H))).obj y₀) ≫
          (L.fiberEquivalence q).functor.map
            ((L.normalizationJointIso (g ×ₘ 𝟙 (SingleObj.star H))).hom.app y₀) ≫
          (L.fiberEquivalence q).functor.map
            ((L.jointMap g).map ((L.fiberEquivalence p).inverse.map ε)) :=
    (Hom.transportIso_hom_app L.normalizationInv g x).trans
      (congrArg₂ (@CategoryStruct.comp (fiber actions q) _ _ _ _) hf
        (congrArg₂ (@CategoryStruct.comp (fiber actions q) _ _ _ _)
          (congrArg (L.fiberEquivalence q).functor.map hj)
          (congrArg (fun m ↦ (L.fiberEquivalence q).functor.map ((L.jointMap g).map m))
            (L.normalizationInv_inverseFiberIso_hom_app p x))))
  exact hLHS.trans ((L.normalizationInv_transportIso_aux g ε).trans
    (L.normalizedTransport.toLiftTransportIso_hom_app g x).symm)

/-- First coherent triangle of the normalization biequivalence: normalizing `L.normalizationInv`
agrees with the counit isomorphism `toLiftNormalizedTransportIso` of `L.normalizedTransport`. -/
@[simp]
lemma normalizationInv_normalizedTransportHom (L : EquivariantGroupoidLift Γ actions) :
    L.normalizationInv.normalizedTransportHom =
      (NormalizedTransport.toLiftNormalizedTransportIso L.normalizedTransport).hom := by
  apply NormalizedTransport.Hom.ext
  intro p q g
  rw [Hom.normalizedTransportHom_transportIso,
    NormalizedTransport.toLiftNormalizedTransportIso_hom_transportIso]
  exact normalizationInv_transportIso L g

/-- Normalizing the chosen inverse `L.normalizationInv.equivalence.inv` gives the inverse of
`toLiftNormalizedTransportIso L.normalizedTransport`. -/
@[simp]
lemma normalizationInv_equivalence_inv_normalizedTransportHom
    (L : EquivariantGroupoidLift Γ actions) :
    L.normalizationInv.equivalence.inv.normalizedTransportHom =
      (NormalizedTransport.toLiftNormalizedTransportIso L.normalizedTransport).inv := by
  apply (cancel_epi L.normalizationInv.normalizedTransportHom).mp
  have h := L.normalizationInv.equivalence.unit.inv.normalizedTransportHom_eq
  rw [Hom.equivalence_hom] at h
  rw [← Hom.comp_normalizedTransportHom, h, Hom.id_normalizedTransportHom,
    normalizationInv_normalizedTransportHom, Iso.hom_inv_id]

/-- Normalizing the forward unit equivalence `L.normalizationEquivalence.hom` gives the inverse of
`toLiftNormalizedTransportIso L.normalizedTransport`. -/
lemma normalizationEquivalence_hom_normalizedTransportHom
    (L : EquivariantGroupoidLift Γ actions) :
    L.normalizationEquivalence.hom.normalizedTransportHom =
      (NormalizedTransport.toLiftNormalizedTransportIso L.normalizedTransport).inv :=
  L.normalizationInv_equivalence_inv_normalizedTransportHom

namespace Hom

variable {L L' : EquivariantGroupoidLift Γ actions}

/-- Two morphisms of equivariant lifts inducing the same comparison of normalized transports are
isomorphic by a unique compatible modification. -/
noncomputable def isoOfNormalizedTransportHomEq {φ ψ : L ⟶ L'}
    (h : φ.normalizedTransportHom = ψ.normalizedTransportHom) : φ ≅ ψ :=
  (λ_ φ).symm ≪≫
    whiskerRightIso L.normalizationInv.equivalence.counit.symm φ ≪≫
    α_ L.normalizationEquivalence.hom L.normalizationInv φ ≪≫
    whiskerLeftIso L.normalizationEquivalence.hom
      (φ.normalizationInvIso.symm ≪≫
        whiskerRightIso (eqToIso (congrArg NormalizedTransport.Hom.toLiftHom h))
          L'.normalizationInv ≪≫
        ψ.normalizationInvIso) ≪≫
    (α_ L.normalizationEquivalence.hom L.normalizationInv ψ).symm ≪≫
    whiskerRightIso L.normalizationInv.equivalence.counit ψ ≪≫
    λ_ ψ

/-- A compatible modification between two morphisms of lifts exists if and only if they induce the
same comparison of normalized transports. -/
lemma nonempty_hom₂_iff {φ ψ : L ⟶ L'} :
    Nonempty (φ ⟶ ψ) ↔ φ.normalizedTransportHom = ψ.normalizedTransportHom :=
  ⟨fun ⟨Θ⟩ ↦ Θ.normalizedTransportHom_eq,
    fun h ↦ ⟨(isoOfNormalizedTransportHomEq h).hom⟩⟩

/-- Two morphisms of lifts are isomorphic if and only if they induce the same comparison of
normalized transports. -/
lemma nonempty_iso_iff {φ ψ : L ⟶ L'} :
    Nonempty (φ ≅ ψ) ↔ φ.normalizedTransportHom = ψ.normalizedTransportHom :=
  ⟨fun ⟨e⟩ ↦ e.hom.normalizedTransportHom_eq,
    fun h ↦ ⟨isoOfNormalizedTransportHomEq h⟩⟩

/-- Transport a comparison `α : L.normalizedTransport ⟶ L'.normalizedTransport` of normalized
transports back along `L.normalizationEquivalence` and `L'.normalizationInv` to a lift morphism. -/
noncomputable def ofNormalizedTransportHom
    (α : L.normalizedTransport ⟶ L'.normalizedTransport) : L ⟶ L' :=
  L.normalizationEquivalence.hom ≫ α.toLiftHom ≫ L'.normalizationInv

/-- Transporting a comparison of normalized transports to a morphism of lifts and normalizing
recovers the original comparison. -/
@[simp]
lemma ofNormalizedTransportHom_normalizedTransportHom
    (α : L.normalizedTransport ⟶ L'.normalizedTransport) :
    (ofNormalizedTransportHom α).normalizedTransportHom = α := by
  rw [ofNormalizedTransportHom, comp_normalizedTransportHom, comp_normalizedTransportHom,
    normalizationEquivalence_hom_normalizedTransportHom, normalizationInv_normalizedTransportHom,
    NormalizedTransport.toLiftNormalizedTransportIso_hom_naturality, Iso.inv_hom_id_assoc]

/-- Reconstructing a lift morphism from its normalized transport comparison recovers the original
morphism up to a unique compatible invertible modification. -/
noncomputable def ofNormalizedTransportHomIso (φ : L.Hom L') :
    ofNormalizedTransportHom φ.normalizedTransportHom ≅ (φ : L ⟶ L') :=
  isoOfNormalizedTransportHomEq (ofNormalizedTransportHom_normalizedTransportHom _)

end Hom

/-- Second coherent triangle of the normalization biequivalence: reconstructing the counit
isomorphism `toLiftNormalizedTransportIso N` gives a morphism of lifts isomorphic to
`N.toLift.normalizationInv`. -/
noncomputable def NormalizedTransport.toLiftNormalizedTransportIsoHomIso
    (N : NormalizedTransport Γ actions) :
    (NormalizedTransport.toLiftNormalizedTransportIso N).hom.toLiftHom ≅
      N.toLift.normalizationInv :=
  Hom.isoOfNormalizedTransportHomEq <| by
    apply (cancel_mono (NormalizedTransport.toLiftNormalizedTransportIso N).hom).mp
    rw [NormalizedTransport.toLiftNormalizedTransportIso_hom_naturality,
      normalizationInv_normalizedTransportHom]

/-- Normalization is faithful on every hom-category because compatible modifications are unique. -/
instance faithful_normalizationPseudofunctor_mapFunctor
    (L L' : EquivariantGroupoidLift Γ actions) :
    ((normalizationPseudofunctor actions).mapFunctor L L').Faithful where
  map_injective _ := Subsingleton.elim _ _

/-- Normalization is full on every hom-category: equal normalized transport comparisons lift to a
compatible modification. -/
instance full_normalizationPseudofunctor_mapFunctor
    (L L' : EquivariantGroupoidLift Γ actions) :
    ((normalizationPseudofunctor actions).mapFunctor L L').Full where
  map_surjective {φ ψ} η := by
    have h := LocallyDiscrete.eq_of_hom η
    rw [PrelaxFunctor.mapFunctor_obj, PrelaxFunctor.mapFunctor_obj] at h
    have h' : φ.normalizedTransportHom = ψ.normalizedTransportHom := congrArg Discrete.as h
    exact ⟨(Hom.isoOfNormalizedTransportHomEq h').hom, Subsingleton.elim _ _⟩

/-- Normalization is essentially surjective on every hom-category: every comparison of normalized
transports lifts to a morphism of equivariant lifts. -/
instance essSurj_normalizationPseudofunctor_mapFunctor
    (L L' : EquivariantGroupoidLift Γ actions) :
    ((normalizationPseudofunctor actions).mapFunctor L L').EssSurj where
  mem_essImage α :=
    ⟨Hom.ofNormalizedTransportHom (L := L) (L' := L') α.as,
      ⟨eqToIso <| Discrete.ext <|
        (by rw [PrelaxFunctor.mapFunctor_obj, normalizationPseudofunctor_map_as] :
            (((normalizationPseudofunctor actions).mapFunctor L L').obj
                (Hom.ofNormalizedTransportHom (L := L) (L' := L') α.as)).as =
              (Hom.ofNormalizedTransportHom (L := L) (L' := L') α.as).normalizedTransportHom).trans
          (Hom.ofNormalizedTransportHom_normalizedTransportHom (L := L) (L' := L') α.as)⟩⟩

/-- Normalization is a local equivalence on every hom-category. -/
instance isEquivalence_normalizationPseudofunctor_mapFunctor
    (L L' : EquivariantGroupoidLift Γ actions) :
    ((normalizationPseudofunctor actions).mapFunctor L L').IsEquivalence where

/-- Normalization induces an equivalence from the thin groupoid of lift morphisms `L ⟶ L'` to the
discrete hom-category between `(normalizationPseudofunctor actions).obj L` and
`(normalizationPseudofunctor actions).obj L'`. -/
noncomputable def normalizationMapEquivalence
    (L L' : EquivariantGroupoidLift Γ actions) :
    (L ⟶ L') ≌
      ((normalizationPseudofunctor actions).obj L ⟶
        (normalizationPseudofunctor actions).obj L') :=
  ((normalizationPseudofunctor actions).mapFunctor L L').asEquivalence

@[simp]
lemma normalizationMapEquivalence_functor (L L' : EquivariantGroupoidLift Γ actions) :
    (normalizationMapEquivalence L L').functor =
      (normalizationPseudofunctor actions).mapFunctor L L' :=
  (rfl)

private lemma inv_comp_toLiftHom_normalizedTransportHom_comp_hom
    {N N' : NormalizedTransport Γ actions} (α : N ⟶ N') :
    (NormalizedTransport.toLiftNormalizedTransportIso N).inv ≫
        α.toLiftHom.normalizedTransportHom ≫
        (NormalizedTransport.toLiftNormalizedTransportIso N').hom = α := by
  rw [NormalizedTransport.toLiftNormalizedTransportIso_hom_naturality, Iso.inv_hom_id_assoc]

private lemma toLiftHom_normalizedTransportHom_inv_comp_hom
    {N N' : NormalizedTransport Γ actions} (φ : N.toLift ⟶ N'.toLift) :
    ((NormalizedTransport.toLiftNormalizedTransportIso N).inv ≫
        φ.normalizedTransportHom ≫
        (NormalizedTransport.toLiftNormalizedTransportIso N').hom
      ).toLiftHom.normalizedTransportHom =
      φ.normalizedTransportHom := by
  apply (cancel_mono (NormalizedTransport.toLiftNormalizedTransportIso N').hom).mp
  rw [NormalizedTransport.toLiftNormalizedTransportIso_hom_naturality, Iso.hom_inv_id_assoc]

/-- Reconstruction is faithful on every hom-category because its source hom-categories are
discrete. -/
instance faithful_reconstructionPseudofunctor_mapFunctor
    (N N' : LocallyDiscrete (NormalizedTransport Γ actions)) :
    ((reconstructionPseudofunctor actions).mapFunctor N N').Faithful where
  map_injective _ := Subsingleton.elim _ _

/-- Reconstruction is full on every hom-category: any compatible modification between reconstructed
lift morphisms comes from equality of the underlying comparisons. -/
instance full_reconstructionPseudofunctor_mapFunctor
    (N N' : LocallyDiscrete (NormalizedTransport Γ actions)) :
    ((reconstructionPseudofunctor actions).mapFunctor N N').Full where
  map_surjective {α β} Θ := by
    have h := Θ.normalizedTransportHom_eq
    rw [PrelaxFunctor.mapFunctor_obj, PrelaxFunctor.mapFunctor_obj,
      reconstructionPseudofunctor_map, reconstructionPseudofunctor_map] at h
    have hab : α = β := Discrete.ext <|
      (inv_comp_toLiftHom_normalizedTransportHom_comp_hom α.as).symm.trans
        ((congrArg (fun k ↦ (NormalizedTransport.toLiftNormalizedTransportIso N.as).inv ≫
            k ≫ (NormalizedTransport.toLiftNormalizedTransportIso N'.as).hom) h).trans
          (inv_comp_toLiftHom_normalizedTransportHom_comp_hom β.as))
    exact ⟨eqToHom hab, Subsingleton.elim _ _⟩

/-- Reconstruction is essentially surjective on every hom-category. -/
instance essSurj_reconstructionPseudofunctor_mapFunctor
    (N N' : LocallyDiscrete (NormalizedTransport Γ actions)) :
    ((reconstructionPseudofunctor actions).mapFunctor N N').EssSurj where
  mem_essImage φ :=
    ⟨((NormalizedTransport.toLiftNormalizedTransportIso N.as).inv ≫
        φ.normalizedTransportHom ≫
        (NormalizedTransport.toLiftNormalizedTransportIso N'.as).hom).toLoc,
      ⟨Hom.isoOfNormalizedTransportHomEq <| by
        rw [PrelaxFunctor.mapFunctor_obj, reconstructionPseudofunctor_map]
        exact toLiftHom_normalizedTransportHom_inv_comp_hom φ⟩⟩

/-- Reconstruction is a local equivalence on every hom-category. -/
instance isEquivalence_reconstructionPseudofunctor_mapFunctor
    (N N' : LocallyDiscrete (NormalizedTransport Γ actions)) :
    ((reconstructionPseudofunctor actions).mapFunctor N N').IsEquivalence where

/-- Reconstruction induces an equivalence on every hom-category between locally discrete
normalized transports and their reconstructed lifts. -/
noncomputable def reconstructionMapEquivalence
    (N N' : LocallyDiscrete (NormalizedTransport Γ actions)) :
    (N ⟶ N') ≌
      ((reconstructionPseudofunctor actions).obj N ⟶
        (reconstructionPseudofunctor actions).obj N') :=
  ((reconstructionPseudofunctor actions).mapFunctor N N').asEquivalence

@[simp]
lemma reconstructionMapEquivalence_functor
    (N N' : LocallyDiscrete (NormalizedTransport Γ actions)) :
    (reconstructionMapEquivalence N N').functor =
      (reconstructionPseudofunctor actions).mapFunctor N N' :=
  (rfl)

/-- A morphism between two equivariant lifts exists if and only if a comparison exists between
their normalized transports. -/
lemma nonempty_hom_iff (L L' : EquivariantGroupoidLift Γ actions) :
    Nonempty (L ⟶ L') ↔ Nonempty (L.normalizedTransport ⟶ L'.normalizedTransport) :=
  ⟨fun ⟨φ⟩ ↦ ⟨φ.normalizedTransportHom⟩,
    fun ⟨α⟩ ↦ ⟨Hom.ofNormalizedTransportHom α⟩⟩

/-- Two equivariant lifts are equivalent in `EquivariantGroupoidLift Γ actions` if and only if
their normalized transports are isomorphic in `NormalizedTransport Γ actions`. -/
lemma nonempty_equivalence_iff (L L' : EquivariantGroupoidLift Γ actions) :
    Nonempty (L ≌ L') ↔ Nonempty (L.normalizedTransport ≅ L'.normalizedTransport) :=
  ⟨fun ⟨e⟩ ↦ ⟨asIso e.hom.normalizedTransportHom⟩,
    fun ⟨e⟩ ↦ ⟨(Hom.ofNormalizedTransportHom e.hom).equivalence⟩⟩

end Consequences

end TauCeti.EquivariantGroupoidLift
