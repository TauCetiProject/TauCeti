/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
public import TauCeti.CategoryTheory.Bicategory.Biequivalence
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.NormalizedTransport.Counit
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.NormalizedTransport.Unit

/-!
# The biequivalence between equivariant lifts and normalized transport

For a family `actions` of categorical `H`-actions indexed by `Γ`, every lift `L` is equivalent in
`EquivariantGroupoidLift Γ actions` to the reconstruction `L.normalizedTransport.toLift` of its
normalized transport, with inverse morphism `L.normalizationInv` given by the chosen inverse fiber
equivalences and their counits (`EquivariantGroupoidLift.normalizationEquivalence`). Moreover,
normalizing followed by reconstructing and normalizing again is equivalent to the identity of
`LocallyDiscrete (NormalizedTransport Γ actions)` via `normalizationCounitEquiv`.

This file proves that `normalizationInv` and `normalizationEquivalence.hom` are pseudonatural in
morphisms of lifts `φ : L ⟶ L'`:

* the inverse-fiber comparisons `φ.inverseFiberIso` assemble into an invertible compatible
  modification `φ.normalizationInvNatIso :
  φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv ≅ L.normalizationInv ≫ φ`;
* taking mates across `normalizationEquivalence` gives the forward naturality isomorphism
  `φ.normalizationHomNatIso :
  φ ≫ L'.normalizationEquivalence.hom ≅
  L.normalizationEquivalence.hom ≫ φ.normalizedTransportHom.toLiftHom`.

Since compatible modifications between parallel lift morphisms form a `Subsingleton` and are
automatically invertible (`EquivariantGroupoidLift.subsingleton₂` and
`EquivariantGroupoidLift.isGroupoid_hom`), and every `1`-morphism of lifts is already an
equivalence (`EquivariantGroupoidLift.Hom.equivalence`), restricting to equivalences and invertible
modifications loses no morphisms. Uniqueness of compatible modifications discharges the coherence
axioms of the strong transformations `normalizationUnitHom` and `normalizationUnitInv`, assembling
the objectwise equivalences into the unit equivalence

`normalizationUnitEquiv actions :
  Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ≌
    (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions)`

and hence into the biequivalence

`normalizationBiequivalence actions :
  TauCeti.Biequivalence (EquivariantGroupoidLift Γ actions)
    (LocallyDiscrete (NormalizedTransport Γ actions))`.

Normalizing `L.normalizationInv` recovers the counit component
`(toLiftNormalizedTransportIso L.normalizedTransport).hom`. Together with the unit naturality
isomorphisms, this yields explicit adjoint equivalences on hom-categories for both
`normalizationPseudofunctor` and `reconstructionPseudofunctor`, and shows that two parallel lift
morphisms admit a compatible modification if and only if they induce the same comparison of
normalized transports.

## Main declarations

* `TauCeti.EquivariantGroupoidLift.Hom.normalizationInvNatIso`,
  `TauCeti.EquivariantGroupoidLift.Hom.normalizationHomNatIso`: naturality of `normalizationInv`
  and `normalizationEquivalence.hom` along morphisms of lifts;
* `TauCeti.EquivariantGroupoidLift.Hom.nonempty_hom₂_iff`: parallel morphisms of lifts admit a
  compatible modification if and only if their normalized transport comparisons are equal;
* `TauCeti.EquivariantGroupoidLift.normalizationInv_normalizedTransportHom`: normalizing
  `L.normalizationInv` gives the return comparison `toLiftNormalizedTransportIso`;
* `TauCeti.EquivariantGroupoidLift.normalizationUnitHom`,
  `TauCeti.EquivariantGroupoidLift.normalizationUnitInv`,
  `TauCeti.EquivariantGroupoidLift.normalizationUnitEquiv`: the strong transformations and adjoint
  equivalence comparing the identity with normalization followed by reconstruction;
* `TauCeti.EquivariantGroupoidLift.normalizationBiequivalence`: the biequivalence between
  `EquivariantGroupoidLift Γ actions` and `LocallyDiscrete (NormalizedTransport Γ actions)`;
* `TauCeti.EquivariantGroupoidLift.normalizationHomEquivalence`,
  `TauCeti.EquivariantGroupoidLift.reconstructionHomEquivalence`: the induced equivalences on
  hom-categories.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055), Chapter 4: strong transformations,
  modifications, mates, and biequivalences.
* Edward Frenkel,
  [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  Cambridge Studies in Advanced Mathematics 103 (2007): equivariant families of local categories
  over parameter groupoids.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory CategoryTheory.Prod
open scoped Pseudofunctor.StrongTrans

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}

/-! ### Naturality of the normalization comparisons on lift morphisms -/

namespace Hom

variable {L L' : EquivariantGroupoidLift Γ actions}

private lemma normalizationJointInv_modification (φ : L ⟶ L') {p q : Γ} (g : p ⟶ q)
    (a : SingleObj.star H ⟶ SingleObj.star H) (x : fiber actions p) :
    (φ.inverseFiberIso q).hom.app ((L.normalizedTransport.jointFunctor (g ×ₘ a)).obj x) ≫
        (L'.fiberEquivalence q).inverse.map
          ((φ.transportIso g).hom.app ((act actions p a).obj x)) ≫
        (L'.normalizationJointIso (g ×ₘ a)).hom.app x =
      (φ.jointFunctor q).map ((L.normalizationJointIso (g ×ₘ a)).hom.app x) ≫
        (φ.joint.naturality (g ×ₘ a).toLoc).hom.toNatTrans.app
          ((L.fiberEquivalence p).inverse.obj x) ≫
        (L'.joint.map (g ×ₘ a).toLoc).toFunctor.map ((φ.inverseFiberIso p).hom.app x) := by
  have hf : (𝟙 p ×ₘ a).toLoc ≫ (g ×ₘ 𝟙 (SingleObj.star H)).toLoc = (g ×ₘ a).toLoc := by
    apply congrArg Quiver.Hom.toLoc
    exact Prod.ext (Category.id_comp _) (Category.comp_id _)
  dsimp only [NormalizedTransport.jointFunctor, normalizedTransport, transport_obj,
    Functor.comp_obj]
  simp only [transportIso_hom_app, normalizationJointIso_hom_app, Functor.map_comp,
    Category.assoc]
  rw [(L'.fiberEquivalence q).unitInv_naturality_assoc,
    (L'.fiberEquivalence q).unitInv_naturality_assoc,
    φ.inverseFiberIso_hom_app_comp_unitInv_assoc]
  apply congrArg ((φ.jointFunctor q).map ((L.fiberEquivalence q).unitInv.app _) ≫ ·)
  rw [← Functor.map_comp_assoc (L'.jointMap g), ← φ.inverseFiberIso_actInverseIso p a x]
  simp only [Functor.map_comp, Category.assoc]
  erw [← (φ.jointMapIso g).hom.naturality_assoc]
  apply congrArg ((φ.jointFunctor q).map ((L.jointMap g).map _) ≫ ·)
  have hn := (L'.joint.mapComp' (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
    (g ×ₘ a).toLoc hf).inv.toNatTrans.naturality ((φ.inverseFiberIso p).hom.app x)
  dsimp only [Cat.Hom.comp_toFunctor, Functor.comp_map, jointMap, jointAct] at hn
  erw [hn]
  dsimp only [Functor.comp_obj]
  have hc := φ.joint.naturality_comp'_hom_app (𝟙 p ×ₘ a).toLoc
    (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ a).toLoc hf ((L.fiberEquivalence p).inverse.obj x)
  rw [hc]
  simp only [jointMapIso_hom_app, jointActIso_hom_app, jointMap, Category.assoc,
    ← Functor.map_comp_assoc, Cat.Hom.inv_hom_id_toNatTrans_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- The inverse-fiber comparisons `φ.inverseFiberIso` assemble into an invertible modification
comparing `φ.normalizedTransportHom.jointHom ≫ L'.normalizationJointInv` with
`L.normalizationJointInv ≫ φ.joint`. -/
noncomputable def normalizationInvJointIso (φ : L ⟶ L') :
    φ.normalizedTransportHom.jointHom ≫ L'.normalizationJointInv ≅
      L.normalizationJointInv ≫ φ.joint :=
  (Pseudofunctor.StrongTrans.isoMk
    (fun X ↦ Cat.Hom.isoMk (φ.inverseFiberIso X.as.1) ≪≫
      (λ_ (L'.fiberEquivalence X.as.1).inverse.toCatHom).symm)
    (fun {X Y} f ↦ by
      obtain ⟨⟨p, ⟨⟩⟩⟩ := X
      obtain ⟨⟨q, ⟨⟩⟩⟩ := Y
      obtain ⟨⟨g, c⟩⟩ := f
      refine Cat.whiskerLeft_comp_eq_comp_whiskerRight _ _ _ _ (fun x ↦ ?_)
      rw [Pseudofunctor.StrongTrans.comp_naturality_hom_app,
        Pseudofunctor.StrongTrans.comp_naturality_hom_app]
      let x' : fiber actions p := x
      have hαp : (Cat.Hom.isoMk (φ.inverseFiberIso p) ≪≫
          (λ_ (L'.fiberEquivalence p).inverse.toCatHom).symm).hom.toNatTrans.app x' =
          (φ.inverseFiberIso p).hom.app x' := by simp
      have hαq : (Cat.Hom.isoMk (φ.inverseFiberIso q) ≪≫
          (λ_ (L'.fiberEquivalence q).inverse.toCatHom).symm).hom.toNatTrans.app
          ((L.normalizedTransport.jointFunctor (g ×ₘ c)).obj x') =
          (φ.inverseFiberIso q).hom.app
            ((L.normalizedTransport.jointFunctor (g ×ₘ c)).obj x') := by simp
      have hj := (NormalizedTransport.Hom.jointHom_naturality_hom_app
        (φ := φ.normalizedTransportHom) { as := (g, c) } x').trans
        (by rw [normalizedTransportHom_transportIso]; rfl)
      have hn' := L'.normalizationJointInv_naturality_hom_app { as := (g, c) } x'
      have hn := L.normalizationJointInv_naturality_hom_app { as := (g, c) } x'
      erw [hαq, hαp, hj, hn', hn]
      exact (φ.normalizationJointInv_modification g c x').trans
        (Category.assoc _ _ _).symm)).symm

@[simp]
lemma normalizationInvJointIso_hom_as_app (φ : L ⟶ L') (X : LocallyDiscrete (Γ × SingleObj H)) :
    (φ.normalizationInvJointIso).hom.as.app X =
      (λ_ (L'.fiberEquivalence X.as.1).inverse.toCatHom).hom ≫
        (Cat.Hom.isoMk (φ.inverseFiberIso X.as.1)).inv :=
  (rfl)

@[simp]
lemma normalizationInvJointIso_inv_as_app (φ : L ⟶ L') (X : LocallyDiscrete (Γ × SingleObj H)) :
    (φ.normalizationInvJointIso).inv.as.app X =
      (Cat.Hom.isoMk (φ.inverseFiberIso X.as.1)).hom ≫
        (λ_ (L'.fiberEquivalence X.as.1).inverse.toCatHom).inv :=
  (rfl)

/-- The lift morphisms `normalizationInv` are natural in `φ : L ⟶ L'` up to a canonical compatible
invertible modification, whose components are the inverse-fiber comparisons of `φ`. -/
noncomputable def normalizationInvNatIso (φ : L ⟶ L') :
    φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv ≅ L.normalizationInv ≫ φ :=
  isoMk φ.normalizationInvJointIso fun p a ↦ by
    obtain ⟨⟨⟩⟩ := a
    refine Cat.Hom₂.ext (NatTrans.ext (funext fun x ↦ ?_))
    let x' : fiber actions p := x
    let x'' : L.normalizedTransport.toLift.jointFiber p := x
    -- Unpack composition and right whiskering of 2-morphisms in `Cat`.
    erw [Cat.Hom₂.comp_app, Cat.whiskerRight_app]
    have hα : (φ.normalizationInvJointIso.hom.as.app
        ((Prod.sectR p (SingleObj H)).toPseudofunctor.obj
          ⟨SingleObj.star H⟩)).toNatTrans.app x =
        (φ.inverseFiberIso p).inv.app x' := by
      rw [normalizationInvJointIso_hom_as_app]
      -- Evaluate the natural transformation composite across the `joint.obj` / `fiber`
      -- identification at `(p, *)`.
      erw [Cat.Hom₂.comp_app, Cat.leftUnitor_hom_toNatTrans, Functor.leftUnitor_hom_app,
        Category.id_comp, Cat.Hom.isoMk_inv, NatTrans.toCatHom₂_toNatTrans]
      rfl
    have hβ : (((Hom.comp L.normalizationInv φ).fiberIso p).hom.as.app
        ⟨SingleObj.star H⟩).toNatTrans.app x'' =
        (φ.fiberFunctorIso p).hom.app ((L.fiberEquivalence p).inverse.obj x') ≫
          (L.fiberEquivalence p).counit.app x' := by
      have h := comp_fiberFunctorIso_hom_app L.normalizationInv φ p x''
      rw [(Hom.comp L.normalizationInv φ).fiberFunctorIso_hom_app p x'',
        L.normalizationInv.fiberFunctorIso_hom_app p x'',
        L.normalizationInv_fiberIso_hom_as_app, Cat.Hom.isoMk_hom,
        NatTrans.toCatHom₂_toNatTrans] at h
      exact h
    have hγ :
        (((Hom.comp φ.normalizedTransportHom.toLiftHom L'.normalizationInv).fiberIso p).hom.as.app
          ⟨SingleObj.star H⟩).toNatTrans.app x'' = (L'.fiberEquivalence p).counit.app x' := by
      have h := comp_fiberFunctorIso_hom_app φ.normalizedTransportHom.toLiftHom
        L'.normalizationInv p x''
      simp only [fiberFunctorIso_hom_app, NormalizedTransport.Hom.toLiftHom_fiberIso_hom_as_app,
        L'.normalizationInv_fiberIso_hom_as_app, Cat.Hom.isoMk_hom,
        NatTrans.toCatHom₂_toNatTrans, Cat.leftUnitor_hom_toNatTrans] at h
      erw [Functor.leftUnitor_hom_app, Category.comp_id] at h
      exact h
    -- Substitute the three component evaluations across the `jointFiber` / `fiber` identification.
    erw [hα, hβ, hγ]
    apply (cancel_epi ((L'.fiberEquivalence p).functor.map
      ((φ.inverseFiberIso p).hom.app x'))).mp
    erw [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact (φ.functor_map_inverseFiberIso_hom_app_comp_counit p x').symm

@[simp]
lemma normalizationInvNatIso_hom_joint (φ : L ⟶ L') :
    (φ.normalizationInvNatIso).hom.joint = φ.normalizationInvJointIso.hom :=
  isoMk_hom_joint _ _

@[simp]
lemma normalizationInvNatIso_inv_joint (φ : L ⟶ L') :
    (φ.normalizationInvNatIso).inv.joint = φ.normalizationInvJointIso.inv :=
  isoMk_inv_joint _ _

/-- The forward morphisms of `normalizationEquivalence` are natural in `φ : L ⟶ L'` up to a
canonical compatible invertible modification, obtained by taking the mate of
`normalizationInvNatIso` across `normalizationEquivalence`. -/
noncomputable def normalizationHomNatIso (φ : L ⟶ L') :
    φ ≫ L'.normalizationEquivalence.hom ≅
      L.normalizationEquivalence.hom ≫ φ.normalizedTransportHom.toLiftHom :=
  asIso ((Bicategory.mateEquiv L.normalizationEquivalence.adj L'.normalizationEquivalence.adj).symm
    φ.normalizationInvNatIso.inv)

/-- The forward naturality modification is the inverse mate of `normalizationInvNatIso.inv`. -/
lemma normalizationHomNatIso_hom (φ : L ⟶ L') :
    (φ.normalizationHomNatIso).hom =
      (Bicategory.mateEquiv L.normalizationEquivalence.adj L'.normalizationEquivalence.adj).symm
        (φ.normalizationInvNatIso).inv :=
  (rfl)

/-- The forward and inverse naturality modifications of `normalizationEquivalence` are mates. -/
lemma mateEquiv_normalizationHomNatIso_hom (φ : L ⟶ L') :
    Bicategory.mateEquiv L.normalizationEquivalence.adj L'.normalizationEquivalence.adj
        (φ.normalizationHomNatIso).hom =
      (φ.normalizationInvNatIso).inv :=
  (Bicategory.mateEquiv L.normalizationEquivalence.adj
    L'.normalizationEquivalence.adj).apply_symm_apply _

/-- Every morphism of lifts factors up to a unique compatible invertible modification through the
reconstruction of its normalized transport comparison. -/
noncomputable def normalizationFactorizationIso (φ : L ⟶ L') :
    φ ≅ L.normalizationEquivalence.hom ≫ φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv :=
  (λ_ φ).symm ≪≫ whiskerRightIso L.normalizationEquivalence.unit φ ≪≫
    α_ L.normalizationEquivalence.hom L.normalizationInv φ ≪≫
    whiskerLeftIso L.normalizationEquivalence.hom φ.normalizationInvNatIso.symm

/-- Two parallel morphisms of lifts with the same normalized transport comparison are isomorphic by
a unique compatible invertible modification. -/
noncomputable def isoOfNormalizedTransportHomEq {φ ψ : L ⟶ L'}
    (h : φ.normalizedTransportHom = ψ.normalizedTransportHom) : φ ≅ ψ :=
  φ.normalizationFactorizationIso ≪≫
    whiskerLeftIso L.normalizationEquivalence.hom
      (whiskerRightIso (eqToIso (congrArg NormalizedTransport.Hom.toLiftHom h))
        L'.normalizationInv) ≪≫
    ψ.normalizationFactorizationIso.symm

/-- Two parallel morphisms of lifts admit a compatible modification if and only if they induce the
same comparison of normalized transports on the prescribed fibers. -/
lemma nonempty_hom₂_iff (φ ψ : L ⟶ L') :
    Nonempty (φ ⟶ ψ) ↔ φ.normalizedTransportHom = ψ.normalizedTransportHom :=
  ⟨fun ⟨Θ⟩ ↦ Θ.normalizedTransportHom_eq, fun h ↦ ⟨(isoOfNormalizedTransportHomEq h).hom⟩⟩

/-- Normalizing the chosen quasi-inverse of a lift morphism gives the inverse comparison in the
groupoid of normalized transports. -/
@[simp]
lemma equivalence_inv_normalizedTransportHom (φ : L ⟶ L') :
    φ.equivalence.inv.normalizedTransportHom = CategoryTheory.inv φ.normalizedTransportHom := by
  have h := Hom₂.normalizedTransportHom_eq φ.equivalence.unit.inv
  rw [comp_normalizedTransportHom, id_normalizedTransportHom] at h
  exact (IsIso.inv_eq_of_hom_inv_id h).symm

end Hom

/-! ### Triangle compatibility of normalization and reconstruction -/

/-- The inverse-fiber comparison of `L.normalizationInv` maps the reconstructed fiber counit by
`(L.fiberEquivalence p).inverse`. -/
lemma normalizationInv_inverseFiberIso_hom_app (L : EquivariantGroupoidLift Γ actions) (p : Γ)
    (x : fiber actions p) :
    (L.normalizationInv.inverseFiberIso p).hom.app x =
      (L.fiberEquivalence p).inverse.map
        ((L.normalizedTransport.toLift.fiberEquivalence p).counit.app x) := by
  let ε := (L.normalizedTransport.toLift.fiberEquivalence p).counit.app x
  apply (L.fiberEquivalence p).functor.map_injective
  apply (cancel_mono ((L.fiberEquivalence p).counit.app x)).mp
  rw [Hom.functor_map_inverseFiberIso_hom_app_comp_counit, Hom.fiberFunctorIso_hom_app,
    L.normalizationInv_fiberIso_hom_as_app, Cat.Hom.isoMk_hom, NatTrans.toCatHom₂_toNatTrans]
  exact ((L.fiberEquivalence p).counit_naturality ε).symm

/-- Normalizing `L.normalizationInv` recovers the canonical return comparison
`toLiftNormalizedTransportIso` of `L.normalizedTransport`. -/
@[simp]
lemma normalizationInv_normalizedTransportHom (L : EquivariantGroupoidLift Γ actions) :
    L.normalizationInv.normalizedTransportHom =
      (NormalizedTransport.toLiftNormalizedTransportIso L.normalizedTransport).hom := by
  refine NormalizedTransport.Hom.ext fun p q g ↦ Iso.ext (NatTrans.ext (funext fun x ↦ ?_))
  let N := L.normalizedTransport
  let y : fiber actions p := (N.toLift.fiberEquivalence p).inverse.obj x
  let ε : y ⟶ x := (N.toLift.fiberEquivalence p).counit.app x
  rw [Hom.normalizedTransportHom_transportIso,
    NormalizedTransport.toLiftNormalizedTransportIso_hom_transportIso,
    Hom.transportIso_hom_app, NormalizedTransport.toLiftTransportIso_hom_app]
  have hnat : (L.normalizationJointInv.naturality
      (g ×ₘ 𝟙 (SingleObj.star H)).toLoc).hom.toNatTrans.app y =
      (L.fiberEquivalence q).unitInv.app
        ((L.jointMap g).obj ((L.fiberEquivalence p).inverse.obj
          ((act actions p (𝟙 (SingleObj.star H))).obj y))) ≫
        (L.jointMap g).map
          ((L.fiberEquivalence p).inverse.map ((actId actions p).hom.app y)) := by
    rw [L.normalizationJointInv_naturality_hom_app, L.normalizationJointIso_hom_app]
    have hm := L.joint.mapComp'_id_comp_inv_app (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
      ((L.fiberEquivalence p).inverse.obj y)
    have hid : (L.joint.mapId ⟨(p, SingleObj.star H)⟩).hom.toNatTrans.app
        ((L.fiberEquivalence p).inverse.obj y) =
        (L.jointMapId p).hom.app ((L.fiberEquivalence p).inverse.obj y) := by
      simp only [jointMapId_hom_app, ← prod_id, Quiver.Hom.id_toLoc,
        Pseudofunctor.mapId'_eq_mapId]
    erw [hm, hid]
    dsimp only [jointMap]
    -- Project `(g ×ₘ 𝟙 _).toLoc.as` to `(g, 𝟙 _)` when matching `actInverseIso_actId`.
    erw [← CategoryTheory.Functor.map_comp, L.actInverseIso_actId]
    rfl
  have hfiso : (L.normalizationInv.fiberFunctorIso q).inv.app
      ((N.toLift.jointMap g).obj y) =
      (L.fiberEquivalence q).counitInv.app ((N.toLift.jointMap g).obj y) := by
    rw [Hom.fiberFunctorIso_inv_app, L.normalizationInv_fiberIso_inv_as_app, Cat.Hom.isoMk_inv,
      NatTrans.toCatHom₂_toNatTrans]
  -- Evaluate the joint naturality and fiber comparison cells on the reconstructed fiber carrier.
  erw [Hom.jointMapIso_hom_app, hnat, hfiso, L.normalizationInv_inverseFiberIso_hom_app p x]
  erw [CategoryTheory.Functor.map_comp, Category.assoc,
    (L.fiberEquivalence q).counitInv_functor_comp_assoc]
  have hend : (L.fiberEquivalence q).functor.map
      ((L.jointMap g).map ((L.fiberEquivalence p).inverse.map ((actId actions p).hom.app y))) ≫
      (L.fiberEquivalence q).functor.map
        ((L.jointMap g).map ((L.fiberEquivalence p).inverse.map ε)) =
      (L.transport g).map ((act actions p (𝟙 (SingleObj.star H))).map ε) ≫
        (L.transport g).map ((actId actions p).hom.app x) := by
    dsimp only [transport, Functor.comp_map]
    simp only [← CategoryTheory.Functor.map_comp, (actId actions p).hom.naturality]
    rfl
  exact hend

/-- Normalizing the forward morphism of `L.normalizationEquivalence` recovers the inverse return
comparison `(toLiftNormalizedTransportIso L.normalizedTransport).inv`. -/
lemma normalizationEquivalence_hom_normalizedTransportHom
    (L : EquivariantGroupoidLift Γ actions) :
    L.normalizationEquivalence.hom.normalizedTransportHom =
      (NormalizedTransport.toLiftNormalizedTransportIso L.normalizedTransport).inv := by
  simp

/-- Reconstructing a comparison of normalized transports and conjugating by
`normalizationEquivalence` recovers the original comparison upon normalization. -/
lemma normalizedTransportHom_reconstruction {L L' : EquivariantGroupoidLift Γ actions}
    (χ : L.normalizedTransport ⟶ L'.normalizedTransport) :
    (L.normalizationEquivalence.hom ≫ χ.toLiftHom ≫ L'.normalizationInv).normalizedTransportHom =
      χ := by
  rw [Hom.comp_normalizedTransportHom, Hom.comp_normalizedTransportHom,
    normalizationEquivalence_hom_normalizedTransportHom, normalizationInv_normalizedTransportHom,
    NormalizedTransport.toLiftNormalizedTransportIso_hom_naturality, Iso.inv_hom_id_assoc]

/-! ### The normalization unit and biequivalence -/

section Biequivalence

variable (actions)

/-- The forward morphisms of `normalizationEquivalence` assemble into a strong transformation from
the identity pseudofunctor on `EquivariantGroupoidLift Γ actions` to normalization followed by
reconstruction. Uniqueness of compatible modifications discharges the coherence axioms. -/
-- Expose the carrier so the dependent unit and counit component equations of
-- `normalizationUnitEquiv` retain their literal lift-morphism endpoints.
@[expose] noncomputable def normalizationUnitHom :
    Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ⟶
      (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) where
  app L := L.normalizationEquivalence.hom
  naturality φ := φ.normalizationHomNatIso
  naturality_naturality _ := @Subsingleton.elim _ (subsingleton₂ _ _) _ _
  naturality_id _ := @Subsingleton.elim _ (subsingleton₂ _ _) _ _
  naturality_comp _ _ := @Subsingleton.elim _ (subsingleton₂ _ _) _ _

@[simp]
lemma normalizationUnitHom_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitHom actions).app L = L.normalizationEquivalence.hom :=
  (rfl)

@[simp]
lemma normalizationUnitHom_naturality {L L' : EquivariantGroupoidLift Γ actions} (φ : L ⟶ L') :
    (normalizationUnitHom actions).naturality φ = φ.normalizationHomNatIso :=
  (rfl)

/-- The morphisms `normalizationInv` assemble into a strong transformation from normalization
followed by reconstruction back to the identity pseudofunctor on
`EquivariantGroupoidLift Γ actions`. -/
-- Expose the carrier so the dependent unit and counit component equations of
-- `normalizationUnitEquiv` retain their literal lift-morphism endpoints.
@[expose] noncomputable def normalizationUnitInv :
    (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) ⟶
      Pseudofunctor.id (EquivariantGroupoidLift Γ actions) where
  app L := L.normalizationInv
  naturality φ := φ.normalizationInvNatIso
  naturality_naturality _ := @Subsingleton.elim _ (subsingleton₂ _ _) _ _
  naturality_id _ := @Subsingleton.elim _ (subsingleton₂ _ _) _ _
  naturality_comp _ _ := @Subsingleton.elim _ (subsingleton₂ _ _) _ _

@[simp]
lemma normalizationUnitInv_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitInv actions).app L = L.normalizationInv :=
  (rfl)

@[simp]
lemma normalizationUnitInv_naturality {L L' : EquivariantGroupoidLift Γ actions} (φ : L ⟶ L') :
    (normalizationUnitInv actions).naturality φ = φ.normalizationInvNatIso :=
  (rfl)

/-- The identity pseudofunctor on `EquivariantGroupoidLift Γ actions` is equivalent to
normalization followed by reconstruction, with objectwise components `normalizationEquivalence`. -/
-- Expose the body so the unit and counit component equations below typecheck directly against
-- `normalizationUnitHom` and `normalizationUnitInv`.
@[expose] noncomputable def normalizationUnitEquiv :
    Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ≌
      (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) where
  hom := normalizationUnitHom actions
  inv := normalizationUnitInv actions
  unit :=
    { hom :=
        { as :=
            { app L := L.normalizationEquivalence.unit.hom
              naturality _ := @Subsingleton.elim _ (subsingleton₂ _ _) _ _ } }
      inv :=
        { as :=
            { app L := L.normalizationEquivalence.unit.inv
              naturality _ := @Subsingleton.elim _ (subsingleton₂ _ _) _ _ } }
      hom_inv_id := Pseudofunctor.StrongTrans.homCategory.ext fun _ ↦
        @Subsingleton.elim _ (subsingleton₂ _ _) _ _
      inv_hom_id := Pseudofunctor.StrongTrans.homCategory.ext fun _ ↦
        @Subsingleton.elim _ (subsingleton₂ _ _) _ _ }
  counit :=
    { hom :=
        { as :=
            { app L := L.normalizationEquivalence.counit.hom
              naturality _ := @Subsingleton.elim _ (subsingleton₂ _ _) _ _ } }
      inv :=
        { as :=
            { app L := L.normalizationEquivalence.counit.inv
              naturality _ := @Subsingleton.elim _ (subsingleton₂ _ _) _ _ } }
      hom_inv_id := Pseudofunctor.StrongTrans.homCategory.ext fun _ ↦
        @Subsingleton.elim _ (subsingleton₂ _ _) _ _
      inv_hom_id := Pseudofunctor.StrongTrans.homCategory.ext fun _ ↦
        @Subsingleton.elim _ (subsingleton₂ _ _) _ _ }
  left_triangle := Iso.ext (Pseudofunctor.StrongTrans.homCategory.ext fun _ ↦
    @Subsingleton.elim _ (subsingleton₂ _ _) _ _)

@[simp]
lemma normalizationUnitEquiv_hom :
    (normalizationUnitEquiv actions).hom = normalizationUnitHom actions :=
  (rfl)

@[simp]
lemma normalizationUnitEquiv_inv :
    (normalizationUnitEquiv actions).inv = normalizationUnitInv actions :=
  (rfl)

-- Keep these dependent modification component equations named: the implicit endpoints of
-- `StrongTrans.Hom.as` mention `normalizationUnitEquiv.hom` and `normalizationUnitEquiv.inv`, which
-- simplify under the lemmas above.
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

/-- The biequivalence between the bicategory of coherent equivariant lifts and the locally discrete
bicategory of normalized transport data on the prescribed fibers. Every `1`-morphism of lifts is
already an equivalence and every hom-category of lifts is a thin groupoid, so the full bicategory
of lifts participates in this biequivalence without restricting morphisms. -/
-- Expose the record so the types of `unitEquiv` and `counitEquiv`, which mention the `functor` and
-- `inverse` projections, reduce directly in the projection lemmas below.
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

/-- Coherent equivariant lifts exist if and only if normalized transport data exist on the
prescribed fibers. -/
lemma nonempty_iff_normalizedTransport :
    Nonempty (EquivariantGroupoidLift Γ actions) ↔ Nonempty (NormalizedTransport Γ actions) :=
  ⟨fun ⟨L⟩ ↦ ⟨L.normalizedTransport⟩, fun ⟨N⟩ ↦ ⟨N.toLift⟩⟩

end Biequivalence

/-! ### Equivalences on hom-categories -/

section HomEquivalence

private noncomputable def normalizationHomInverse (L L' : EquivariantGroupoidLift Γ actions) :
    ((normalizationPseudofunctor actions).obj L ⟶
      (normalizationPseudofunctor actions).obj L') ⥤ (L ⟶ L') :=
  (reconstructionPseudofunctor actions).mapFunctor
      ((normalizationPseudofunctor actions).obj L)
      ((normalizationPseudofunctor actions).obj L') ⋙
    postcomp _ L'.normalizationInv ⋙
    precomp _ L.normalizationEquivalence.hom

private lemma normalizationHomInverse_obj (L L' : EquivariantGroupoidLift Γ actions)
    (χ : (normalizationPseudofunctor actions).obj L ⟶
      (normalizationPseudofunctor actions).obj L') :
    (normalizationHomInverse L L').obj χ =
      L.normalizationEquivalence.hom ≫ χ.as.toLiftHom ≫ L'.normalizationInv := by
  dsimp only [normalizationHomInverse, Functor.comp_obj]
  -- Evaluate `precomp`, `postcomp`, and `mapFunctor` across the exposed pseudofunctor objects.
  erw [precomp_obj, postcomp_obj, PrelaxFunctor.mapFunctor_obj]
  rfl

/-- Normalization induces an adjoint equivalence between the thin hom-groupoid `L ⟶ L'` of lifts
and the discrete hom-category of normalized transport comparisons from `L.normalizedTransport` to
`L'.normalizedTransport`. -/
noncomputable def normalizationHomEquivalence (L L' : EquivariantGroupoidLift Γ actions) :
    (L ⟶ L') ≌
      ((normalizationPseudofunctor actions).obj L ⟶
        (normalizationPseudofunctor actions).obj L') where
  functor := (normalizationPseudofunctor actions).mapFunctor L L'
  inverse := normalizationHomInverse L L'
  unitIso := NatIso.ofComponents
    (fun φ ↦ φ.normalizationFactorizationIso ≪≫
      eqToIso (by
        have h := normalizationHomInverse_obj L L'
          (((normalizationPseudofunctor actions).mapFunctor L L').obj φ)
        rw [PrelaxFunctor.mapFunctor_obj] at h
        exact h.symm))
    (fun _ ↦ @Subsingleton.elim _ (subsingleton₂ _ _) _ _)
  counitIso := NatIso.ofComponents
    (fun χ ↦ eqToIso (Discrete.ext (by
      have h : (((normalizationHomInverse L L' ⋙
          (normalizationPseudofunctor actions).mapFunctor L L').obj χ)).as = χ.as := by
        rw [Functor.comp_obj, PrelaxFunctor.mapFunctor_obj, normalizationHomInverse_obj]
        exact normalizedTransportHom_reconstruction χ.as
      exact h)))
    (fun _ ↦ Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

@[simp]
lemma normalizationHomEquivalence_functor (L L' : EquivariantGroupoidLift Γ actions) :
    (normalizationHomEquivalence L L').functor =
      (normalizationPseudofunctor actions).mapFunctor L L' :=
  (rfl)

@[simp]
lemma normalizationHomEquivalence_inverse_obj (L L' : EquivariantGroupoidLift Γ actions)
    (χ : (normalizationPseudofunctor actions).obj L ⟶
      (normalizationPseudofunctor actions).obj L') :
    (normalizationHomEquivalence L L').inverse.obj χ =
      L.normalizationEquivalence.hom ≫ χ.as.toLiftHom ≫ L'.normalizationInv :=
  normalizationHomInverse_obj L L' χ

/-- The normalization pseudofunctor is a local equivalence on every hom-category. -/
instance isEquivalence_normalizationPseudofunctor_mapFunctor
    (L L' : EquivariantGroupoidLift Γ actions) :
    ((normalizationPseudofunctor actions).mapFunctor L L').IsEquivalence :=
  (normalizationHomEquivalence L L').isEquivalence_functor

/-- Morphisms of lifts `L ⟶ L'` exist if and only if comparisons of their normalized transports
exist. -/
lemma nonempty_hom_iff (L L' : EquivariantGroupoidLift Γ actions) :
    Nonempty (L ⟶ L') ↔ Nonempty (L.normalizedTransport ⟶ L'.normalizedTransport) :=
  ⟨fun ⟨φ⟩ ↦ ⟨φ.normalizedTransportHom⟩,
    fun ⟨χ⟩ ↦ ⟨L.normalizationEquivalence.hom ≫ χ.toLiftHom ≫ L'.normalizationInv⟩⟩

private noncomputable def reconstructionHomInverse
    (N N' : LocallyDiscrete (NormalizedTransport Γ actions)) :
    ((reconstructionPseudofunctor actions).obj N ⟶
      (reconstructionPseudofunctor actions).obj N') ⥤ (N ⟶ N') :=
  (normalizationPseudofunctor actions).mapFunctor
      ((reconstructionPseudofunctor actions).obj N)
      ((reconstructionPseudofunctor actions).obj N') ⋙
    postcomp _ ((normalizationCounitHom actions).app N') ⋙
    precomp _ ((normalizationCounitInv actions).app N)

private lemma reconstructionHomInverse_obj_as
    (N N' : LocallyDiscrete (NormalizedTransport Γ actions))
    (φ : (reconstructionPseudofunctor actions).obj N ⟶
      (reconstructionPseudofunctor actions).obj N') :
    ((reconstructionHomInverse N N').obj φ).as =
      (NormalizedTransport.toLiftNormalizedTransportIso N.as).inv ≫
        ((normalizationPseudofunctor actions).map φ).as ≫
        (NormalizedTransport.toLiftNormalizedTransportIso N'.as).hom := by
  dsimp only [reconstructionHomInverse, Functor.comp_obj]
  -- Unpack composition in `LocallyDiscrete` to the underlying `NormalizedTransport` morphisms.
  erw [precomp_obj, postcomp_obj, PrelaxFunctor.mapFunctor_obj,
    normalizationCounitInv_app, normalizationCounitHom_app]
  rfl

/-- Reconstruction induces an adjoint equivalence between the discrete hom-category `N ⟶ N'` of
normalized transports and the hom-groupoid `N.as.toLift ⟶ N'.as.toLift` of reconstructed lifts. -/
noncomputable def reconstructionHomEquivalence
    (N N' : LocallyDiscrete (NormalizedTransport Γ actions)) :
    (N ⟶ N') ≌
      ((reconstructionPseudofunctor actions).obj N ⟶
        (reconstructionPseudofunctor actions).obj N') where
  functor := (reconstructionPseudofunctor actions).mapFunctor N N'
  inverse := reconstructionHomInverse N N'
  unitIso := NatIso.ofComponents
    (fun χ ↦ eqToIso (Discrete.ext (by
      have h : (((reconstructionPseudofunctor actions).mapFunctor N N' ⋙
          reconstructionHomInverse N N').obj χ).as = χ.as := by
        dsimp only [Functor.comp_obj]
        rw [reconstructionHomInverse_obj_as, PrelaxFunctor.mapFunctor_obj]
        -- Identify `(normalizationPseudofunctor.map (reconstructionPseudofunctor.map χ)).as` with
        -- `χ.as.toLiftHom.normalizedTransportHom` to apply return naturality.
        erw [NormalizedTransport.toLiftNormalizedTransportIso_hom_naturality,
          Iso.inv_hom_id_assoc]
      exact h.symm)))
    (fun _ ↦ Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents
    (fun φ ↦
      eqToIso (PrelaxFunctor.mapFunctor_obj
        (reconstructionPseudofunctor actions).toPrelaxFunctor N N'
        ((reconstructionHomInverse N N').obj φ)) ≪≫
        Hom.isoOfNormalizedTransportHomEq (by
          have h : (((reconstructionPseudofunctor actions).map
              ((reconstructionHomInverse N N').obj φ))).normalizedTransportHom =
              φ.normalizedTransportHom := by
            erw [← cancel_mono (NormalizedTransport.toLiftNormalizedTransportIso N'.as).hom,
              NormalizedTransport.toLiftNormalizedTransportIso_hom_naturality,
              reconstructionHomInverse_obj_as, Iso.hom_inv_id_assoc]
            rfl
          exact h))
    (fun _ ↦ @Subsingleton.elim _ (subsingleton₂ _ _) _ _)
  functor_unitIso_comp _ := @Subsingleton.elim _ (subsingleton₂ _ _) _ _

@[simp]
lemma reconstructionHomEquivalence_functor
    (N N' : LocallyDiscrete (NormalizedTransport Γ actions)) :
    (reconstructionHomEquivalence N N').functor =
      (reconstructionPseudofunctor actions).mapFunctor N N' :=
  (rfl)

-- Keep this equation un-tagged for `simp`: its binder mentions
-- `(reconstructionPseudofunctor actions).obj N`, which simplifies via
-- `reconstructionPseudofunctor_obj`.
lemma reconstructionHomEquivalence_inverse_obj_as
    (N N' : LocallyDiscrete (NormalizedTransport Γ actions))
    (φ : (reconstructionPseudofunctor actions).obj N ⟶
      (reconstructionPseudofunctor actions).obj N') :
    ((reconstructionHomEquivalence N N').inverse.obj φ).as =
      (NormalizedTransport.toLiftNormalizedTransportIso N.as).inv ≫
        ((normalizationPseudofunctor actions).map φ).as ≫
        (NormalizedTransport.toLiftNormalizedTransportIso N'.as).hom :=
  reconstructionHomInverse_obj_as N N' φ

/-- The reconstruction pseudofunctor is a local equivalence on every hom-category. -/
instance isEquivalence_reconstructionPseudofunctor_mapFunctor
    (N N' : LocallyDiscrete (NormalizedTransport Γ actions)) :
    ((reconstructionPseudofunctor actions).mapFunctor N N').IsEquivalence :=
  (reconstructionHomEquivalence N N').isEquivalence_functor

/-- Reconstructed morphisms of lifts admit a compatible modification if and only if the original
normalized transport comparisons are equal. -/
lemma NormalizedTransport.Hom.nonempty_toLiftHom_hom₂_iff
    {N N' : NormalizedTransport Γ actions} (φ ψ : N ⟶ N') :
    Nonempty (φ.toLiftHom ⟶ ψ.toLiftHom) ↔ φ = ψ := by
  rw [Hom.nonempty_hom₂_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ congrArg (Hom.normalizedTransportHom ∘ Hom.toLiftHom) h⟩
  have h' := congrArg (· ≫ (toLiftNormalizedTransportIso N').hom) h
  rw [toLiftNormalizedTransportIso_hom_naturality,
    toLiftNormalizedTransportIso_hom_naturality] at h'
  exact (cancel_epi (toLiftNormalizedTransportIso N).hom).mp h'

end HomEquivalence

end TauCeti.EquivariantGroupoidLift
