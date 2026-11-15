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
import Mathlib.CategoryTheory.Bicategory.Functor.Cat

/-!
# The biequivalence between equivariant groupoid lifts and normalized transport

An equivariant groupoid lift `L` of prescribed `H`-actions along `Γ` is equivalent to the
reconstruction `L.normalizedTransport.toLift` of its normalized transport through
`L.normalizationEquivalence`, whose inverse `L.normalizationInv` acts on the joint fibers by the
chosen inverse fiber comparisons `(L.fiberEquivalence p).inverse` and on the prescribed fibers by
their counits. Conversely, normalizing the lift `N.toLift` reconstructed from normalized transport
data `N` recovers `N` up to the natural isomorphism `N.toLiftNormalizedTransportIso`, giving the
counit equivalence `normalizationCounitEquiv`.

This file proves that the objectwise equivalences `L.normalizationEquivalence` are pseudonatural in
morphisms `φ : L ⟶ L'` of lifts and assembles the full biequivalence between the bicategory of
equivariant lifts and the locally discrete bicategory of normalized transports:

* `Hom.normalizationInvIso`: for `φ : L ⟶ L'`, an isomorphism of lift morphisms
  `φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv ≅ L.normalizationInv ≫ φ` whose
  inverse joint modification has components the inverse-fiber comparisons `φ.inverseFiberIso p`;
* `Hom.normalizationHomIso`: the mate isomorphism
  `φ ≫ L'.normalizationEquivalence.hom ≅ L.normalizationEquivalence.hom ≫
  φ.normalizedTransportHom.toLiftHom`, obtained from `φ.normalizationInvIso.inv` through
  `Bicategory.mateEquiv` and automatic invertibility of compatible modifications;
* `normalizationUnitHom`, `normalizationUnitInv`, `normalizationUnitEquiv`: the strong
  transformations between the identity of `EquivariantGroupoidLift Γ actions` and normalization
  followed by reconstruction, together with their unit and counit modifications;
* `normalizationBiequivalence`: the resulting biequivalence
  `TauCeti.Biequivalence (EquivariantGroupoidLift Γ actions)
  (LocallyDiscrete (NormalizedTransport Γ actions))`;
* `normalizationInv_normalizedTransportHom`: normalizing `L.normalizationInv` recovers the counit
  component `(L.normalizedTransport.toLiftNormalizedTransportIso).hom` on the nose;
* `normalizationHomEquivalence`: for any two lifts `L` and `L'`, normalization induces an
  equivalence of hom-categories `(L ⟶ L') ≌ (⟨L.normalizedTransport⟩ ⟶ ⟨L'.normalizedTransport⟩)`.
  In particular, two parallel lift morphisms admit a compatible modification if and only if they
  induce equal morphisms of normalized transports (`Hom.nonempty_hom_iff`).

Because the hom-categories of `EquivariantGroupoidLift Γ actions` are thin groupoids, the
coherence axioms for strong transformations and the triangle identity for modifications into
`EquivariantGroupoidLift Γ actions` hold automatically once the naturality `2`-isomorphisms exist.
The mathematical content of the unit assembly therefore lies in constructing the compatible joint
modification `Hom.normalizationInvIso` along all parameter and symmetry arrows.

## Main declarations

* `TauCeti.EquivariantGroupoidLift.Hom.normalizationInvIso`: naturality of `normalizationInv` for
  morphisms of lifts;
* `TauCeti.EquivariantGroupoidLift.Hom.normalizationHomIso`: naturality of
  `normalizationEquivalence.hom` for morphisms of lifts;
* `TauCeti.EquivariantGroupoidLift.normalizationUnitHom`,
  `TauCeti.EquivariantGroupoidLift.normalizationUnitInv`: the forward and inverse strong
  transformations of the normalization unit;
* `TauCeti.EquivariantGroupoidLift.normalizationUnitEquiv`: the unit equivalence between the
  identity pseudofunctor and normalization followed by reconstruction;
* `TauCeti.EquivariantGroupoidLift.normalizationBiequivalence`: the biequivalence between
  `EquivariantGroupoidLift Γ actions` and `LocallyDiscrete (NormalizedTransport Γ actions)`;
* `TauCeti.EquivariantGroupoidLift.normalizationInv_normalizedTransportHom`: triangle identity
  comparing the normalized unit inverse with the counit;
* `TauCeti.EquivariantGroupoidLift.liftOfNormalizedTransportHom`: reconstruction of a lift morphism
  from a morphism of normalized transports;
* `TauCeti.EquivariantGroupoidLift.Hom.nonempty_hom_iff`: two parallel lift morphisms admit a
  compatible modification if and only if their induced normalized transport morphisms are equal;
* `TauCeti.EquivariantGroupoidLift.normalizationHomEquivalence`: equivalence of hom-categories
  induced by normalization.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055), Chapters 4 and 6: strong transformations,
  modifications, mates and biequivalences.
* Edward Frenkel,
  [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  Cambridge Studies in Advanced Mathematics 103 (2007), §1.3: families of local categories over a
  groupoid of parameters and their equivariant transport.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift.Hom

open CategoryTheory Bicategory CategoryTheory.Prod Pseudofunctor.StrongTrans

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  {L L' : EquivariantGroupoidLift Γ actions}

/-- Along a joint arrow `(g, a)`, the inverse-fiber comparison of `φ` intertwines the joint
naturality cell of `L.normalizationInv ≫ φ` with that of
`φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv`. -/
@[reassoc]
lemma inverseFiberIso_hom_app_comp_normalizationJointIso (φ : L ⟶ L') {p q : Γ} (g : p ⟶ q)
    (a : SingleObj.star H ⟶ SingleObj.star H) (x : fiber actions p) :
    (φ.inverseFiberIso q).hom.app ((L.normalizedTransport.jointFunctor (g ×ₘ a)).obj x) ≫
      (L'.fiberEquivalence q).inverse.map
        ((φ.transportIso g).hom.app ((act actions p a).obj x)) ≫
      (L'.normalizationJointIso (g ×ₘ a)).hom.app x =
    (φ.jointFunctor q).map ((L.normalizationJointIso (g ×ₘ a)).hom.app x) ≫
      (φ.joint.naturality (g ×ₘ a).toLoc).hom.toNatTrans.app
        ((L.fiberEquivalence p).inverse.obj x) ≫
      (L'.joint.map (g ×ₘ a).toLoc).toFunctor.map ((φ.inverseFiberIso p).hom.app x) := by
  dsimp only [NormalizedTransport.jointFunctor, normalizedTransport,
    EquivariantGroupoidLift.transport_obj, Functor.comp_obj]
  rw [transportIso_hom_app, normalizationJointIso_hom_app, normalizationJointIso_hom_app]
  simp only [Functor.map_comp, Category.assoc]
  -- Cancel the target fiber comparison at `q` using unit naturality and the unit mate equation.
  rw [← (L'.fiberEquivalence q).inverse.map_comp_assoc
    ((L'.fiberEquivalence q).functor.map ((φ.jointMapIso g).hom.app _)),
    ← (L'.fiberEquivalence q).functor.map_comp]
  erw [(L'.fiberEquivalence q).unitInv_naturality_assoc,
    φ.inverseFiberIso_hom_app_comp_unitInv_assoc]
  simp only [Category.assoc]
  -- Commute the source inverse-fiber comparison past the prescribed `H`-action.
  rw [← (L'.jointMap g).map_comp_assoc, ← φ.inverseFiberIso_actInverseIso]
  simp only [Functor.map_comp, Category.assoc]
  erw [← (φ.jointMapIso g).hom.naturality_assoc]
  -- Move the remaining source comparison past the target joint compositor.
  let c' := L'.joint.mapComp' (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
    (g ×ₘ a).toLoc (by simp [← Quiver.Hom.comp_toLoc])
  have hc' := c'.inv.toNatTrans.naturality ((φ.inverseFiberIso p).hom.app x)
  dsimp only [Cat.Hom.comp_toFunctor, Functor.comp_map, jointMap, jointAct] at hc'
  rw [hc']
  -- Recombine the parameter and symmetry naturality cells of `φ.joint` along `(g, a)`.
  have hcomp := φ.joint.naturality_comp'_hom_app (𝟙 p ×ₘ a).toLoc
    (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ a).toLoc (by simp [← Quiver.Hom.comp_toLoc])
    ((L.fiberEquivalence p).inverse.obj x)
  rw [hcomp]
  dsimp only [c', jointFunctor, jointMap, jointAct]
  simp only [Category.assoc]
  rw [← ((φ.joint.app ⟨(q, SingleObj.star H)⟩).toFunctor).map_comp_assoc
    ((L.joint.mapComp' (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ a).toLoc
      (by simp [← Quiver.Hom.comp_toLoc])).inv.toNatTrans.app
      ((L.fiberEquivalence p).inverse.obj x)),
    Cat.Hom.inv_hom_id_toNatTrans_app]
  erw [CategoryTheory.Functor.map_id]
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_obj, Functor.comp_map,
    jointMapIso_hom_app, jointActIso_hom_app, Category.id_comp]

private lemma normalizationInv_modification_naturality (φ : L ⟶ L')
    {X Y : LocallyDiscrete (Γ × SingleObj H)} (f : X ⟶ Y) (x : fiber actions X.as.1) :
    (φ.inverseFiberIso Y.as.1).hom.app ((L.normalizedTransport.jointFunctor f.as).obj x) ≫
        (((φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv).joint.naturality
          f).hom.toNatTrans.app x) =
      (((L.normalizationInv ≫ φ).joint.naturality f).hom.toNatTrans.app x) ≫
        (L'.joint.map f).toFunctor.map ((φ.inverseFiberIso X.as.1).hom.app x) := by
  obtain ⟨⟨p, ⟨⟩⟩⟩ := X
  obtain ⟨⟨q, ⟨⟩⟩⟩ := Y
  obtain ⟨⟨g, a⟩⟩ := f
  erw [Pseudofunctor.StrongTrans.comp_naturality_hom_app,
    Pseudofunctor.StrongTrans.comp_naturality_hom_app,
    NormalizedTransport.Hom.jointHom_naturality_hom_app,
    L'.normalizationJointInv_naturality_hom_app,
    L.normalizationJointInv_naturality_hom_app,
    normalizedTransportHom_transportIso]
  exact (φ.inverseFiberIso_hom_app_comp_normalizationJointIso g a x).trans
    (Category.assoc _ _ _).symm

private lemma normalizationInv_modification_comm (φ : L ⟶ L') (p : Γ)
    (a : LocallyDiscrete (SingleObj H)) :
    (Cat.Hom.isoMk (φ.inverseFiberIso p) ≪≫
        (λ_ (L'.fiberEquivalence p).inverse.toCatHom).symm).hom ▷
      (L'.comparison p).app a ≫
        ((φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv).fiberIso p).hom.as.app a =
      ((L.normalizationInv ≫ φ).fiberIso p).hom.as.app a := by
  obtain ⟨⟨⟩⟩ := a
  ext x
  rw [EquivariantGroupoidLift.comp_fiberIso, EquivariantGroupoidLift.comp_fiberIso,
    comp_fiberIso_hom_as_app, comp_fiberIso_hom_as_app,
    NormalizedTransport.Hom.toLiftHom_fiberIso_hom_as_app,
    normalizationInv_fiberIso_hom_as_app, normalizationInv_fiberIso_hom_as_app]
  let I : fiber actions p ⟶ fiber actions p := 𝟙 (fiber actions p)
  let R' : fiber actions p ⟶ L'.jointFiber p := (L'.fiberEquivalence p).inverse.toCatHom
  let R : fiber actions p ⟶ L.jointFiber p := (L.fiberEquivalence p).inverse.toCatHom
  let F : L.jointFiber p ⟶ L'.jointFiber p := φ.joint.app ⟨(p, SingleObj.star H)⟩
  let E' : L'.jointFiber p ⟶ fiber actions p := (L'.comparison p).app ⟨SingleObj.star H⟩
  let E : L.jointFiber p ⟶ fiber actions p := (L.comparison p).app ⟨SingleObj.star H⟩
  let m : R ≫ F ⟶ I ≫ R' := (Cat.Hom.isoMk (φ.inverseFiberIso p) ≪≫ (λ_ R').symm).hom
  let c' : R' ≫ E' ⟶ I := (Cat.Hom.isoMk (L'.fiberEquivalence p).counitIso).hom
  let c : R ≫ E ⟶ I := (Cat.Hom.isoMk (L.fiberEquivalence p).counitIso).hom
  let f : F ≫ E' ⟶ E := (φ.fiberIso p).hom.as.app ⟨SingleObj.star H⟩
  -- Express both sides using the named `Cat` morphisms so component simplification applies.
  change (m ▷ E' ≫ ((α_ I R' E').hom ≫ I ◁ c' ≫ (λ_ I).hom)).toNatTrans.app x =
    ((α_ R F E').hom ≫ R ◁ f ≫ c).toNatTrans.app x
  simp only [Cat.Hom.toNatTrans_comp, NatTrans.comp_app, Cat.whiskerLeft_app,
    Cat.whiskerRight_app, Cat.associator_hom_app, Cat.leftUnitor_hom_toNatTrans,
    Functor.leftUnitor_hom_app, eqToHom_refl, Category.id_comp]
  simpa [I, R', R, F, E', E, m, c', c, f, EquivariantGroupoidLift.fiberEquivalence_functor,
    fiberFunctorIso_hom_app, CategoryTheory.Equivalence.counit] using
    φ.functor_map_inverseFiberIso_hom_app_comp_counit p x

/-- Naturality of `normalizationInv` with respect to a morphism `φ : L ⟶ L'` of lifts.
Its inverse joint modification has components the inverse-fiber comparisons `φ.inverseFiberIso p`,
and its forward joint modification has components their inverses. -/
noncomputable def normalizationInvIso (φ : L ⟶ L') :
    φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv ≅ L.normalizationInv ≫ φ :=
  (isoMk
    (Pseudofunctor.StrongTrans.isoMk
      (fun X ↦ Cat.Hom.isoMk (φ.inverseFiberIso X.as.1) ≪≫
        (λ_ (L'.fiberEquivalence X.as.1).inverse.toCatHom).symm)
      (fun {X Y} f ↦
        Cat.whiskerLeft_comp_eq_comp_whiskerRight
          (Cat.Hom.isoMk (φ.inverseFiberIso X.as.1) ≪≫
            (λ_ (L'.fiberEquivalence X.as.1).inverse.toCatHom).symm).hom
          (Cat.Hom.isoMk (φ.inverseFiberIso Y.as.1) ≪≫
            (λ_ (L'.fiberEquivalence Y.as.1).inverse.toCatHom).symm).hom
          _ _ fun x ↦ by
            simp only [Iso.trans_hom, Iso.symm_hom, Cat.Hom.toNatTrans_comp, NatTrans.comp_app,
              Cat.Hom.isoMk_hom, NatTrans.toCatHom₂_toNatTrans, Cat.leftUnitor_inv_toNatTrans,
              Functor.leftUnitor_inv_app, Category.comp_id]
            exact φ.normalizationInv_modification_naturality f x))
    (φ.normalizationInv_modification_comm)).symm

@[simp]
lemma normalizationInvIso_hom_joint_as_app (φ : L ⟶ L')
    (X : LocallyDiscrete (Γ × SingleObj H)) :
    (φ.normalizationInvIso.hom.joint.as.app X) =
      (λ_ (L'.fiberEquivalence X.as.1).inverse.toCatHom).hom ≫
        (Cat.Hom.isoMk (φ.inverseFiberIso X.as.1)).inv := by
  dsimp only [normalizationInvIso, Iso.symm_hom]
  erw [isoMk_inv_joint]
  rfl

@[simp]
lemma normalizationInvIso_inv_joint_as_app (φ : L ⟶ L')
    (X : LocallyDiscrete (Γ × SingleObj H)) :
    (φ.normalizationInvIso.inv.joint.as.app X) =
      (Cat.Hom.isoMk (φ.inverseFiberIso X.as.1)).hom ≫
        (λ_ (L'.fiberEquivalence X.as.1).inverse.toCatHom).inv := by
  dsimp only [normalizationInvIso, Iso.symm_inv]
  erw [isoMk_hom_joint]
  rfl

lemma normalizationInvIso_hom_app (φ : L ⟶ L') (p : Γ) (x : fiber actions p) :
    (φ.normalizationInvIso.hom.joint.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.app x =
      (φ.inverseFiberIso p).inv.app x := by
  simp
  rfl

lemma normalizationInvIso_inv_app (φ : L ⟶ L') (p : Γ) (x : fiber actions p) :
    (φ.normalizationInvIso.inv.joint.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.app x =
      (φ.inverseFiberIso p).hom.app x := by
  simp
  rfl

/-- Naturality of `normalizationEquivalence.hom` with respect to a morphism `φ : L ⟶ L'` of
lifts, obtained as the mate of `φ.normalizationInvIso.inv` across the adjoint equivalences
`L.normalizationEquivalence` and `L'.normalizationEquivalence`. -/
noncomputable def normalizationHomIso (φ : L ⟶ L') :
    φ ≫ L'.normalizationEquivalence.hom ≅
      L.normalizationEquivalence.hom ≫ φ.normalizedTransportHom.toLiftHom :=
  asIso ((Bicategory.mateEquiv L.normalizationEquivalence.adj
    L'.normalizationEquivalence.adj).symm φ.normalizationInvIso.inv)

lemma normalizationHomIso_hom (φ : L ⟶ L') :
    φ.normalizationHomIso.hom =
      (Bicategory.mateEquiv L.normalizationEquivalence.adj
        L'.normalizationEquivalence.adj).symm φ.normalizationInvIso.inv :=
  (rfl)

@[simp]
lemma mateEquiv_normalizationHomIso_hom (φ : L ⟶ L') :
    Bicategory.mateEquiv L.normalizationEquivalence.adj L'.normalizationEquivalence.adj
        φ.normalizationHomIso.hom =
      φ.normalizationInvIso.inv :=
  (Bicategory.mateEquiv L.normalizationEquivalence.adj
    L'.normalizationEquivalence.adj).apply_symm_apply _

/-- On each joint fiber, the forward component of `φ.normalizationHomIso` conjugates the fiber
comparison of `φ` by the fiber comparisons of the forward normalization equivalences. -/
lemma normalizationHomIso_hom_app (φ : L ⟶ L') (p : Γ) (Y : L.jointFiber p) :
    (φ.normalizationHomIso.hom.joint.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.app Y =
      (L'.normalizationEquivalence.hom.fiberFunctorIso p).hom.app ((φ.jointFunctor p).obj Y) ≫
        (φ.fiberFunctorIso p).hom.app Y ≫
          (L.normalizationEquivalence.hom.fiberFunctorIso p).inv.app Y := by
  -- The reconstructed target lift has identity prescribed-fiber comparison functors.
  have h : ((φ.comp L'.normalizationEquivalence.hom).fiberFunctorIso p).hom.app Y ≫
        ((L.normalizationEquivalence.hom.comp
          φ.normalizedTransportHom.toLiftHom).fiberFunctorIso p).inv.app Y =
      (L'.normalizationEquivalence.hom.fiberFunctorIso p).hom.app ((φ.jointFunctor p).obj Y) ≫
        (φ.fiberFunctorIso p).hom.app Y ≫
          (L.normalizationEquivalence.hom.fiberFunctorIso p).inv.app Y := by
    rw [comp_fiberFunctorIso_hom_app, comp_fiberFunctorIso_inv_app,
      fiberFunctorIso_inv_app φ.normalizedTransportHom.toLiftHom,
      NormalizedTransport.Hom.toLiftHom_fiberIso_inv_as_app, Cat.leftUnitor_inv_toNatTrans]
    erw [Functor.leftUnitor_inv_app, Category.comp_id]
    exact Category.assoc _ _ _
  exact (map_modification_app φ.normalizationHomIso.hom p Y).trans h

/-- On each joint fiber, the inverse component of `φ.normalizationHomIso` conjugates the inverse
fiber comparison of `φ` by the fiber comparisons of the forward normalization equivalences. -/
lemma normalizationHomIso_inv_app (φ : L ⟶ L') (p : Γ) (Y : L.jointFiber p) :
    (φ.normalizationHomIso.inv.joint.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.app Y =
      (L.normalizationEquivalence.hom.fiberFunctorIso p).hom.app Y ≫
        (φ.fiberFunctorIso p).inv.app Y ≫
          (L'.normalizationEquivalence.hom.fiberFunctorIso p).inv.app
            ((φ.jointFunctor p).obj Y) := by
  have h : ((L.normalizationEquivalence.hom.comp
          φ.normalizedTransportHom.toLiftHom).fiberFunctorIso p).hom.app Y ≫
        ((φ.comp L'.normalizationEquivalence.hom).fiberFunctorIso p).inv.app Y =
      (L.normalizationEquivalence.hom.fiberFunctorIso p).hom.app Y ≫
        (φ.fiberFunctorIso p).inv.app Y ≫
          (L'.normalizationEquivalence.hom.fiberFunctorIso p).inv.app
            ((φ.jointFunctor p).obj Y) := by
    rw [comp_fiberFunctorIso_hom_app, comp_fiberFunctorIso_inv_app,
      fiberFunctorIso_hom_app φ.normalizedTransportHom.toLiftHom,
      NormalizedTransport.Hom.toLiftHom_fiberIso_hom_as_app, Cat.leftUnitor_hom_toNatTrans]
    erw [Functor.leftUnitor_hom_app, Category.id_comp]
    rfl
  exact (map_modification_app φ.normalizationHomIso.inv p Y).trans h

end TauCeti.EquivariantGroupoidLift.Hom

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory CategoryTheory.Prod Pseudofunctor.StrongTrans NormalizedTransport

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  (actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w})

/-! ### The normalization unit and biequivalence -/

/-- The forward strong transformation of the normalization unit, from the identity pseudofunctor
of `EquivariantGroupoidLift Γ actions` to normalization followed by reconstruction. Its component
at `L` is `L.normalizationEquivalence.hom` and its naturality isomorphism at `φ` is
`φ.normalizationHomIso`. -/
-- Expose the body so that the unit and counit component equations of `normalizationUnitEquiv`
-- retain their literal endpoints.
@[expose] noncomputable def normalizationUnitHom :
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

@[simp]
lemma normalizationUnitHom_naturality {L L' : EquivariantGroupoidLift Γ actions} (φ : L ⟶ L') :
    (normalizationUnitHom actions).naturality φ = φ.normalizationHomIso :=
  (rfl)

/-- The inverse strong transformation of the normalization unit, from normalization followed by
reconstruction to the identity pseudofunctor of `EquivariantGroupoidLift Γ actions`. Its component
at `L` is `L.normalizationInv` and its naturality isomorphism at `φ` is `φ.normalizationInvIso`. -/
-- Expose the body so that the unit and counit component equations of `normalizationUnitEquiv`
-- retain their literal endpoints.
@[expose] noncomputable def normalizationUnitInv :
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

@[simp]
lemma normalizationUnitInv_naturality {L L' : EquivariantGroupoidLift Γ actions} (φ : L ⟶ L') :
    (normalizationUnitInv actions).naturality φ = φ.normalizationInvIso :=
  (rfl)

/-- The identity pseudofunctor of `EquivariantGroupoidLift Γ actions` is equivalent to
normalization followed by reconstruction, through `normalizationUnitHom` and
`normalizationUnitInv` and the objectwise unit and counit modifications of
`normalizationEquivalence`. -/
-- Expose the body so that the component equations of its unit and counit modifications can be
-- stated with their literal endpoints.
@[expose] noncomputable def normalizationUnitEquiv :
    Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ≌
      (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) where
  hom := normalizationUnitHom actions
  inv := normalizationUnitInv actions
  unit := Pseudofunctor.StrongTrans.isoMk (fun L ↦ L.normalizationEquivalence.unit)
    (fun _ ↦ Subsingleton.elim _ _)
  counit := Pseudofunctor.StrongTrans.isoMk (fun L ↦ L.normalizationEquivalence.counit)
    (fun _ ↦ Subsingleton.elim _ _)
  left_triangle := Iso.ext (homCategory.ext fun _ ↦ Subsingleton.elim _ _)

@[simp]
lemma normalizationUnitEquiv_hom :
    (normalizationUnitEquiv actions).hom = normalizationUnitHom actions :=
  (rfl)

@[simp]
lemma normalizationUnitEquiv_inv :
    (normalizationUnitEquiv actions).inv = normalizationUnitInv actions :=
  (rfl)

@[simp]
lemma normalizationUnitEquiv_unit_hom_as_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitEquiv actions).unit.hom.as.app L = L.normalizationEquivalence.unit.hom :=
  (rfl)

@[simp]
lemma normalizationUnitEquiv_unit_inv_as_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitEquiv actions).unit.inv.as.app L = L.normalizationEquivalence.unit.inv :=
  (rfl)

@[simp]
lemma normalizationUnitEquiv_counit_hom_as_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitEquiv actions).counit.hom.as.app L =
      L.normalizationEquivalence.counit.hom :=
  (rfl)

@[simp]
lemma normalizationUnitEquiv_counit_inv_as_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitEquiv actions).counit.inv.as.app L =
      L.normalizationEquivalence.counit.inv :=
  (rfl)

/-- The biequivalence between the bicategory of coherent equivariant groupoid lifts and the
locally discrete bicategory of normalized transports on the prescribed fibers. -/
-- Expose the body so that `normalizationBiequivalence_unitEquiv` and
-- `normalizationBiequivalence_counitEquiv` typecheck with their literal pseudofunctor endpoints.
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

/-! ### Triangle coherence and equivalence of hom-categories -/

section TriangleAndHomEquivalence

variable {actions}

private lemma normalizationInv_inverseFiberIso_hom_app (L : EquivariantGroupoidLift Γ actions)
    (p : Γ) (x : fiber actions p) :
    (L.normalizationInv.inverseFiberIso p).hom.app x =
      (L.fiberEquivalence p).inverse.map
        ((L.normalizedTransport.toLift.fiberEquivalence p).counit.app x) := by
  apply (L.fiberEquivalence p).functor.map_injective
  apply (cancel_mono ((L.fiberEquivalence p).counit.app x)).mp
  rw [L.normalizationInv.functor_map_inverseFiberIso_hom_app_comp_counit]
  rw [Hom.fiberFunctorIso_hom_app, L.normalizationInv_fiberIso_hom_as_app]
  erw [(L.fiberEquivalence p).counit_naturality]
  rfl

/-- Normalizing `L.normalizationInv` gives the return comparison
`(toLiftNormalizedTransportIso L.normalizedTransport).hom` on the nose. This is the triangle
coherence relating the unit and counit of `normalizationBiequivalence`. -/
@[simp]
lemma normalizationInv_normalizedTransportHom (L : EquivariantGroupoidLift Γ actions) :
    L.normalizationInv.normalizedTransportHom =
      (toLiftNormalizedTransportIso L.normalizedTransport).hom := by
  refine NormalizedTransport.Hom.ext fun p q g ↦ Iso.ext (NatTrans.ext (funext fun x ↦ ?_))
  let y : fiber actions p := (L.normalizedTransport.toLift.fiberEquivalence p).inverse.obj x
  let ε : y ⟶ x := (L.normalizedTransport.toLift.fiberEquivalence p).counit.app x
  rw [Hom.normalizedTransportHom_transportIso, toLiftNormalizedTransportIso_hom_transportIso,
    Hom.transportIso_hom_app, L.normalizedTransport.toLiftTransportIso_hom_app,
    L.normalizationInv_inverseFiberIso_hom_app]
  simp only [Hom.fiberFunctorIso_inv_app, L.normalizationInv_fiberIso_inv_as_app,
    Hom.jointMapIso_hom_app]
  erw [L.normalizationJointInv_naturality_hom_app]
  -- Display the remaining cells in the prescribed fibers, since `toLift.jointFiber` is
  -- `fiber actions` and `toLift.jointMap g` is `T_1 ⋙ L.transport g`.
  change (L.fiberEquivalence q).counitInv.app
        ((L.transport g).obj ((act actions p (𝟙 _)).obj y)) ≫
      (L.fiberEquivalence q).functor.map
        ((L.normalizationJointIso (g ×ₘ 𝟙 (SingleObj.star H))).hom.app y) ≫
      (L.fiberEquivalence q).functor.map
        ((L.jointMap g).map ((L.fiberEquivalence p).inverse.map ε)) =
    (L.transport g).map ((act actions p (𝟙 _)).map ε) ≫
      (L.transport g).map ((actId actions p).hom.app x)
  rw [L.normalizationJointIso_hom_app]
  dsimp only [transport, Functor.comp_obj, Functor.comp_map]
  simp only [Functor.map_comp, Category.assoc]
  -- Cancel the target counit inverse against the mapped unit inverse at `q`.
  rw [(L.fiberEquivalence q).counitInv_app_functor,
    ← (L.fiberEquivalence q).functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  -- Reduce the left-unit compositor along `(𝟙 p, 1) ≫ (g, 1)` to `jointMapId` and `actId`.
  have hid : (L.joint.mapComp' (𝟙 p ×ₘ 𝟙 (SingleObj.star H)).toLoc
      (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
      (by simp [← Quiver.Hom.comp_toLoc])).inv.toNatTrans.app
        ((L.fiberEquivalence p).inverse.obj y) =
      (L.jointMap g).map ((L.jointMapId p).hom.app _) := by
    simpa [← prod_id, Quiver.Hom.id_toLoc, jointMap, jointMapId_hom_app,
      Pseudofunctor.mapId'_eq_mapId] using
      L.joint.mapComp'_id_comp_inv_app (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
        ((L.fiberEquivalence p).inverse.obj y)
  rw [hid]
  have hnat := (actId actions p).hom.naturality ε
  dsimp only [Functor.id_map, Functor.id_obj] at hnat
  simp only [← Functor.map_comp, reassoc_of% (L.actInverseIso_actId p y), hnat]

/-- Normalizing `L.normalizationEquivalence.hom` gives the inverse return comparison
`(toLiftNormalizedTransportIso L.normalizedTransport).inv`. -/
lemma normalizationEquivalence_hom_normalizedTransportHom (L : EquivariantGroupoidLift Γ actions) :
    L.normalizationEquivalence.hom.normalizedTransportHom =
      (toLiftNormalizedTransportIso L.normalizedTransport).inv := by
  rw [← cancel_mono (toLiftNormalizedTransportIso L.normalizedTransport).hom, Iso.inv_hom_id,
    ← L.normalizationInv_normalizedTransportHom, ← Hom.comp_normalizedTransportHom,
    ← L.normalizationEquivalence_inv]
  exact (L.normalizationEquivalence.unit.symm.hom.normalizedTransportHom_eq).trans
    (Hom.id_normalizedTransportHom L)

/-- Reconstructing a normalized transport morphism
`ψ : L.normalizedTransport ⟶ L'.normalizedTransport` and conjugating by the normalization
equivalences produces a lift morphism `L ⟶ L'`. -/
noncomputable def liftOfNormalizedTransportHom {L L' : EquivariantGroupoidLift Γ actions}
    (ψ : L.normalizedTransport ⟶ L'.normalizedTransport) : L ⟶ L' :=
  L.normalizationEquivalence.hom ≫ ψ.toLiftHom ≫ L'.normalizationInv

/-- Normalizing `liftOfNormalizedTransportHom ψ` recovers `ψ` strictly. -/
@[simp]
lemma liftOfNormalizedTransportHom_normalizedTransportHom
    {L L' : EquivariantGroupoidLift Γ actions}
    (ψ : L.normalizedTransport ⟶ L'.normalizedTransport) :
    (liftOfNormalizedTransportHom ψ).normalizedTransportHom = ψ := by
  rw [liftOfNormalizedTransportHom, Hom.comp_normalizedTransportHom,
    Hom.comp_normalizedTransportHom, L.normalizationEquivalence_hom_normalizedTransportHom,
    L'.normalizationInv_normalizedTransportHom, toLiftNormalizedTransportIso_hom_naturality,
    Iso.inv_hom_id_assoc]

/-- Reconstructing the normalization of a lift morphism `φ : L ⟶ L'` recovers `φ` up to a
canonical isomorphism of lift morphisms. -/
noncomputable def liftOfNormalizedTransportHomIso {L L' : EquivariantGroupoidLift Γ actions}
    (φ : L ⟶ L') : liftOfNormalizedTransportHom φ.normalizedTransportHom ≅ φ :=
  whiskerLeftIso L.normalizationEquivalence.hom φ.normalizationInvIso ≪≫
    (α_ L.normalizationEquivalence.hom L.normalizationInv φ).symm ≪≫
    whiskerRightIso L.normalizationEquivalence.unit.symm φ ≪≫
    λ_ φ

/-- Two parallel morphisms of equivariant lifts admit a compatible modification if and only if
they induce the same morphism of normalized transports. -/
lemma Hom.nonempty_hom_iff {L L' : EquivariantGroupoidLift Γ actions} (φ ψ : L ⟶ L') :
    Nonempty (φ ⟶ ψ) ↔ φ.normalizedTransportHom = ψ.normalizedTransportHom := by
  refine ⟨fun ⟨Θ⟩ ↦ Θ.normalizedTransportHom_eq, fun h ↦ ?_⟩
  exact ⟨(liftOfNormalizedTransportHomIso φ).symm.hom ≫
    eqToHom (congrArg liftOfNormalizedTransportHom h) ≫
    (liftOfNormalizedTransportHomIso ψ).hom⟩

private lemma normalizationPseudofunctor_mapFunctor_obj_as
    {L L' : EquivariantGroupoidLift Γ actions} (φ : L ⟶ L') :
    (((normalizationPseudofunctor actions).mapFunctor L L').obj φ).as = φ.normalizedTransportHom :=
  (congrArg Discrete.as ((normalizationPseudofunctor actions).mapFunctor_obj L L' φ)).trans
    (normalizationPseudofunctor_map_as actions φ)

private lemma normalizationPseudofunctor_mapFunctor_obj_liftOfNormalizedTransportHom
    {L L' : EquivariantGroupoidLift Γ actions}
    (ψ : (normalizationPseudofunctor actions).obj L ⟶
      (normalizationPseudofunctor actions).obj L') :
    ((normalizationPseudofunctor actions).mapFunctor L L').obj
        (liftOfNormalizedTransportHom (L := L) (L' := L') ψ.as) = ψ :=
  ((normalizationPseudofunctor actions).mapFunctor_obj L L' _).trans
    (Discrete.ext ((normalizationPseudofunctor_map_as actions _).trans
      (liftOfNormalizedTransportHom_normalizedTransportHom ψ.as)))

private noncomputable def normalizationHomInverse
    (L L' : EquivariantGroupoidLift Γ actions) :
    ((normalizationPseudofunctor actions).obj L ⟶
      (normalizationPseudofunctor actions).obj L') ⥤ (L ⟶ L') :=
  (reconstructionPseudofunctor actions).mapFunctor
      ((normalizationPseudofunctor actions).obj L)
      ((normalizationPseudofunctor actions).obj L') ⋙
    postcomp L.normalizedTransport.toLift L'.normalizationInv ⋙
    precomp L' L.normalizationEquivalence.hom

private lemma normalizationHomInverse_obj {L L' : EquivariantGroupoidLift Γ actions}
    (ψ : (normalizationPseudofunctor actions).obj L ⟶
      (normalizationPseudofunctor actions).obj L') :
    (normalizationHomInverse L L').obj ψ =
      liftOfNormalizedTransportHom (L := L) (L' := L') ψ.as :=
  (precomp_obj _ _ _).trans
    ((congrArg (L.normalizationEquivalence.hom ≫ ·) (postcomp_obj _ _ _)).trans
      (congrArg (fun g : L.normalizedTransport.toLift ⟶ L'.normalizedTransport.toLift ↦
          L.normalizationEquivalence.hom ≫ g ≫ L'.normalizationInv)
        ((reconstructionPseudofunctor actions).mapFunctor_obj
          ((normalizationPseudofunctor actions).obj L)
          ((normalizationPseudofunctor actions).obj L') ψ)))

/-- Normalization induces an equivalence of hom-categories between morphisms of lifts `L ⟶ L'`
and morphisms of normalized transports in `LocallyDiscrete (NormalizedTransport Γ actions)`.
Because `normalizationInv_normalizedTransportHom` gives a strict triangle identity on normalized
transports, the inverse functor is given directly by reconstruction conjugated by
`L.normalizationEquivalence.hom` and `L'.normalizationInv`. -/
noncomputable def normalizationHomEquivalence
    (L L' : EquivariantGroupoidLift Γ actions) :
    (L ⟶ L') ≌ ((normalizationPseudofunctor actions).obj L ⟶
      (normalizationPseudofunctor actions).obj L') where
  functor := (normalizationPseudofunctor actions).mapFunctor L L'
  inverse := normalizationHomInverse L L'
  unitIso := NatIso.ofComponents
    (fun φ ↦ (liftOfNormalizedTransportHomIso φ).symm ≪≫
      eqToIso ((normalizationHomInverse_obj _).trans
        (congrArg (liftOfNormalizedTransportHom (L := L) (L' := L'))
          (normalizationPseudofunctor_mapFunctor_obj_as φ))).symm)
    (fun _ ↦ Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents
    (fun ψ ↦ eqToIso
      ((congrArg ((normalizationPseudofunctor actions).mapFunctor L L').obj
          (normalizationHomInverse_obj ψ)).trans
        (normalizationPseudofunctor_mapFunctor_obj_liftOfNormalizedTransportHom ψ)))
    (fun _ ↦ Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

@[simp]
lemma normalizationHomEquivalence_functor (L L' : EquivariantGroupoidLift Γ actions) :
    (L.normalizationHomEquivalence L').functor =
      (normalizationPseudofunctor actions).mapFunctor L L' :=
  (rfl)

@[simp]
lemma normalizationHomEquivalence_inverse_obj (L L' : EquivariantGroupoidLift Γ actions)
    (ψ : (normalizationPseudofunctor actions).obj L ⟶
      (normalizationPseudofunctor actions).obj L') :
    (L.normalizationHomEquivalence L').inverse.obj ψ =
      liftOfNormalizedTransportHom (L := L) (L' := L') ψ.as :=
  normalizationHomInverse_obj ψ

end TriangleAndHomEquivalence

end TauCeti.EquivariantGroupoidLift
