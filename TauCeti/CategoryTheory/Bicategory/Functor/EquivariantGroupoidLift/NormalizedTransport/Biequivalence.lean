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
# The normalization biequivalence for equivariant groupoid lifts

Normalizing a lift on the prescribed fibers sends `EquivariantGroupoidLift Γ actions` to the
locally discrete bicategory `LocallyDiscrete (NormalizedTransport Γ actions)`, and reconstruction
returns a lift with identity fiber comparisons. Here we show that the objectwise equivalences
`L.normalizationEquivalence : L ≌ L.normalizedTransport.toLift` are pseudonatural in morphisms of
lifts, assembling into the normalization unit equivalence

`normalizationUnitEquiv actions :
  Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ≌
    (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions)`

and combining with `normalizationCounitEquiv` to give

`normalizationBiequivalence actions :
  TauCeti.Biequivalence (EquivariantGroupoidLift Γ actions)
    (LocallyDiscrete (NormalizedTransport Γ actions))`.

Every `1`-morphism of `EquivariantGroupoidLift Γ actions` is already an equivalence and every
`2`-morphism is already invertible and unique, so no passage to a sub-bicategory of equivalences
and invertible modifications is needed. Naturality of the backward unit components
`L.normalizationInv` is given on joint fibers by the inverse-fiber comparisons `φ.inverseFiberIso`;
passing to mates along the adjoint equivalences `L.normalizationInv.equivalence` and inverting in
the hom groupoid gives naturality of the forward unit components `L.normalizationEquivalence.hom`.

Normalizing `L.normalizationInv` recovers the return comparison `toLiftNormalizedTransportIso` at
`L.normalizedTransport`. Together with naturality of the counit, this identifies morphisms of
lifts up to unique invertible modification with morphisms of their normalized transports, and shows
that normalization and reconstruction induce equivalences on all hom categories.

## Main declarations

* `TauCeti.EquivariantGroupoidLift.Hom.inverseFiberIso_normalizationJointIso`: the inverse-fiber
  comparisons intertwine the reconstructed normalized-transport comparison and
  `L'.normalizationJointIso` with `L.normalizationJointIso` and the joint naturality cell;
* `TauCeti.EquivariantGroupoidLift.Hom.normalizationInvIso`,
  `TauCeti.EquivariantGroupoidLift.Hom.normalizationHomIso`: the naturality isomorphisms of the
  backward and forward normalization unit morphisms;
* `TauCeti.EquivariantGroupoidLift.normalizationUnitHom`,
  `TauCeti.EquivariantGroupoidLift.normalizationUnitInv`,
  `TauCeti.EquivariantGroupoidLift.normalizationUnitEquiv`: the unit strong transformations and
  pseudonatural equivalence;
* `TauCeti.EquivariantGroupoidLift.normalizationBiequivalence`: the biequivalence between coherent
  equivariant lifts and normalized transport on the prescribed fibers;
* `TauCeti.EquivariantGroupoidLift.normalizationInv_normalizedTransportHom`,
  `TauCeti.EquivariantGroupoidLift.Hom.ofNormalizedTransportHom`,
  `TauCeti.EquivariantGroupoidLift.Hom.nonempty_hom₂_iff`,
  `TauCeti.EquivariantGroupoidLift.isEquivalence_normalizationPseudofunctor_mapFunctor`:
  compatibility of unit and counit under normalization and the induced equivalences on hom
  categories.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055), Chapters 4 and 6: strong transformations,
  modifications, mates, and biequivalences.
* Edward Frenkel,
  [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  Cambridge Studies in Advanced Mathematics 103 (2007), §1.3: equivariant families of local
  representation categories.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory CategoryTheory.Prod Pseudofunctor.StrongTrans NormalizedTransport

/-! ### Naturality of the objectwise normalization equivalences -/

namespace Hom

section Naturality

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  {L L' : EquivariantGroupoidLift Γ actions} (φ : L ⟶ L')

private lemma inverseFiberIso_transportIso_unitInv {p q : Γ} (g : p ⟶ q)
    (y : fiber actions p) :
    (φ.inverseFiberIso q).hom.app ((L.transport g).obj y) ≫
        (L'.fiberEquivalence q).inverse.map ((φ.transportIso g).hom.app y) ≫
        (L'.fiberEquivalence q).unitInv.app
          ((L'.jointMap g).obj ((L'.fiberEquivalence p).inverse.obj y)) =
      (φ.jointFunctor q).map ((L.fiberEquivalence q).unitInv.app
          ((L.jointMap g).obj ((L.fiberEquivalence p).inverse.obj y))) ≫
        (φ.jointMapIso g).hom.app ((L.fiberEquivalence p).inverse.obj y) ≫
        (L'.jointMap g).map ((φ.inverseFiberIso p).hom.app y) := by
  rw [transportIso_hom_app]
  dsimp only [EquivariantGroupoidLift.transport, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  -- Naturality of `unitInv` crosses the unfolded `(fiberEquivalence q).functor ⋙ inverse`.
  erw [(L'.fiberEquivalence q).unitInv_naturality,
    (L'.fiberEquivalence q).unitInv_naturality_assoc]
  rw [φ.inverseFiberIso_hom_app_comp_unitInv_assoc q
    ((L.jointMap g).obj ((L.fiberEquivalence p).inverse.obj y))]

/-- Along any joint arrow, the inverse-fiber comparisons intertwine the reconstructed
normalized-transport comparison and `L'.normalizationJointIso` with `L.normalizationJointIso`
and the joint naturality cell of `φ`. -/
@[reassoc]
lemma inverseFiberIso_normalizationJointIso {X Y : Γ × SingleObj H} (f : X ⟶ Y)
    (x : fiber actions X.1) :
    (φ.inverseFiberIso Y.1).hom.app ((L.normalizedTransport.jointFunctor f).obj x) ≫
        (L'.fiberEquivalence Y.1).inverse.map
          ((φ.normalizedTransportHom.jointIso f).hom.app x) ≫
        (L'.normalizationJointIso f).hom.app x =
      (φ.jointFunctor Y.1).map ((L.normalizationJointIso f).hom.app x) ≫
        (φ.joint.naturality f.toLoc).hom.toNatTrans.app
          ((L.fiberEquivalence X.1).inverse.obj x) ≫
        (L'.joint.map f.toLoc).toFunctor.map ((φ.inverseFiberIso X.1).hom.app x) := by
  obtain ⟨p, ⟨⟩⟩ := X
  obtain ⟨q, ⟨⟩⟩ := Y
  have hf : (𝟙 p ×ₘ f.2).toLoc ≫ (f.1 ×ₘ 𝟙 (SingleObj.star H)).toLoc = f.toLoc := by
    rw [← Quiver.Hom.comp_toLoc]
    exact congrArg Quiver.Hom.toLoc (Prod.ext (Category.id_comp f.1) (Category.comp_id f.2))
  -- Factor `(φ.joint.naturality f.toLoc).hom` along `(𝟙 p ×ₘ f.2)` followed by `(f.1 ×ₘ 𝟙 _)`.
  have hcomp' :
      (φ.jointFunctor q).map
          ((L.joint.mapComp' (𝟙 p ×ₘ f.2).toLoc (f.1 ×ₘ 𝟙 (SingleObj.star H)).toLoc f.toLoc
            hf).inv.toNatTrans.app ((L.fiberEquivalence p).inverse.obj x)) ≫
        (φ.joint.naturality f.toLoc).hom.toNatTrans.app
          ((L.fiberEquivalence p).inverse.obj x) =
      (φ.jointMapIso f.1).hom.app
          ((L.jointAct p f.2).obj ((L.fiberEquivalence p).inverse.obj x)) ≫
        (L'.jointMap f.1).map
          ((φ.jointActIso p f.2).hom.app ((L.fiberEquivalence p).inverse.obj x)) ≫
        (L'.joint.mapComp' (𝟙 p ×ₘ f.2).toLoc (f.1 ×ₘ 𝟙 (SingleObj.star H)).toLoc f.toLoc
          hf).inv.toNatTrans.app
          ((φ.jointFunctor p).obj ((L.fiberEquivalence p).inverse.obj x)) := by
    have hcomp := φ.joint.naturality_comp'_hom_app
      (𝟙 p ×ₘ f.2).toLoc (f.1 ×ₘ 𝟙 (SingleObj.star H)).toLoc f.toLoc hf
      ((L.fiberEquivalence p).inverse.obj x)
    rw [jointMapIso_hom_app, jointActIso_hom_app, hcomp]
    dsimp only [jointFunctor, jointMap, jointAct]
    rw [← CategoryTheory.Functor.map_comp_assoc, Cat.Hom.inv_hom_id_toNatTrans_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  rw [NormalizedTransport.Hom.jointIso_hom_app, normalizedTransportHom_transportIso,
    L.normalizationJointIso_hom_app, L'.normalizationJointIso_hom_app]
  dsimp only [NormalizedTransport.jointFunctor, normalizedTransport,
    EquivariantGroupoidLift.transport, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  -- Match the unfolded `L.transport` and `jointFiber` carriers across naturality rewrites.
  erw [← Category.assoc ((L'.fiberEquivalence q).inverse.map _),
    ← Category.assoc ((φ.inverseFiberIso q).hom.app _),
    φ.inverseFiberIso_transportIso_unitInv (f.1 : p ⟶ q) ((act actions p f.2).obj x)]
  simp only [Category.assoc]
  rw [reassoc_of% hcomp', ← Functor.map_comp_assoc (L'.jointMap f.1),
    ← φ.inverseFiberIso_actInverseIso p f.2 x]
  simp only [Functor.map_comp, Category.assoc]
  erw [← (φ.jointMapIso f.1).hom.naturality_assoc ((L.actInverseIso p f.2).hom.app x),
    (L'.joint.mapComp' (𝟙 p ×ₘ f.2).toLoc (f.1 ×ₘ 𝟙 _).toLoc f.toLoc hf).inv.toNatTrans.naturality
      ((φ.inverseFiberIso p).hom.app x)]
  rfl

private lemma inverseFiberIso_trans_leftUnitor_symm_hom_app
    (X : LocallyDiscrete (Γ × SingleObj H)) (x : fiber actions X.as.1) :
    (Cat.Hom.isoMk (φ.inverseFiberIso X.as.1) ≪≫
      (λ_ (L'.fiberEquivalence X.as.1).inverse.toCatHom).symm).hom.toNatTrans.app x =
    (φ.inverseFiberIso X.as.1).hom.app x := by
  simp

/-- The underlying joint modification comparing `L.normalizationInv ≫ φ` with
`φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv`. Its component at `(p, ⋆)` is
`φ.inverseFiberIso p` followed by the inverse left unitor in `Cat`. -/
private noncomputable def normalizationInvSymmJointIso :
    (L.normalizationInv ≫ φ).joint ≅
      (φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv).joint :=
  Pseudofunctor.StrongTrans.isoMk
    (fun X ↦ Cat.Hom.isoMk (φ.inverseFiberIso X.as.1) ≪≫
      (λ_ (L'.fiberEquivalence X.as.1).inverse.toCatHom).symm)
    (fun {X Y} f ↦ by
      refine Cat.whiskerLeft_comp_eq_comp_whiskerRight _ _ _ _ fun x ↦ ?_
      -- Expand the composite naturality cells across the reconstructed joint carrier.
      erw [inverseFiberIso_trans_leftUnitor_symm_hom_app φ Y,
        inverseFiberIso_trans_leftUnitor_symm_hom_app φ X,
        Pseudofunctor.StrongTrans.comp_naturality_hom_app,
        Pseudofunctor.StrongTrans.comp_naturality_hom_app,
        NormalizedTransport.Hom.jointHom_naturality_hom_app,
        L'.normalizationJointInv_naturality_hom_app,
        L.normalizationJointInv_naturality_hom_app]
      let x₀ : fiber actions X.as.1 := x
      have h := φ.inverseFiberIso_normalizationJointIso f.as x₀
      rw [NormalizedTransport.Hom.jointIso_hom_app] at h
      exact h.trans (Category.assoc _ _ _).symm)

private lemma normalizationInvSymmJointIso_hom_as_app (X : LocallyDiscrete (Γ × SingleObj H)) :
    (normalizationInvSymmJointIso φ).hom.as.app X =
      (Cat.Hom.isoMk (φ.inverseFiberIso X.as.1)).hom ≫
        (λ_ (L'.fiberEquivalence X.as.1).inverse.toCatHom).inv :=
  (rfl)

private lemma whiskerRight_trans_leftUnitor_inv_comp_eq {C D D' A : Cat.{v, w}}
    {I : C ⟶ D} {I' : C ⟶ D'} {Φ : D ⟶ D'} {E₀ : C ⟶ A} {E : D ⟶ A} {E' : D' ⟶ A}
    (i : I ≫ Φ ⟶ I') (ε₀ : 𝟙 C ≫ E₀ ⟶ E₀) (ε : I ≫ E ⟶ E₀) (ε' : I' ≫ E' ⟶ E₀)
    (f : Φ ≫ E' ⟶ E)
    (h : ∀ x : C, E'.toFunctor.map (i.toNatTrans.app x) ≫
        ε'.toNatTrans.app x ≫ ε₀.toNatTrans.app x =
      f.toNatTrans.app (I.toFunctor.obj x) ≫ ε.toNatTrans.app x) :
    (i ≫ (λ_ I').inv) ▷ E' ≫ (α_ (𝟙 C) I' E').hom ≫ 𝟙 C ◁ ε' ≫ ε₀ =
      (α_ I Φ E').hom ≫ I ◁ f ≫ ε := by
  ext x
  simpa using h x

/-- Reconstructing the normalized comparison of a lift morphism `φ : L ⟶ L'` and composing with
`L'.normalizationInv` is isomorphic to `L.normalizationInv` followed by `φ`. On each joint fiber,
the inverse modification acts by `φ.inverseFiberIso`. -/
noncomputable def normalizationInvIso :
    φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv ≅ L.normalizationInv ≫ φ :=
  (isoMk (normalizationInvSymmJointIso φ) fun p a ↦ by
    obtain ⟨⟨⟩⟩ := a
    rw [normalizationInvSymmJointIso_hom_as_app,
      EquivariantGroupoidLift.comp_fiberIso, comp_fiberIso_hom_as_app,
      EquivariantGroupoidLift.comp_fiberIso, comp_fiberIso_hom_as_app]
    refine whiskerRight_trans_leftUnitor_inv_comp_eq _ _ _ _ _ fun (x : fiber actions p) ↦ ?_
    rw [L'.normalizationInv_fiberIso_hom_as_app, L.normalizationInv_fiberIso_hom_as_app,
      NormalizedTransport.Hom.toLiftHom_fiberIso_hom_as_app]
    have h := φ.functor_map_inverseFiberIso_hom_app_comp_counit p x
    rw [fiberFunctorIso_hom_app] at h
    exact (congrArg (_ ≫ ·) (Category.comp_id ((L'.fiberEquivalence p).counit.app x))).trans h).symm

lemma normalizationInvIso_hom_joint_as_app (X : LocallyDiscrete (Γ × SingleObj H)) :
    (normalizationInvIso φ).hom.joint.as.app X =
      (λ_ (L'.fiberEquivalence X.as.1).inverse.toCatHom).hom ≫
        (Cat.Hom.isoMk (φ.inverseFiberIso X.as.1)).inv := by
  rw [normalizationInvIso, Iso.symm_hom, isoMk_inv_joint]
  rfl

lemma normalizationInvIso_inv_joint_as_app (X : LocallyDiscrete (Γ × SingleObj H)) :
    (normalizationInvIso φ).inv.joint.as.app X =
      (Cat.Hom.isoMk (φ.inverseFiberIso X.as.1)).hom ≫
        (λ_ (L'.fiberEquivalence X.as.1).inverse.toCatHom).inv := by
  rw [normalizationInvIso, Iso.symm_inv, isoMk_hom_joint]
  rfl

lemma normalizationInvIso_hom_app (p : Γ) (x : fiber actions p) :
    ((normalizationInvIso φ).hom.joint.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.app x =
      (φ.inverseFiberIso p).inv.app x := by
  rw [normalizationInvIso_hom_joint_as_app]
  simp
  rfl

lemma normalizationInvIso_inv_app (p : Γ) (x : fiber actions p) :
    ((normalizationInvIso φ).inv.joint.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.app x =
      (φ.inverseFiberIso p).hom.app x := by
  rw [normalizationInvIso_inv_joint_as_app]
  simp
  rfl

/-- The forward normalization morphisms are natural in `φ : L ⟶ L'`: `φ` followed by
`L'.normalizationEquivalence.hom` is isomorphic to `L.normalizationEquivalence.hom` followed by
the reconstructed normalized comparison of `φ`. The inverse `2`-morphism is the mate of
`(normalizationInvIso φ).hom` across the normalization equivalences. -/
noncomputable def normalizationHomIso :
    φ ≫ L'.normalizationEquivalence.hom ≅
      L.normalizationEquivalence.hom ≫ φ.normalizedTransportHom.toLiftHom :=
  (asIso (mateEquiv L.normalizationInv.equivalence.adj
    L'.normalizationInv.equivalence.adj (normalizationInvIso φ).hom)).symm

lemma normalizationHomIso_inv_eq_mateEquiv :
    (normalizationHomIso φ).inv =
      mateEquiv L.normalizationInv.equivalence.adj
        L'.normalizationInv.equivalence.adj (normalizationInvIso φ).hom :=
  (rfl)

end Naturality

end Hom

/-! ### The normalization unit equivalence and biequivalence -/

section Biequivalence

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  (actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w})

/-- The forward unit strong transformation from the identity of `EquivariantGroupoidLift Γ actions`
to normalization followed by reconstruction, with components `L.normalizationEquivalence.hom`.
Coherence of its naturality cells holds automatically because compatible modifications of lift
morphisms are unique. -/
-- Expose the record so the unit and counit component equations of `normalizationUnitEquiv`
-- retain their literal 1-morphism endpoints.
@[expose] noncomputable def normalizationUnitHom :
    Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ⟶
      (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) where
  app L := L.normalizationEquivalence.hom
  naturality φ := Hom.normalizationHomIso φ
  naturality_naturality _ := Subsingleton.elim _ _
  naturality_id _ := Subsingleton.elim _ _
  naturality_comp _ _ := Subsingleton.elim _ _

@[simp]
lemma normalizationUnitHom_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitHom actions).app L = L.normalizationEquivalence.hom :=
  (rfl)

lemma normalizationUnitHom_naturality {L L' : EquivariantGroupoidLift Γ actions} (φ : L ⟶ L') :
    (normalizationUnitHom actions).naturality φ = Hom.normalizationHomIso φ :=
  (rfl)

/-- The backward unit strong transformation from normalization followed by reconstruction to the
identity of `EquivariantGroupoidLift Γ actions`, with components `L.normalizationInv`. -/
-- Expose the record so the unit and counit component equations of `normalizationUnitEquiv`
-- retain their literal 1-morphism endpoints.
@[expose] noncomputable def normalizationUnitInv :
    (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) ⟶
      Pseudofunctor.id (EquivariantGroupoidLift Γ actions) where
  app L := L.normalizationInv
  naturality φ := Hom.normalizationInvIso φ
  naturality_naturality _ := Subsingleton.elim _ _
  naturality_id _ := Subsingleton.elim _ _
  naturality_comp _ _ := Subsingleton.elim _ _

@[simp]
lemma normalizationUnitInv_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitInv actions).app L = L.normalizationInv :=
  (rfl)

lemma normalizationUnitInv_naturality {L L' : EquivariantGroupoidLift Γ actions} (φ : L ⟶ L') :
    (normalizationUnitInv actions).naturality φ = Hom.normalizationInvIso φ :=
  (rfl)

/-- The identity pseudofunctor on `EquivariantGroupoidLift Γ actions` is equivalent to
normalization followed by reconstruction, with objectwise components
`L.normalizationEquivalence`. -/
-- Expose the equivalence so the types of its unit and counit component equations reduce to the
-- objectwise unit and counit of `L.normalizationEquivalence`.
@[expose] noncomputable def normalizationUnitEquiv :
    Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ≌
      (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) :=
  Equivalence.mkOfAdjointifyCounit (f := normalizationUnitHom actions)
    (g := normalizationUnitInv actions)
    (Pseudofunctor.StrongTrans.isoMk (fun L ↦ L.normalizationEquivalence.unit)
      (fun _ ↦ Subsingleton.elim _ _))
    (Pseudofunctor.StrongTrans.isoMk (fun L ↦ L.normalizationEquivalence.counit)
      (fun _ ↦ Subsingleton.elim _ _))

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

/-- Adjointification does not alter the counit of `normalizationUnitEquiv`, since modifications
into `EquivariantGroupoidLift Γ actions` have unique `2`-morphism components. -/
lemma normalizationUnitEquiv_counit :
    (normalizationUnitEquiv actions).counit =
      Pseudofunctor.StrongTrans.isoMk (fun L ↦ L.normalizationEquivalence.counit)
        (fun _ ↦ Subsingleton.elim _ _) :=
  adjointifyCounit_eq_of_left_triangle <|
    Iso.ext <| homCategory.ext fun _ ↦ Subsingleton.elim _ _

@[simp]
lemma normalizationUnitEquiv_counit_hom_as_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitEquiv actions).counit.hom.as.app L = L.normalizationEquivalence.counit.hom :=
  congrArg (fun e ↦ e.hom.as.app L) (normalizationUnitEquiv_counit actions)

@[simp]
lemma normalizationUnitEquiv_counit_inv_as_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitEquiv actions).counit.inv.as.app L = L.normalizationEquivalence.counit.inv :=
  congrArg (fun e ↦ e.inv.as.app L) (normalizationUnitEquiv_counit actions)

/-- The biequivalence between the bicategory of coherent equivariant groupoid lifts and the
locally discrete bicategory of normalized transports on the prescribed fibers. -/
-- Expose the body so the types of the unit and counit projections reduce to the two
-- pseudofunctors in `normalizationBiequivalence_unitEquiv` and `counitEquiv`.
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

/-! ### Compatibility with the counit and equivalences on hom categories -/

section Classification

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}

/-- The inverse-fiber comparison of `L.normalizationInv` acts by applying the original inverse
fiber equivalence to the counit of the reconstructed fiber equivalence. -/
lemma normalizationInv_inverseFiberIso_hom_app (L : EquivariantGroupoidLift Γ actions)
    (p : Γ) (x : fiber actions p) :
    (L.normalizationInv.inverseFiberIso p).hom.app x =
      (L.fiberEquivalence p).inverse.map
        ((L.normalizedTransport.toLift.fiberEquivalence p).counit.app x) := by
  apply (L.fiberEquivalence p).functor.map_injective
  apply (cancel_mono ((L.fiberEquivalence p).counit.app x)).mp
  rw [Hom.functor_map_inverseFiberIso_hom_app_comp_counit, Hom.fiberFunctorIso_hom_app,
    L.normalizationInv_fiberIso_hom_as_app]
  -- Unfold `Cat.Hom.isoMk counitIso` to `counit` across the naturality square.
  erw [(L.fiberEquivalence p).counit_naturality]
  rfl

private lemma normalizationInv_fiberFunctorIso_inv_comp_unitInv
    (L : EquivariantGroupoidLift Γ actions) (q : Γ) (z : L.jointFiber q) :
    (L.normalizationInv.fiberFunctorIso q).inv.app ((L.fiberEquivalence q).functor.obj z) ≫
      (L.fiberEquivalence q).functor.map ((L.fiberEquivalence q).unitInv.app z) = 𝟙 _ := by
  let w : L.normalizedTransport.toLift.jointFiber q := (L.fiberEquivalence q).functor.obj z
  refine (Iso.inv_comp_eq (α := (L.normalizationInv.fiberFunctorIso q).app w)
    (g := 𝟙 ((L.normalizedTransport.toLift.fiberEquivalence q).functor.obj w))).mpr ?_
  rw [Category.comp_id, Iso.app_hom, Hom.fiberFunctorIso_hom_app,
    L.normalizationInv_fiberIso_hom_as_app]
  have hcounit :
      (L.fiberEquivalence q).functor.map ((L.fiberEquivalence q).unitInv.app z) =
        (L.fiberEquivalence q).counit.app ((L.fiberEquivalence q).functor.obj z) := by
    apply (cancel_epi ((L.fiberEquivalence q).functor.map ((L.fiberEquivalence q).unit.app z))).mp
    rw [← CategoryTheory.Functor.map_comp]
    simp
  exact hcounit

/-- Normalizing `L.normalizationInv` along a parameter arrow gives the return comparison
`toLiftTransportIso` of `L.normalizedTransport`. -/
lemma normalizationInv_transportIso_hom_app (L : EquivariantGroupoidLift Γ actions)
    {p q : Γ} (g : p ⟶ q) (x : fiber actions p) :
    (L.normalizationInv.transportIso g).hom.app x =
      (L.normalizedTransport.toLiftTransportIso g).hom.app x := by
  let N := L.normalizedTransport
  let y : fiber actions p := (N.toLift.fiberEquivalence p).inverse.obj x
  let ε : y ⟶ x := (N.toLift.fiberEquivalence p).counit.app x
  -- Expand the joint comparison at `(g, 1)` and simplify its left identity factor.
  have hjoint₀ :
      (L.normalizationJointIso (g ×ₘ 𝟙 (SingleObj.star H))).hom.app y =
        (L.fiberEquivalence q).unitInv.app
            ((L.jointMap g).obj ((L.fiberEquivalence p).inverse.obj
              ((act actions p (𝟙 (SingleObj.star H))).obj y))) ≫
          (L.jointMap g).map ((L.actInverseIso p (𝟙 (SingleObj.star H))).hom.app y) ≫
          (L.jointMap g).map ((L.jointMapId p).hom.app ((L.fiberEquivalence p).inverse.obj y)) := by
    rw [L.normalizationJointIso_hom_app]
    dsimp only [jointMap]
    simp only [← prod_id, Quiver.Hom.id_toLoc]
    rw [Pseudofunctor.mapComp'_id_comp_inv_app]
    simp only [jointMapId_hom_app, ← prod_id, Quiver.Hom.id_toLoc,
      Pseudofunctor.mapId'_eq_mapId]
    rfl
  have hjoint :=
    (congrArg (L.fiberEquivalence q).functor.map hjoint₀).trans (Functor.map_comp _ _ _)
  -- Simplify the remaining composite in `fiber actions q` before comparing with
  -- `toLiftTransportIso`.
  have hrem :
      (L.fiberEquivalence q).functor.map
          ((L.jointMap g).map ((L.actInverseIso p (𝟙 (SingleObj.star H))).hom.app y) ≫
            (L.jointMap g).map ((L.jointMapId p).hom.app ((L.fiberEquivalence p).inverse.obj y))) ≫
        (L.fiberEquivalence q).functor.map
          ((L.jointMap g).map ((L.fiberEquivalence p).inverse.map ε)) =
      (L.transport g).map ((act actions p (𝟙 (SingleObj.star H))).map ε) ≫
        (L.transport g).map ((actId actions p).hom.app x) := by
    rw [← Functor.map_comp, ← Functor.map_comp, L.actInverseIso_actId p y,
      ← Functor.map_comp, ← Functor.map_comp, ← L.transport_map]
    exact (congrArg (L.transport g).map ((actId actions p).hom.naturality ε).symm).trans
      ((L.transport g).map_comp _ _)
  rw [Hom.transportIso_hom_app, L.normalizationInv_inverseFiberIso_hom_app, Hom.jointMapIso_hom_app]
  -- Unfold `L.normalizationInv.joint` and cancel the target counit/unit pair.
  erw [L.normalizationJointInv_naturality_hom_app, hjoint, ← Category.assoc, ← Category.assoc,
    L.normalizationInv_fiberFunctorIso_inv_comp_unitInv q
      ((L.jointMap g).obj ((L.fiberEquivalence p).inverse.obj ((act actions p (𝟙 _)).obj y))),
    Category.id_comp]
  exact hrem.trans (N.toLiftTransportIso_hom_app g x).symm

/-- Normalizing the backward unit morphism `L.normalizationInv` yields the forward return
comparison `(toLiftNormalizedTransportIso L.normalizedTransport).hom`. -/
@[simp]
lemma normalizationInv_normalizedTransportHom (L : EquivariantGroupoidLift Γ actions) :
    L.normalizationInv.normalizedTransportHom =
      (toLiftNormalizedTransportIso L.normalizedTransport).hom := by
  refine NormalizedTransport.Hom.ext fun p q g ↦ Iso.ext (NatTrans.ext (funext fun x ↦ ?_))
  rw [Hom.normalizedTransportHom_transportIso, toLiftNormalizedTransportIso_hom_transportIso]
  exact L.normalizationInv_transportIso_hom_app g x

/-- Normalizing the chosen inverse of `L.normalizationInv` yields the inverse return comparison
`(toLiftNormalizedTransportIso L.normalizedTransport).inv`. -/
@[simp]
lemma normalizationInv_equivalence_inv_normalizedTransportHom
    (L : EquivariantGroupoidLift Γ actions) :
    L.normalizationInv.equivalence.inv.normalizedTransportHom =
      (toLiftNormalizedTransportIso L.normalizedTransport).inv := by
  apply (cancel_mono (toLiftNormalizedTransportIso L.normalizedTransport).hom).mp
  rw [Iso.inv_hom_id, ← L.normalizationInv_normalizedTransportHom,
    ← Hom.comp_normalizedTransportHom, ← L.normalizationEquivalence_hom]
  exact (Hom.Hom₂.normalizedTransportHom_eq L.normalizationEquivalence.unit.inv).trans
    (Hom.id_normalizedTransportHom L)

/-- Normalizing the forward unit morphism `L.normalizationEquivalence.hom` yields the inverse
return comparison `(toLiftNormalizedTransportIso L.normalizedTransport).inv`. -/
lemma normalizationEquivalence_hom_normalizedTransportHom
    (L : EquivariantGroupoidLift Γ actions) :
    L.normalizationEquivalence.hom.normalizedTransportHom =
      (toLiftNormalizedTransportIso L.normalizedTransport).inv :=
  L.normalizationInv_equivalence_inv_normalizedTransportHom

namespace Hom

variable {L L' : EquivariantGroupoidLift Γ actions}

/-- Lift a comparison of normalized transports `L.normalizedTransport ⟶ L'.normalizedTransport`
to a morphism of equivariant lifts `L ⟶ L'` by conjugating its reconstruction with the objectwise
normalization equivalences. -/
noncomputable def ofNormalizedTransportHom
    (α : L.normalizedTransport ⟶ L'.normalizedTransport) : L ⟶ L' :=
  L.normalizationEquivalence.hom ≫ α.toLiftHom ≫ L'.normalizationInv

/-- Conjugating a reconstructed normalized-transport comparison by the normalization equivalences
recovers that comparison upon normalization. -/
@[simp]
lemma ofNormalizedTransportHom_normalizedTransportHom
    (α : L.normalizedTransport ⟶ L'.normalizedTransport) :
    (ofNormalizedTransportHom α).normalizedTransportHom = α := by
  simp only [ofNormalizedTransportHom, comp_normalizedTransportHom,
    normalizationEquivalence_hom, normalizationInv_equivalence_inv_normalizedTransportHom,
    normalizationInv_normalizedTransportHom, toLiftNormalizedTransportIso_hom_naturality,
    Iso.inv_hom_id_assoc]

/-- Every lift morphism `φ : L ⟶ L'` is isomorphic via a compatible modification to the lift of
its normalized transport comparison. -/
noncomputable def ofNormalizedTransportHomIso (φ : L ⟶ L') :
    ofNormalizedTransportHom φ.normalizedTransportHom ≅ φ :=
  whiskerLeftIso L.normalizationEquivalence.hom (normalizationInvIso φ) ≪≫
    (α_ L.normalizationEquivalence.hom L.normalizationInv φ).symm ≪≫
    whiskerRightIso L.normalizationEquivalence.unit.symm φ ≪≫
    λ_ φ

/-- Two parallel morphisms of equivariant lifts are connected by a compatible modification if and
only if they induce the same comparison of normalized transports. -/
lemma nonempty_hom₂_iff (φ ψ : L ⟶ L') :
    Nonempty (φ ⟶ ψ) ↔ φ.normalizedTransportHom = ψ.normalizedTransportHom := by
  refine ⟨fun ⟨Θ⟩ ↦ Θ.normalizedTransportHom_eq, fun h ↦ ?_⟩
  refine ⟨((ofNormalizedTransportHomIso φ).symm ≪≫ eqToIso (by rw [h]) ≪≫
    ofNormalizedTransportHomIso ψ).hom⟩

/-- Two parallel morphisms of equivariant lifts are isomorphic in the hom category if and only if
they induce the same comparison of normalized transports. -/
lemma nonempty_iso_iff (φ ψ : L ⟶ L') :
    Nonempty (φ ≅ ψ) ↔ φ.normalizedTransportHom = ψ.normalizedTransportHom :=
  ⟨fun ⟨e⟩ ↦ e.hom.normalizedTransportHom_eq,
    fun h ↦ let ⟨Θ⟩ := (nonempty_hom₂_iff φ ψ).2 h; ⟨asIso Θ⟩⟩

end Hom

/-- Two equivariant lifts over the same prescribed actions are linked by a lift morphism if and
only if their normalized transports are linked by a coherent comparison. -/
lemma nonempty_hom_iff (L L' : EquivariantGroupoidLift Γ actions) :
    Nonempty (L ⟶ L') ↔ Nonempty (L.normalizedTransport ⟶ L'.normalizedTransport) :=
  ⟨fun ⟨φ⟩ ↦ ⟨φ.normalizedTransportHom⟩, fun ⟨α⟩ ↦ ⟨Hom.ofNormalizedTransportHom α⟩⟩

/-- Two equivariant lifts over the same prescribed actions are equivalent in
`EquivariantGroupoidLift Γ actions` if and only if their normalized transports are isomorphic. -/
lemma nonempty_equivalence_iff (L L' : EquivariantGroupoidLift Γ actions) :
    Nonempty (L ≌ L') ↔ Nonempty (L.normalizedTransport ≅ L'.normalizedTransport) :=
  ⟨fun ⟨e⟩ ↦ ⟨asIso e.hom.normalizedTransportHom⟩,
    fun ⟨e⟩ ↦ ⟨(Hom.ofNormalizedTransportHom e.hom).equivalence⟩⟩

section LocalEquivalence

variable (actions)

/-- Normalization induces an equivalence on every hom category of equivariant groupoid lifts. -/
instance isEquivalence_normalizationPseudofunctor_mapFunctor
    (L L' : EquivariantGroupoidLift Γ actions) :
    ((normalizationPseudofunctor actions).mapFunctor L L').IsEquivalence where
  faithful := ⟨fun {_ _} _ _ _ ↦ Subsingleton.elim _ _⟩
  full :=
    { map_surjective {φ ψ} η := by
        have h : φ.normalizedTransportHom = ψ.normalizedTransportHom :=
          congrArg Discrete.as (LocallyDiscrete.eq_of_hom η)
        obtain ⟨Θ⟩ := (Hom.nonempty_hom₂_iff φ ψ).2 h
        exact ⟨Θ, Subsingleton.elim _ _⟩ }
  essSurj :=
    ⟨fun α ↦ ⟨Hom.ofNormalizedTransportHom α.as, ⟨eqToIso (congrArg Quiver.Hom.toLoc
      (Hom.ofNormalizedTransportHom_normalizedTransportHom α.as))⟩⟩⟩

/-- Reconstruction induces an equivalence on every hom category of normalized transports. -/
instance isEquivalence_reconstructionPseudofunctor_mapFunctor
    (N N' : LocallyDiscrete (NormalizedTransport Γ actions)) :
    ((reconstructionPseudofunctor actions).mapFunctor N N').IsEquivalence where
  faithful := ⟨fun {_ _} _ _ _ ↦ Subsingleton.elim _ _⟩
  full :=
    { map_surjective {φ ψ} Θ := by
        have h : φ.as = ψ.as := by
          apply (cancel_epi (toLiftNormalizedTransportIso N.as).hom).mp
          rw [← toLiftNormalizedTransportIso_hom_naturality φ.as,
            ← toLiftNormalizedTransportIso_hom_naturality ψ.as]
          exact congrArg (· ≫ (toLiftNormalizedTransportIso N'.as).hom)
            (Hom.Hom₂.normalizedTransportHom_eq Θ)
        exact ⟨eqToHom (Discrete.ext h), Subsingleton.elim _ _⟩ }
  essSurj :=
    ⟨fun ψ ↦
      let ψ' : N.as.toLift ⟶ N'.as.toLift := ψ
      let α : N.as ⟶ N'.as :=
        (toLiftNormalizedTransportIso N.as).inv ≫ ψ'.normalizedTransportHom ≫
          (toLiftNormalizedTransportIso N'.as).hom
      ⟨α.toLoc, by
        have h : α.toLiftHom.normalizedTransportHom = ψ'.normalizedTransportHom := by
          apply (cancel_mono (toLiftNormalizedTransportIso N'.as).hom).mp
          rw [toLiftNormalizedTransportIso_hom_naturality α]
          simp [α]
        exact (Hom.nonempty_iso_iff α.toLiftHom ψ').2 h⟩⟩

end LocalEquivalence

end Classification

end TauCeti.EquivariantGroupoidLift
