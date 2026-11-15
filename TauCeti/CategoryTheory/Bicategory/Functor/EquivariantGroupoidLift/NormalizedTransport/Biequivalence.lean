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
# The biequivalence between equivariant lifts and normalized transport

An equivariant groupoid lift packages a joint pseudofunctor on `Γ × SingleObj H` together with
action-compatible equivalences to prescribed fiber categories. Normalizing a lift conjugates its
joint functors by chosen inverse fiber equivalences to obtain coherent equivariant transport data
on the prescribed fibers themselves, while reconstruction turns normalized transport data back into
a lift whose fiber comparisons are identity functors. Because original lifts carry arbitrary
auxiliary joint categories and chosen fiber comparisons, normalization and reconstruction do not
invert one another strictly on types; instead they form a biequivalence between the bicategory of
equivariant lifts and the locally discrete bicategory of normalized transports.

For a morphism of lifts `φ : L ⟶ L'`, the inverse-fiber comparisons `φ.inverseFiberIso p` assemble
into a compatible invertible modification
`φ.normalizationInvNaturality :
  φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv ≅ L.normalizationInv ≫ φ`.
Since hom-categories in `EquivariantGroupoidLift Γ actions` are thin groupoids, these modifications
automatically satisfy the coherence equations of a strong transformation `normalizationUnitInv`,
and taking mates across the objectwise equivalences `L.normalizationEquivalence` yields the forward
unit strong transformation `normalizationUnitHom` and adjoint equivalence `normalizationUnitEquiv`.
Combining `normalizationUnitEquiv` with `normalizationCounitEquiv` gives
`normalizationBiequivalence`.

Normalizing the objectwise comparison `L.normalizationInv` recovers the counit isomorphism
`toLiftNormalizedTransportIso L.normalizedTransport`. Together with unit naturality, this identifies
each hom-groupoid `L ⟶ L'` with the discrete category of normalized transport morphisms
`L.normalizedTransport ⟶ L'.normalizedTransport`: every normalized transport comparison lifts to a
morphism of lifts, and two parallel morphisms of lifts admit a compatible modification if and only
if they induce the same comparison of normalized transports.

## Main declarations

* `TauCeti.EquivariantGroupoidLift.normalizationInv_normalizedTransportHom`: normalizing
  `L.normalizationInv` gives `(toLiftNormalizedTransportIso L.normalizedTransport).hom`;
* `TauCeti.EquivariantGroupoidLift.Hom.normalizationInvNaturality`,
  `TauCeti.EquivariantGroupoidLift.Hom.normalizationHomNaturality`: naturality of the objectwise
  normalization comparisons in morphisms of lifts;
* `TauCeti.EquivariantGroupoidLift.normalizationUnitHom`,
  `TauCeti.EquivariantGroupoidLift.normalizationUnitInv`,
  `TauCeti.EquivariantGroupoidLift.normalizationUnitEquiv`: the unit strong transformations and
  adjoint equivalence comparing the identity pseudofunctor with normalization followed by
  reconstruction;
* `TauCeti.EquivariantGroupoidLift.normalizationBiequivalence`: the biequivalence between
  `EquivariantGroupoidLift Γ actions` and `LocallyDiscrete (NormalizedTransport Γ actions)`;
* `TauCeti.EquivariantGroupoidLift.Hom.ofNormalizedTransportHom`,
  `TauCeti.EquivariantGroupoidLift.Hom.isoOfNormalizedTransportHomEq`,
  `TauCeti.EquivariantGroupoidLift.normalizationMapFunctorEquivalence`: lifting normalized
  transport comparisons, uniqueness up to compatible modification, and the resulting equivalence on
  hom-categories.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055), Chapter 4: strong transformations,
  modifications and biequivalences.
* Edward Frenkel,
  [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  Cambridge Studies in Advanced Mathematics 103 (2007): families of local categories over
  parameter groupoids with loop group actions.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory CategoryTheory.Prod Pseudofunctor.StrongTrans NormalizedTransport

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}

/-! ### Triangle coherence of the objectwise unit comparison -/

namespace Hom

/-- Normalizing the inverse of a lift equivalence gives the inverse of its normalized comparison. -/
@[simp]
lemma equivalence_inv_normalizedTransportHom {L L' : EquivariantGroupoidLift Γ actions}
    (φ : L ⟶ L') :
    φ.equivalence.inv.normalizedTransportHom = CategoryTheory.inv φ.normalizedTransportHom := by
  have h : φ.normalizedTransportHom ≫ φ.equivalence.inv.normalizedTransportHom = 𝟙 _ := by
    rw [← comp_normalizedTransportHom, ← id_normalizedTransportHom L]
    exact φ.equivalence.unit.inv.normalizedTransportHom_eq
  exact (IsIso.inv_eq_of_hom_inv_id h).symm

end Hom

/-- On each prescribed fiber, the inverse-fiber comparison of `L.normalizationInv` maps the chosen
counit of the reconstructed identity equivalence by the inverse fiber equivalence of `L`. -/
lemma normalizationInv_inverseFiberIso_hom_app (L : EquivariantGroupoidLift Γ actions)
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

private lemma normalizationInv_jointMapIso_hom_app (L : EquivariantGroupoidLift Γ actions)
    {p q : Γ} (g : p ⟶ q) (y : fiber actions p) :
    (L.normalizationInv.jointMapIso g).hom.app y =
      (L.fiberEquivalence q).unitInv.app
          ((L.jointMap g).obj ((L.fiberEquivalence p).inverse.obj
            ((act actions p (𝟙 (SingleObj.star H))).obj y))) ≫
        (L.jointMap g).map
          ((L.fiberEquivalence p).inverse.map ((actId actions p).hom.app y)) := by
  have hid : (L.joint.mapComp' (𝟙 p ×ₘ 𝟙 (SingleObj.star H)).toLoc
      (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
      (by
        apply congrArg Quiver.Hom.toLoc
        exact Prod.ext (Category.id_comp _) (Category.comp_id _))).inv.toNatTrans.app
        ((L.fiberEquivalence p).inverse.obj y) =
      (L.jointMap g).map ((L.jointMapId p).hom.app ((L.fiberEquivalence p).inverse.obj y)) := by
    have h := L.joint.mapComp'_id_comp_inv_app (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
      ((L.fiberEquivalence p).inverse.obj y)
    simp only [jointMapId_hom_app, ← prod_id, Quiver.Hom.id_toLoc,
      Pseudofunctor.mapId'_eq_mapId] at h ⊢
    exact h
  have hact : (L.actInverseIso p (𝟙 (SingleObj.star H))).hom.app y ≫
      (L.jointMapId p).hom.app ((L.fiberEquivalence p).inverse.obj y) =
      (L.fiberEquivalence p).inverse.map ((actId actions p).hom.app y) := by
    simpa only [Category.assoc] using L.actInverseIso_actId p y
  erw [Hom.jointMapIso_hom_app, L.normalizationJointInv_naturality_hom_app]
  change (L.normalizationJointIso (g ×ₘ 𝟙 (SingleObj.star H))).hom.app y = _
  rw [L.normalizationJointIso_hom_app, hid, ← (L.jointMap g).map_comp, hact]

/-- Along each parameter arrow, the transport comparison induced by `L.normalizationInv` agrees
with the canonical return isomorphism `toLiftTransportIso` of `L.normalizedTransport`. -/
lemma normalizationInv_transportIso_hom_app (L : EquivariantGroupoidLift Γ actions)
    {p q : Γ} (g : p ⟶ q) (x : fiber actions p) :
    (L.normalizationInv.transportIso g).hom.app x =
      (L.normalizedTransport.toLiftTransportIso g).hom.app x := by
  let y₀ : fiber actions p := (L.normalizedTransport.toLift.fiberEquivalence p).inverse.obj x
  let ε₀ : y₀ ⟶ x := (L.normalizedTransport.toLift.fiberEquivalence p).counit.app x
  rw [Hom.transportIso_hom_app]
  erw [L.normalizationInv_jointMapIso_hom_app, L.normalizationInv_inverseFiberIso_hom_app,
    (L.fiberEquivalence q).functor.map_comp, Category.assoc]
  rw [Hom.fiberFunctorIso_inv_app, L.normalizationInv_fiberIso_inv_as_app]
  -- Cancel the counit inverse and mapped unit inverse of `L.fiberEquivalence q`.
  erw [(L.fiberEquivalence q).counitInv_functor_comp_assoc]
  erw [← (L.fiberEquivalence q).functor.map_comp, ← (L.jointMap g).map_comp,
    ← (L.fiberEquivalence p).inverse.map_comp]
  rw [toLiftTransportIso_hom_app, ← (L.normalizedTransport.transport g).map_comp]
  exact congrArg (L.transport g).map ((actId actions p).hom.naturality ε₀).symm

/-- The transport comparison induced by `L.normalizationInv` along `g` is the canonical return
isomorphism `toLiftTransportIso` of `L.normalizedTransport`. -/
lemma normalizationInv_transportIso (L : EquivariantGroupoidLift Γ actions) {p q : Γ}
    (g : p ⟶ q) :
    L.normalizationInv.transportIso g = L.normalizedTransport.toLiftTransportIso g := by
  ext x
  exact L.normalizationInv_transportIso_hom_app g x

/-- Normalizing the objectwise comparison `L.normalizationInv` recovers the forward counit
isomorphism `toLiftNormalizedTransportIso` of `L.normalizedTransport`. -/
@[simp]
lemma normalizationInv_normalizedTransportHom (L : EquivariantGroupoidLift Γ actions) :
    L.normalizationInv.normalizedTransportHom =
      (toLiftNormalizedTransportIso L.normalizedTransport).hom := by
  refine NormalizedTransport.Hom.ext fun p q g ↦ ?_
  rw [Hom.normalizedTransportHom_transportIso, toLiftNormalizedTransportIso_hom_transportIso]
  exact L.normalizationInv_transportIso g

/-- Normalizing the forward objectwise equivalence `L.normalizationEquivalence.hom` gives the
inverse counit isomorphism `toLiftNormalizedTransportIso` of `L.normalizedTransport`. -/
lemma normalizationEquivalence_hom_normalizedTransportHom
    (L : EquivariantGroupoidLift Γ actions) :
    L.normalizationEquivalence.hom.normalizedTransportHom =
      (toLiftNormalizedTransportIso L.normalizedTransport).inv := by
  simp [normalizationInv_normalizedTransportHom]

/-! ### Naturality of the objectwise unit comparisons -/

private lemma trans_leftUnitor_symm_hom_app {D D' : Cat.{v, w}} {T U : D ⟶ D'} (e : T ≅ U)
    (X : D) :
    (e ≪≫ (λ_ U).symm).hom.toNatTrans.app X = e.hom.toNatTrans.app X := by
  simp

private lemma trans_leftUnitor_symm_inv_app {D D' : Cat.{v, w}} {T U : D ⟶ D'} (e : T ≅ U)
    (X : D) :
    (e ≪≫ (λ_ U).symm).inv.toNatTrans.app X = e.inv.toNatTrans.app X := by
  simp

private lemma normalizationInv_fiber_comm_cat
    {D₀ D₁ D₂ : Cat.{v, w}} {F : D₀ ⟶ D₁} {G : D₁ ⟶ D₂}
    {I₁ : D₀ ⟶ D₂} {E₁ : D₁ ⟶ D₀} {E₂ : D₂ ⟶ D₀}
    (e : F ≫ G ≅ I₁) (c₁ : I₁ ≫ E₂ ⟶ 𝟙 D₀)
    (b : G ≫ E₂ ⟶ E₁) (c₀ : F ≫ E₁ ⟶ 𝟙 D₀)
    (h : ∀ X : D₀,
      E₂.toFunctor.map (e.hom.toNatTrans.app X) ≫ c₁.toNatTrans.app X =
        b.toNatTrans.app (F.toFunctor.obj X) ≫ c₀.toNatTrans.app X) :
    (e ≪≫ (λ_ I₁).symm).hom ▷ E₂ ≫
      ((α_ (𝟙 D₀) I₁ E₂).hom ≫ 𝟙 D₀ ◁ c₁ ≫ (λ_ (𝟙 D₀)).hom) =
      (α_ F G E₂).hom ≫ F ◁ b ≫ c₀ := by
  ext X
  simpa using h X

namespace Hom

variable {L L' : EquivariantGroupoidLift Γ actions} (φ : L ⟶ L')

/-- Along a parameter arrow `g`, the inverse-fiber comparison at `q` followed by the mapped
transport isomorphism agrees with the mapped unit inverse of `L` followed by the joint naturality
cell of `φ` and the inverse-fiber comparison at `p`. -/
private lemma inverseFiberIso_comp_inverse_map_transportIso {p q : Γ} (g : p ⟶ q)
    (z : fiber actions p) :
    (φ.inverseFiberIso q).hom.app ((L.transport g).obj z) ≫
        (L'.fiberEquivalence q).inverse.map ((φ.transportIso g).hom.app z) ≫
          (L'.fiberEquivalence q).unitInv.app
            ((L'.jointMap g).obj ((L'.fiberEquivalence p).inverse.obj z)) =
      (φ.jointFunctor q).map
          ((L.fiberEquivalence q).unitInv.app
            ((L.jointMap g).obj ((L.fiberEquivalence p).inverse.obj z))) ≫
        (φ.jointMapIso g).hom.app ((L.fiberEquivalence p).inverse.obj z) ≫
          (L'.jointMap g).map ((φ.inverseFiberIso p).hom.app z) := by
  rw [φ.transportIso_hom_app]
  dsimp only [EquivariantGroupoidLift.transport, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  erw [(L'.fiberEquivalence q).unitInv_naturality,
    (L'.fiberEquivalence q).unitInv_naturality_assoc]
  rw [φ.inverseFiberIso_hom_app_comp_unitInv_assoc]

/-- Along any joint arrow `f`, the inverse-fiber comparisons commute the joint comparison of `L`
followed by `φ` with the reconstructed normalized comparison of `φ` followed by the joint
comparison of `L'`. -/
private lemma normalizationInv_jointIso_comm {p q : Γ}
    (f : (p, SingleObj.star H) ⟶ (q, SingleObj.star H)) (x : fiber actions p) :
    (φ.inverseFiberIso q).hom.app ((L.transport f.1).obj ((act actions p f.2).obj x)) ≫
        (L'.fiberEquivalence q).inverse.map
          ((φ.transportIso f.1).hom.app ((act actions p f.2).obj x)) ≫
        (L'.normalizationJointIso f).hom.app x =
      ((φ.jointFunctor q).map ((L.normalizationJointIso f).hom.app x) ≫
          (φ.joint.naturality f.toLoc).hom.toNatTrans.app
            ((L.fiberEquivalence p).inverse.obj x)) ≫
        (L'.joint.map f.toLoc).toFunctor.map ((φ.inverseFiberIso p).hom.app x) := by
  have hcomp : (𝟙 p ×ₘ f.2).toLoc ≫ (f.1 ×ₘ 𝟙 (SingleObj.star H)).toLoc = f.toLoc := by
    apply congrArg Quiver.Hom.toLoc
    exact Prod.ext (Category.id_comp _) (Category.comp_id _)
  rw [L.normalizationJointIso_hom_app f x]
  erw [(φ.jointFunctor q).map_comp, (φ.jointFunctor q).map_comp]
  repeat rw [Category.assoc]
  -- Factor the joint naturality cell of `φ` at `f` into its symmetry and parameter parts.
  have hφ := φ.joint.naturality_comp'_hom_app (𝟙 p ×ₘ f.2).toLoc
    (f.1 ×ₘ 𝟙 (SingleObj.star H)).toLoc f.toLoc hcomp ((L.fiberEquivalence p).inverse.obj x)
  erw [reassoc_of% hφ,
    ← (φ.jointFunctor q).map_comp_assoc ((L.joint.mapComp' _ _ _ _).inv.toNatTrans.app _),
    Cat.Hom.inv_hom_id_toNatTrans_app, (φ.jointFunctor q).map_id, Category.id_comp]
  -- Move `inverseFiberIso p` past the target compositor `mapComp'` by naturality.
  erw [← (L'.joint.mapComp' (𝟙 p ×ₘ f.2).toLoc (f.1 ×ₘ 𝟙 (SingleObj.star H)).toLoc f.toLoc
    hcomp).inv.toNatTrans.naturality]
  dsimp only [Cat.Hom.comp_toFunctor, Functor.comp_map]
  rw [← φ.jointMapIso_hom_app, ← φ.jointActIso_hom_app]
  -- Move `actInverseIso` past `jointMapIso` and combine the symmetry comparisons at `p`.
  erw [(φ.jointMapIso f.1).hom.naturality_assoc ((L.actInverseIso p f.2).hom.app x),
    ← (L'.jointMap f.1).map_comp_assoc ((φ.jointActIso p f.2).hom.app _),
    ← (L'.jointMap f.1).map_comp_assoc ((φ.jointFunctor p).map _),
    φ.inverseFiberIso_actInverseIso p f.2 x, (L'.jointMap f.1).map_comp]
  repeat rw [Category.assoc]
  -- Close with the parameter-arrow compatibility at `(act actions p f.2).obj x`.
  have hparam := φ.inverseFiberIso_comp_inverse_map_transportIso f.1 ((act actions p f.2).obj x)
  dsimp only [EquivariantGroupoidLift.transport, Functor.comp_obj] at hparam ⊢
  rw [L'.normalizationJointIso_hom_app f x]
  exact (reassoc_of% hparam) _

/-- The inverse-fiber comparisons are compatible with the prescribed-fiber modifications of
`L.normalizationInv ≫ φ` and `φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv`. -/
private lemma normalizationInv_fiber_comm (p : Γ) (a : LocallyDiscrete (SingleObj H)) :
    (Cat.Hom.isoMk (φ.inverseFiberIso p) ≪≫
        (λ_ (L'.fiberEquivalence p).inverse.toCatHom).symm).hom ▷ (L'.comparison p).app a ≫
      ((φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv).fiberIso p).hom.as.app a =
      ((L.normalizationInv ≫ φ).fiberIso p).hom.as.app a := by
  obtain ⟨⟨⟩⟩ := a
  have hlhs :
      ((φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv).fiberIso p).hom.as.app
          ⟨SingleObj.star H⟩ =
        (α_ (𝟙 (fiber actions p)) (L'.fiberEquivalence p).inverse.toCatHom
            ((L'.comparison p).app ⟨SingleObj.star H⟩)).hom ≫
          𝟙 (fiber actions p) ◁
            (Cat.Hom.isoMk (L'.fiberEquivalence p).counitIso).hom ≫
          (λ_ (𝟙 (fiber actions p))).hom :=
    ((congrArg (fun e ↦ e.hom.as.app ⟨SingleObj.star H⟩)
      (EquivariantGroupoidLift.comp_fiberIso φ.normalizedTransportHom.toLiftHom
        L'.normalizationInv p)).trans
      (comp_fiberIso_hom_as_app φ.normalizedTransportHom.toLiftHom L'.normalizationInv p
        ⟨SingleObj.star H⟩)).trans
      (by
        rw [L'.normalizationInv_fiberIso_hom_as_app,
          NormalizedTransport.Hom.toLiftHom_fiberIso_hom_as_app]
        rfl)
  have hrhs :
      ((L.normalizationInv ≫ φ).fiberIso p).hom.as.app ⟨SingleObj.star H⟩ =
        (α_ (L.fiberEquivalence p).inverse.toCatHom (φ.joint.app ⟨(p, SingleObj.star H)⟩)
            ((L'.comparison p).app ⟨SingleObj.star H⟩)).hom ≫
          (L.fiberEquivalence p).inverse.toCatHom ◁
            ((φ.fiberIso p).hom.as.app ⟨SingleObj.star H⟩) ≫
          (Cat.Hom.isoMk (L.fiberEquivalence p).counitIso).hom :=
    ((congrArg (fun e ↦ e.hom.as.app ⟨SingleObj.star H⟩)
      (EquivariantGroupoidLift.comp_fiberIso L.normalizationInv φ p)).trans
      (comp_fiberIso_hom_as_app L.normalizationInv φ p ⟨SingleObj.star H⟩)).trans
      (by rw [L.normalizationInv_fiberIso_hom_as_app]; rfl)
  refine (congrArg (_ ▷ _ ≫ ·) hlhs).trans ?_
  refine (normalizationInv_fiber_comm_cat (Cat.Hom.isoMk (φ.inverseFiberIso p))
    (Cat.Hom.isoMk (L'.fiberEquivalence p).counitIso).hom
    ((φ.fiberIso p).hom.as.app ⟨SingleObj.star H⟩)
    (Cat.Hom.isoMk (L.fiberEquivalence p).counitIso).hom fun x ↦ ?_).trans hrhs.symm
  exact (φ.functor_map_inverseFiberIso_hom_app_comp_counit p x).trans
    (congrArg (· ≫ _) (fiberFunctorIso_hom_app φ p ((L.fiberEquivalence p).inverse.obj x)))

/-- The underlying joint naturality isomorphism of `normalizationInv` with respect to `φ`,
whose component over `p` is `φ.inverseFiberIso p` up to a left unitor. -/
private noncomputable def normalizationInvJointIso :
    (L.normalizationInv ≫ φ).joint ≅
      (φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv).joint :=
  Pseudofunctor.StrongTrans.isoMk
    (fun X ↦ Cat.Hom.isoMk (φ.inverseFiberIso X.as.1) ≪≫
      (λ_ (L'.fiberEquivalence X.as.1).inverse.toCatHom).symm)
    (fun {X Y} f ↦ by
      obtain ⟨p, ⟨⟩⟩ := X
      obtain ⟨q, ⟨⟩⟩ := Y
      refine Cat.whiskerLeft_comp_eq_comp_whiskerRight _ _ _ _ fun (x : fiber actions p) ↦ ?_
      have hjn : (φ.normalizedTransportHom.jointHom.naturality f).hom.toNatTrans.app x =
          (φ.transportIso f.as.1).hom.app ((act actions p f.as.2).obj x) := by
        rw [φ.normalizedTransportHom.jointHom_naturality_hom_app,
          φ.normalizedTransportHom_transportIso]
      have hn :
          (((φ.normalizedTransportHom.jointHom ≫ L'.normalizationJointInv).naturality
            f).hom.toNatTrans.app x) =
            (L'.fiberEquivalence q).inverse.map
              ((φ.transportIso f.as.1).hom.app ((act actions p f.as.2).obj x)) ≫
            (L'.normalizationJointIso f.as).hom.app x :=
        (Pseudofunctor.StrongTrans.comp_naturality_hom_app
          φ.normalizedTransportHom.jointHom L'.normalizationJointInv f x).trans
          (congrArg (· ≫ _) (congrArg (L'.fiberEquivalence q).inverse.map hjn))
      have hm :
          (((L.normalizationJointInv ≫ φ.joint).naturality f).hom.toNatTrans.app x) =
            (φ.jointFunctor q).map ((L.normalizationJointIso f.as).hom.app x) ≫
              (φ.joint.naturality f.as.toLoc).hom.toNatTrans.app
                ((L.fiberEquivalence p).inverse.obj x) :=
        Pseudofunctor.StrongTrans.comp_naturality_hom_app L.normalizationJointInv φ.joint f x
      erw [trans_leftUnitor_symm_hom_app, trans_leftUnitor_symm_hom_app]
      exact (congrArg (_ ≫ ·) hn).trans
        ((φ.normalizationInv_jointIso_comm f.as x).trans (congrArg (· ≫ _) hm.symm)))

private lemma normalizationInvJointIso_hom_as_app (X : LocallyDiscrete (Γ × SingleObj H)) :
    φ.normalizationInvJointIso.hom.as.app X =
      (Cat.Hom.isoMk (φ.inverseFiberIso X.as.1) ≪≫
        (λ_ (L'.fiberEquivalence X.as.1).inverse.toCatHom).symm).hom :=
  rfl

private lemma normalizationInvJointIso_inv_as_app (X : LocallyDiscrete (Γ × SingleObj H)) :
    φ.normalizationInvJointIso.inv.as.app X =
      (Cat.Hom.isoMk (φ.inverseFiberIso X.as.1) ≪≫
        (λ_ (L'.fiberEquivalence X.as.1).inverse.toCatHom).symm).inv :=
  rfl

private lemma normalizationInv_fiber_comm_inv (p : Γ) (a : LocallyDiscrete (SingleObj H)) :
    φ.normalizationInvJointIso.inv.as.app ((Prod.sectR p (SingleObj H)).toPseudofunctor.obj a) ▷
        (L'.comparison p).app a ≫
      ((L.normalizationInv ≫ φ).fiberIso p).hom.as.app a =
      ((φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv).fiberIso p).hom.as.app a :=
  (congrArg (· ▷ (L'.comparison p).app a ≫ _) (φ.normalizationInvJointIso_inv_as_app _)).trans
    ((congrArg (_ ≫ ·) (φ.normalizationInv_fiber_comm p a).symm).trans
      (inv_hom_whiskerRight_assoc
        (Cat.Hom.isoMk (φ.inverseFiberIso p) ≪≫
          (λ_ (L'.fiberEquivalence p).inverse.toCatHom).symm)
        ((L'.comparison p).app a)
        (((φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv).fiberIso p).hom.as.app a)))

/-- Naturality of the objectwise inverse unit comparisons `normalizationInv` with respect to a
morphism of lifts `φ : L ⟶ L'`. On each joint fiber over `p`, the inverse direction of this
invertible modification has component `(φ.inverseFiberIso p).hom`. -/
noncomputable def normalizationInvNaturality :
    φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv ≅ L.normalizationInv ≫ φ where
  hom := ⟨φ.normalizationInvJointIso.inv, φ.normalizationInv_fiber_comm_inv⟩
  inv := ⟨φ.normalizationInvJointIso.hom, fun p a ↦
    (congrArg (· ▷ (L'.comparison p).app a ≫ _) (φ.normalizationInvJointIso_hom_as_app _)).trans
      (φ.normalizationInv_fiber_comm p a)⟩
  hom_inv_id := EquivariantGroupoidLift.hom₂_ext φ.normalizationInvJointIso.inv_hom_id
  inv_hom_id := EquivariantGroupoidLift.hom₂_ext φ.normalizationInvJointIso.hom_inv_id

private lemma normalizationInvNaturality_hom_joint :
    φ.normalizationInvNaturality.hom.joint = φ.normalizationInvJointIso.inv :=
  rfl

private lemma normalizationInvNaturality_inv_joint :
    φ.normalizationInvNaturality.inv.joint = φ.normalizationInvJointIso.hom :=
  rfl

/-- On objects of the prescribed fiber, the forward direction of `normalizationInvNaturality`
acts by `(φ.inverseFiberIso p).inv`. -/
lemma normalizationInvNaturality_hom_joint_as_app (X : LocallyDiscrete (Γ × SingleObj H))
    (x : fiber actions X.as.1) :
    ((φ.normalizationInvNaturality.hom.joint.as.app X).toNatTrans.app x) =
      (φ.inverseFiberIso X.as.1).inv.app x := by
  obtain ⟨p, ⟨⟩⟩ := X
  rw [φ.normalizationInvNaturality_hom_joint, φ.normalizationInvJointIso_inv_as_app]
  exact trans_leftUnitor_symm_inv_app (Cat.Hom.isoMk (φ.inverseFiberIso p)) x

/-- On objects of the prescribed fiber, the inverse direction of `normalizationInvNaturality`
acts by `(φ.inverseFiberIso p).hom`. -/
lemma normalizationInvNaturality_inv_joint_as_app (X : LocallyDiscrete (Γ × SingleObj H))
    (x : fiber actions X.as.1) :
    ((φ.normalizationInvNaturality.inv.joint.as.app X).toNatTrans.app x) =
      (φ.inverseFiberIso X.as.1).hom.app x := by
  obtain ⟨p, ⟨⟩⟩ := X
  rw [φ.normalizationInvNaturality_inv_joint, φ.normalizationInvJointIso_hom_as_app]
  exact trans_leftUnitor_symm_hom_app (Cat.Hom.isoMk (φ.inverseFiberIso p)) x

/-- Naturality of the forward objectwise unit comparisons `normalizationEquivalence.hom` with
respect to a morphism of lifts `φ : L ⟶ L'`, obtained as the mate of
`φ.normalizationInvNaturality.inv` across `L.normalizationEquivalence` and
`L'.normalizationEquivalence`. -/
noncomputable def normalizationHomNaturality :
    φ ≫ L'.normalizationEquivalence.hom ≅
      L.normalizationEquivalence.hom ≫ φ.normalizedTransportHom.toLiftHom :=
  asIso ((Bicategory.mateEquiv L.normalizationEquivalence.adj
    L'.normalizationEquivalence.adj).symm φ.normalizationInvNaturality.inv)

lemma normalizationHomNaturality_hom :
    φ.normalizationHomNaturality.hom =
      (Bicategory.mateEquiv L.normalizationEquivalence.adj
        L'.normalizationEquivalence.adj).symm φ.normalizationInvNaturality.inv :=
  (rfl)

@[simp]
lemma mateEquiv_normalizationHomNaturality_hom :
    Bicategory.mateEquiv L.normalizationEquivalence.adj L'.normalizationEquivalence.adj
        φ.normalizationHomNaturality.hom =
      φ.normalizationInvNaturality.inv :=
  Equiv.apply_symm_apply _ _

end Hom

/-! ### The normalization unit and biequivalence -/

section Biequivalence

variable (actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w})

/-- The strong transformation from normalization followed by reconstruction to the identity
pseudofunctor on `EquivariantGroupoidLift Γ actions`, with components `L.normalizationInv` and
naturality cells `φ.normalizationInvNaturality`. All 2-dimensional coherence laws hold by
uniqueness of compatible modifications. -/
-- Exposed so the endpoints of the unit and counit component equations of `normalizationUnitEquiv`
-- reduce to `L.normalizationEquivalence.hom` and `L.normalizationInv`.
@[expose] noncomputable def normalizationUnitInv :
    (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) ⟶
      Pseudofunctor.id (EquivariantGroupoidLift Γ actions) where
  app L := L.normalizationInv
  naturality φ := φ.normalizationInvNaturality
  naturality_naturality _ := Subsingleton.elim _ _
  naturality_id _ := Subsingleton.elim _ _
  naturality_comp _ _ := Subsingleton.elim _ _

@[simp]
lemma normalizationUnitInv_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitInv actions).app L = L.normalizationInv :=
  (rfl)

@[simp]
lemma normalizationUnitInv_naturality {L L' : EquivariantGroupoidLift Γ actions} (φ : L ⟶ L') :
    (normalizationUnitInv actions).naturality φ = φ.normalizationInvNaturality :=
  (rfl)

/-- The strong transformation from the identity pseudofunctor on `EquivariantGroupoidLift Γ actions`
to normalization followed by reconstruction, with components `L.normalizationEquivalence.hom` and
naturality cells `φ.normalizationHomNaturality`. -/
-- Exposed so the endpoints of the unit and counit component equations of `normalizationUnitEquiv`
-- reduce to `L.normalizationEquivalence.hom` and `L.normalizationInv`.
@[expose] noncomputable def normalizationUnitHom :
    Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ⟶
      (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) where
  app L := L.normalizationEquivalence.hom
  naturality φ := φ.normalizationHomNaturality
  naturality_naturality _ := Subsingleton.elim _ _
  naturality_id _ := Subsingleton.elim _ _
  naturality_comp _ _ := Subsingleton.elim _ _

@[simp]
lemma normalizationUnitHom_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitHom actions).app L = L.normalizationEquivalence.hom :=
  (rfl)

@[simp]
lemma normalizationUnitHom_naturality {L L' : EquivariantGroupoidLift Γ actions} (φ : L ⟶ L') :
    (normalizationUnitHom actions).naturality φ = φ.normalizationHomNaturality :=
  (rfl)

/-- The identity pseudofunctor of `EquivariantGroupoidLift Γ actions` is equivalent to
normalization followed by reconstruction, with objectwise components `L.normalizationEquivalence`.
Modification naturality and the left triangle identity follow from uniqueness of compatible
modifications. -/
-- Exposed so the component equations of the unit and counit modifications retain their literal
-- endpoints without unfolding the equivalence record.
@[expose] noncomputable def normalizationUnitEquiv :
    Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ≌
      (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) where
  hom := normalizationUnitHom actions
  inv := normalizationUnitInv actions
  unit := Pseudofunctor.StrongTrans.isoMk (fun L ↦ L.normalizationEquivalence.unit)
    (fun _ ↦ Subsingleton.elim _ _)
  counit := Pseudofunctor.StrongTrans.isoMk (fun L ↦ L.normalizationEquivalence.counit)
    (fun _ ↦ Subsingleton.elim _ _)
  left_triangle := Iso.ext (Pseudofunctor.StrongTrans.homCategory.ext
    fun _ ↦ Subsingleton.elim _ _)

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
    (normalizationUnitEquiv actions).counit.hom.as.app L = L.normalizationEquivalence.counit.hom :=
  (rfl)

@[simp]
lemma normalizationUnitEquiv_counit_inv_as_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitEquiv actions).counit.inv.as.app L = L.normalizationEquivalence.counit.inv :=
  (rfl)

/-- The biequivalence between the bicategory of equivariant groupoid lifts and the locally
discrete bicategory of normalized transports on the prescribed fibers. -/
@[expose] noncomputable def normalizationBiequivalence :
    Biequivalence (EquivariantGroupoidLift Γ actions)
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

/-! ### Equivalence on hom-categories and classification up to equivalence -/

namespace Hom

variable {L L' : EquivariantGroupoidLift Γ actions}

/-- Lift a morphism of normalized transports `α : L.normalizedTransport ⟶ L'.normalizedTransport`
to a morphism of equivariant lifts `L ⟶ L'` by conjugating its reconstructed morphism `α.toLiftHom`
with the objectwise normalization equivalences of `L` and `L'`. -/
noncomputable def ofNormalizedTransportHom
    (α : L.normalizedTransport ⟶ L'.normalizedTransport) : L ⟶ L' :=
  L.normalizationEquivalence.hom ≫ α.toLiftHom ≫ L'.normalizationInv

/-- Normalizing a lifted normalized-transport comparison recovers the original comparison. -/
@[simp]
lemma ofNormalizedTransportHom_normalizedTransportHom
    (α : L.normalizedTransport ⟶ L'.normalizedTransport) :
    (ofNormalizedTransportHom α).normalizedTransportHom = α := by
  rw [ofNormalizedTransportHom, comp_normalizedTransportHom, comp_normalizedTransportHom,
    L.normalizationEquivalence_hom_normalizedTransportHom,
    L'.normalizationInv_normalizedTransportHom,
    toLiftNormalizedTransportIso_hom_naturality, Iso.inv_hom_id_assoc]

/-- Every morphism of equivariant lifts is canonically isomorphic to the lift of its normalized
transport comparison. -/
noncomputable def ofNormalizedTransportHomIso (φ : L ⟶ L') :
    ofNormalizedTransportHom φ.normalizedTransportHom ≅ φ :=
  whiskerLeftIso L.normalizationEquivalence.hom φ.normalizationInvNaturality ≪≫
    (α_ L.normalizationEquivalence.hom L.normalizationInv φ).symm ≪≫
    whiskerRightIso L.normalizationEquivalence.unit.symm φ ≪≫
    λ_ φ

/-- Two parallel morphisms of equivariant lifts with equal normalized transport comparisons are
isomorphic by a compatible modification. -/
noncomputable def isoOfNormalizedTransportHomEq {φ ψ : L ⟶ L'}
    (h : φ.normalizedTransportHom = ψ.normalizedTransportHom) : φ ≅ ψ :=
  φ.ofNormalizedTransportHomIso.symm ≪≫
    eqToIso (congrArg ofNormalizedTransportHom h) ≪≫
    ψ.ofNormalizedTransportHomIso

/-- Two parallel morphisms of equivariant lifts are isomorphic if and only if they induce the
same comparison of normalized transports. -/
lemma nonempty_iso_iff_normalizedTransportHom_eq (φ ψ : L ⟶ L') :
    Nonempty (φ ≅ ψ) ↔ φ.normalizedTransportHom = ψ.normalizedTransportHom :=
  ⟨fun ⟨e⟩ ↦ e.hom.normalizedTransportHom_eq, fun h ↦ ⟨isoOfNormalizedTransportHomEq h⟩⟩

/-- Two parallel morphisms of equivariant lifts admit a compatible modification if and only if
they induce the same comparison of normalized transports. -/
lemma nonempty_hom₂_iff_normalizedTransportHom_eq (φ ψ : L ⟶ L') :
    Nonempty (φ ⟶ ψ) ↔ φ.normalizedTransportHom = ψ.normalizedTransportHom :=
  ⟨fun ⟨Θ⟩ ↦ Θ.normalizedTransportHom_eq, fun h ↦ ⟨(isoOfNormalizedTransportHomEq h).hom⟩⟩

end Hom

/-- On each hom-category, `normalizationPseudofunctor` induces an equivalence from the thin
groupoid `L ⟶ L'` of equivariant lift morphisms and compatible modifications to the discrete
category of normalized transport comparisons `L.normalizedTransport ⟶ L'.normalizedTransport`. -/
@[expose] noncomputable def normalizationMapFunctorEquivalence
    (L L' : EquivariantGroupoidLift Γ actions) :
    (L ⟶ L') ≌
      ((normalizationPseudofunctor actions).obj L ⟶
        (normalizationPseudofunctor actions).obj L') where
  functor := (normalizationPseudofunctor actions).mapFunctor L L'
  inverse := Discrete.functor Hom.ofNormalizedTransportHom
  unitIso := NatIso.ofComponents (fun φ ↦ φ.ofNormalizedTransportHomIso.symm)
    (fun _ ↦ Subsingleton.elim _ _)
  counitIso := Discrete.natIso fun α ↦
    Discrete.eqToIso (Hom.ofNormalizedTransportHom_normalizedTransportHom α.as)
  functor_unitIso_comp _ := Subsingleton.elim _ _

@[simp]
lemma normalizationMapFunctorEquivalence_functor (L L' : EquivariantGroupoidLift Γ actions) :
    (normalizationMapFunctorEquivalence L L').functor =
      (normalizationPseudofunctor actions).mapFunctor L L' :=
  (rfl)

@[simp]
lemma normalizationMapFunctorEquivalence_inverse_obj (L L' : EquivariantGroupoidLift Γ actions)
    (α : (normalizationPseudofunctor actions).obj L ⟶ (normalizationPseudofunctor actions).obj L') :
    (normalizationMapFunctorEquivalence L L').inverse.obj α =
      Hom.ofNormalizedTransportHom α.as :=
  Discrete.functor_obj_eq_as _ _

/-- Normalization is locally an equivalence of hom-categories. -/
instance isEquivalence_normalizationPseudofunctor_mapFunctor
    (L L' : EquivariantGroupoidLift Γ actions) :
    ((normalizationPseudofunctor actions).mapFunctor L L').IsEquivalence :=
  (normalizationMapFunctorEquivalence L L').isEquivalence_functor

/-- Two equivariant lifts are equivalent in `EquivariantGroupoidLift Γ actions` if and only if
their normalized transports are isomorphic in `NormalizedTransport Γ actions`. -/
lemma nonempty_equivalence_iff (L L' : EquivariantGroupoidLift Γ actions) :
    Nonempty (L ≌ L') ↔ Nonempty (L.normalizedTransport ≅ L'.normalizedTransport) :=
  ⟨fun ⟨e⟩ ↦ ⟨asIso e.hom.normalizedTransportHom⟩,
    fun ⟨e⟩ ↦ ⟨(Hom.ofNormalizedTransportHom e.hom).equivalence⟩⟩

end TauCeti.EquivariantGroupoidLift
