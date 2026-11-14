/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Biequivalence
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.NormalizedTransport.Counit
public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.NormalizedTransport.Unit
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Equivalence

/-!
# The biequivalence between equivariant groupoid lifts and normalized transports

Normalizing an equivariant groupoid lift `L` conjugates its joint functors by chosen quasi-inverses
of its prescribed-fiber comparisons, producing normalized transport data `L.normalizedTransport` on
the prescribed fiber categories. Reconstructing a lift from normalized transport data uses identity
fiber comparisons, and `L.normalizationInv : L.normalizedTransport.toLift ⟶ L` compares the
reconstructed lift back to `L` via the chosen inverse fiber equivalences and their counits.

For any morphism of lifts `φ : L ⟶ L'`, the inverse-fiber comparisons `φ.inverseFiberIso p` define a
compatible invertible modification `φ.normalizationInvCompIso` between `L.normalizationInv ≫ φ` and
`φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv`. Taking its inverse supplies the
naturality cells of the strong transformation `normalizationUnitInv actions` from normalization
followed by reconstruction to the identity pseudofunctor on `EquivariantGroupoidLift Γ actions`;
the remaining strong-transformation axioms are automatic because compatible modifications between
parallel lift morphisms form a subsingleton.

Since each component `L.normalizationInv` is an adjoint equivalence in the bicategory of lifts,
`Pseudofunctor.StrongTrans.equivalenceMk` and symmetry of bicategorical equivalences upgrade
`normalizationUnitInv actions` to the unit equivalence
`normalizationUnitEquiv actions :
  Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ≌
    (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions)`.
Together with `normalizationCounitEquiv actions`, this yields `normalizationBiequivalence actions`,
a biequivalence between `EquivariantGroupoidLift Γ actions` and the locally discrete bicategory
`LocallyDiscrete (NormalizedTransport Γ actions)`.

## Main definitions

* `TauCeti.EquivariantGroupoidLift.Hom.normalizationInvCompIso`: pseudonaturality isomorphism of
  `normalizationInv` with respect to a morphism of lifts `φ : L ⟶ L'`;
* `TauCeti.EquivariantGroupoidLift.normalizationUnitInv`,
  `TauCeti.EquivariantGroupoidLift.normalizationUnitHom`: the inverse and forward strong
  transformations comparing the identity pseudofunctor on lifts with normalization followed by
  reconstruction;
* `TauCeti.EquivariantGroupoidLift.normalizationUnitEquiv`: the unit adjoint equivalence of
  pseudofunctors;
* `TauCeti.EquivariantGroupoidLift.normalizationBiequivalence`: the biequivalence between
  `EquivariantGroupoidLift Γ actions` and `LocallyDiscrete (NormalizedTransport Γ actions)`.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Oxford University Press (2021),
  [arXiv:2002.06055](https://arxiv.org/abs/2002.06055): biequivalences, strong transformations, and
  pointwise equivalences in pseudofunctor bicategories.
* Edward Frenkel, *Langlands Correspondence for Loop Groups*, Cambridge Studies in Advanced
  Mathematics 103 (2007): equivariant families of categories over parameter groupoids.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift

open CategoryTheory Bicategory CategoryTheory.Prod Pseudofunctor.StrongTrans

namespace Hom

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  {L L' : EquivariantGroupoidLift Γ actions} (φ : L ⟶ L')

private noncomputable def normalizationInvCompJointAppIso
    (X : LocallyDiscrete (Γ × SingleObj H)) :
    (L.normalizationInv.joint ≫ φ.joint).app X ≅
      (φ.normalizedTransportHom.toLiftHom.joint ≫ L'.normalizationInv.joint).app X :=
  match X with
  | ⟨(p, ⟨⟩)⟩ =>
    Cat.Hom.isoMk (φ.inverseFiberIso p) ≪≫ (λ_ (L'.fiberEquivalence p).inverse.toCatHom).symm

private lemma joint_naturality_factor {p q : Γ} (g : p ⟶ q)
    (a : SingleObj.star H ⟶ SingleObj.star H)
    (hf : (𝟙 p ×ₘ a).toLoc ≫ (g ×ₘ 𝟙 (SingleObj.star H)).toLoc = (g ×ₘ a).toLoc)
    (y : L.jointFiber p) :
    (φ.jointMapIso g).hom.app ((L.jointAct p a).obj y) ≫
        (L'.jointMap g).map ((φ.jointActIso p a).hom.app y) ≫
        (L'.joint.mapComp' (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
          (g ×ₘ a).toLoc hf).inv.toNatTrans.app ((φ.jointFunctor p).obj y) =
      (φ.jointFunctor q).map
          ((L.joint.mapComp' (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
            (g ×ₘ a).toLoc hf).inv.toNatTrans.app y) ≫
        (φ.joint.naturality (g ×ₘ a).toLoc).hom.toNatTrans.app y := by
  have hcomp := φ.joint.naturality_comp'_hom_app
    (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ a).toLoc hf y
  rw [← cancel_epi ((φ.jointFunctor q).map
    ((L.joint.mapComp' (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
      (g ×ₘ a).toLoc hf).hom.toNatTrans.app y))]
  rw [← Functor.map_comp_assoc, Cat.Hom.hom_inv_id_toNatTrans_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  simpa only [jointMapIso_hom_app, jointActIso_hom_app, jointMap, jointAct,
    jointFunctor, Category.assoc, Category.id_comp, Category.comp_id] using hcomp.symm

private lemma normalizationInvComp_naturality {p q : Γ} (g : p ⟶ q)
    (a : SingleObj.star H ⟶ SingleObj.star H) (x : fiber actions p) :
    (φ.inverseFiberIso q).hom.app ((L.normalizedTransport.jointFunctor (g ×ₘ a)).obj x) ≫
        (((φ.normalizedTransportHom.toLiftHom.joint ≫ L'.normalizationInv.joint).naturality
          (g ×ₘ a).toLoc).hom.toNatTrans.app x) =
      (((L.normalizationInv.joint ≫ φ.joint).naturality (g ×ₘ a).toLoc).hom.toNatTrans.app x) ≫
        (L'.joint.map (g ×ₘ a).toLoc).toFunctor.map ((φ.inverseFiberIso p).hom.app x) := by
  have hf : (𝟙 p ×ₘ a).toLoc ≫ (g ×ₘ 𝟙 (SingleObj.star H)).toLoc = (g ×ₘ a).toLoc := by
    apply congrArg Quiver.Hom.toLoc
    exact Prod.ext (Category.id_comp _) (Category.comp_id _)
  let cL' := L'.joint.mapComp' (𝟙 p ×ₘ a).toLoc (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (g ×ₘ a).toLoc hf
  erw [Pseudofunctor.StrongTrans.comp_naturality_hom_app,
    Pseudofunctor.StrongTrans.comp_naturality_hom_app,
    NormalizedTransport.Hom.jointHom_naturality_hom_app]
  -- Display the components over the prescribed fiber and joint-fiber categories so rewriting
  -- does not abstract through the reconstructed lift's dependent object carrier.
  change (φ.inverseFiberIso q).hom.app ((L.transport g).obj ((act actions p a).obj x)) ≫
      ((L'.fiberEquivalence q).inverse.map
          ((φ.normalizedTransportHom.transportIso g).hom.app ((act actions p a).obj x)) ≫
        (L'.normalizationJointIso (g ×ₘ a)).hom.app x) =
    ((φ.jointFunctor q).map ((L.normalizationJointIso (g ×ₘ a)).hom.app x) ≫
        (φ.joint.naturality (g ×ₘ a).toLoc).hom.toNatTrans.app
          ((L.fiberEquivalence p).inverse.obj x)) ≫
      (L'.joint.map (g ×ₘ a).toLoc).toFunctor.map ((φ.inverseFiberIso p).hom.app x)
  simp only [normalizedTransportHom_transportIso, transportIso_hom_app,
    normalizationJointIso_hom_app]
  dsimp only [normalizedTransport, transport_obj, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  -- Cancel the target fiber equivalence with its inverse at `q` via `unitInv_naturality`.
  have hq₁ := (L'.fiberEquivalence q).unitInv_naturality
    ((φ.jointMapIso g).hom.app ((L.fiberEquivalence p).inverse.obj ((act actions p a).obj x)) ≫
      (L'.jointMap g).map ((φ.inverseFiberIso p).hom.app ((act actions p a).obj x)))
  simp only [Functor.map_comp, Category.assoc] at hq₁
  erw [reassoc_of% hq₁, φ.inverseFiberIso_hom_app_comp_unitInv_assoc]
  -- Commute the source inverse-fiber comparison past the prescribed action of `a`.
  rw [← (L'.jointMap g).map_comp_assoc, ← φ.inverseFiberIso_actInverseIso p a x]
  simp only [Functor.map_comp, Category.assoc]
  have hg := (φ.jointMapIso g).hom.naturality ((L.actInverseIso p a).hom.app x)
  dsimp only [Functor.comp_map] at hg
  rw [← reassoc_of% hg]
  -- Move the remaining source comparison across the target compositor `cL'.inv`.
  have hc' := cL'.inv.toNatTrans.naturality ((φ.inverseFiberIso p).hom.app x)
  dsimp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at hc'
  erw [hc', reassoc_of% joint_naturality_factor φ g a hf ((L.fiberEquivalence p).inverse.obj x)]

/-- Applying a morphism of lifts `φ : L ⟶ L'` after `L.normalizationInv` is canonically isomorphic
to applying the reconstructed normalized comparison `φ.normalizedTransportHom.toLiftHom` and then
`L'.normalizationInv`. Its joint components are the inverse-fiber comparisons
`φ.inverseFiberIso p`. -/
noncomputable def normalizationInvCompIso :
    L.normalizationInv ≫ φ ≅ φ.normalizedTransportHom.toLiftHom ≫ L'.normalizationInv :=
  isoMk
    (Pseudofunctor.StrongTrans.isoMk (normalizationInvCompJointAppIso φ) fun {X Y} f ↦ by
      obtain ⟨p, ⟨⟩⟩ := X
      obtain ⟨q, ⟨⟩⟩ := Y
      obtain ⟨g, a⟩ := f
      refine Cat.whiskerLeft_comp_eq_comp_whiskerRight _ _ _ _ fun (x : fiber actions p) ↦ ?_
      have hq : (Cat.Hom.isoMk (φ.inverseFiberIso q) ≪≫
            (λ_ (L'.fiberEquivalence q).inverse.toCatHom).symm).hom.toNatTrans.app
              ((L.normalizedTransport.jointFunctor (g ×ₘ a)).obj x) =
          (φ.inverseFiberIso q).hom.app ((L.normalizedTransport.jointFunctor (g ×ₘ a)).obj x) := by
        simp
      have hp : (Cat.Hom.isoMk (φ.inverseFiberIso p) ≪≫
            (λ_ (L'.fiberEquivalence p).inverse.toCatHom).symm).hom.toNatTrans.app x =
          (φ.inverseFiberIso p).hom.app x := by
        simp
      dsimp only [normalizationInvCompJointAppIso, EquivariantGroupoidLift.comp_joint]
      erw [hq, hp]
      exact normalizationInvComp_naturality φ g a x)
    fun p a ↦ by
      obtain ⟨⟨⟩⟩ := a
      ext x
      change fiber actions p at x
      simp only [EquivariantGroupoidLift.comp_fiberIso, comp_fiberIso_hom_as_app,
        normalizationInv_fiberIso_hom_as_app,
        NormalizedTransport.Hom.toLiftHom_fiberIso_hom_as_app]
      -- Display the component equation in the prescribed fiber category; the associators and
      -- unitors of Cat act as identities on objects.
      change (L'.fiberEquivalence p).functor.map ((φ.inverseFiberIso p).hom.app x ≫ 𝟙 _) ≫
          (𝟙 _ ≫ ((L'.fiberEquivalence p).counit.app x ≫ 𝟙 _)) =
        𝟙 _ ≫
          (((φ.fiberIso p).hom.as.app ⟨SingleObj.star H⟩).toNatTrans.app
            ((L.fiberEquivalence p).inverse.obj x) ≫
            (L.fiberEquivalence p).counit.app x)
      simp only [Category.comp_id, Category.id_comp, ← fiberFunctorIso_hom_app]
      exact φ.functor_map_inverseFiberIso_hom_app_comp_counit p x

@[simp]
lemma normalizationInvCompIso_hom_joint_as_app_star (p : Γ) :
    (normalizationInvCompIso φ).hom.joint.as.app ⟨(p, SingleObj.star H)⟩ =
      (Cat.Hom.isoMk (φ.inverseFiberIso p) ≪≫
        (λ_ (L'.fiberEquivalence p).inverse.toCatHom).symm).hom := by
  simp only [normalizationInvCompIso, isoMk_hom_joint]
  rfl

@[simp]
lemma normalizationInvCompIso_inv_joint_as_app_star (p : Γ) :
    (normalizationInvCompIso φ).inv.joint.as.app ⟨(p, SingleObj.star H)⟩ =
      (Cat.Hom.isoMk (φ.inverseFiberIso p) ≪≫
        (λ_ (L'.fiberEquivalence p).inverse.toCatHom).symm).inv := by
  simp only [normalizationInvCompIso, isoMk_inv_joint]
  rfl

end Hom

section Biequivalence

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  (actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w})

/-- The strong transformation from normalization followed by reconstruction to the identity
pseudofunctor on equivariant lifts, with components `L.normalizationInv` and naturality cells
`(Hom.normalizationInvCompIso φ).symm`. -/
-- Expose the component projections so the unit and counit equations retain their lift endpoints.
@[expose] noncomputable def normalizationUnitInv :
    (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) ⟶
      Pseudofunctor.id (EquivariantGroupoidLift Γ actions) where
  app L := L.normalizationInv
  naturality φ := (Hom.normalizationInvCompIso φ).symm
  naturality_naturality _ := Subsingleton.elim _ _
  naturality_id _ := Subsingleton.elim _ _
  naturality_comp _ _ := Subsingleton.elim _ _

@[simp]
lemma normalizationUnitInv_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitInv actions).app L = L.normalizationInv :=
  (rfl)

@[simp]
lemma normalizationUnitInv_naturality {L L' : EquivariantGroupoidLift Γ actions} (φ : L ⟶ L') :
    (normalizationUnitInv actions).naturality φ = (Hom.normalizationInvCompIso φ).symm :=
  (rfl)

/-- The forward strong transformation from the identity pseudofunctor on equivariant lifts to
normalization followed by reconstruction, with components `L.normalizationInv.equivalence.inv`. -/
-- Expose the underlying transformation so component equations of `normalizationUnitEquiv` hold.
@[expose] noncomputable def normalizationUnitHom :
    Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ⟶
      (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) :=
  ((normalizationUnitInv actions).equivalenceMk
    (fun L ↦ L.normalizationInv.equivalence.inv)
    (fun L ↦ L.normalizationInv.equivalence.unit)
    (fun L ↦ L.normalizationInv.equivalence.counit)
    (fun L ↦ L.normalizationInv.equivalence.left_triangle)).inv

@[simp]
lemma normalizationUnitHom_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitHom actions).app L = L.normalizationInv.equivalence.inv :=
  (rfl)

@[simp]
lemma normalizationUnitHom_naturality {L L' : EquivariantGroupoidLift Γ actions} (φ : L ⟶ L') :
    (normalizationUnitHom actions).naturality φ =
      (L.normalizationInv.equivalence.mateIsoEquiv L'.normalizationInv.equivalence
        (Hom.normalizationInvCompIso φ).symm).symm :=
  (rfl)

/-- The identity pseudofunctor on equivariant lifts is equivalent to normalization followed by
reconstruction, by upgrading `normalizationUnitInv` via the pointwise equivalences
`L.normalizationInv.equivalence` and inverting. -/
-- Expose the record projections so its unit and counit component equations can be stated.
@[expose] noncomputable def normalizationUnitEquiv :
    Pseudofunctor.id (EquivariantGroupoidLift Γ actions) ≌
      (normalizationPseudofunctor actions).comp (reconstructionPseudofunctor actions) :=
  ((normalizationUnitInv actions).equivalenceMk
    (fun L ↦ L.normalizationInv.equivalence.inv)
    (fun L ↦ L.normalizationInv.equivalence.unit)
    (fun L ↦ L.normalizationInv.equivalence.counit)
    (fun L ↦ L.normalizationInv.equivalence.left_triangle)).symm

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
    (normalizationUnitEquiv actions).unit.hom.as.app L =
      L.normalizationInv.equivalence.counit.inv :=
  (rfl)

@[simp]
lemma normalizationUnitEquiv_unit_inv_as_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitEquiv actions).unit.inv.as.app L =
      L.normalizationInv.equivalence.counit.hom :=
  (rfl)

@[simp]
lemma normalizationUnitEquiv_counit_hom_as_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitEquiv actions).counit.hom.as.app L =
      L.normalizationInv.equivalence.unit.inv :=
  Subsingleton.elim _ _

@[simp]
lemma normalizationUnitEquiv_counit_inv_as_app (L : EquivariantGroupoidLift Γ actions) :
    (normalizationUnitEquiv actions).counit.inv.as.app L =
      L.normalizationInv.equivalence.unit.hom :=
  Subsingleton.elim _ _

/-- The biequivalence between the bicategory of equivariant groupoid lifts and the locally discrete
bicategory of normalized transports on the prescribed fibers. -/
-- Expose the projections so the unit and counit equations can refer to `functor` and `inverse`.
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

end TauCeti.EquivariantGroupoidLift
