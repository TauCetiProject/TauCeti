/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Normalized
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Cat
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo

/-!
# Coherence of the normalized transport comparison

Reconstructing a lift from normalized transport inserts the identity action functor and
chosen inverse fiber comparisons. The canonical isomorphisms `toLiftTransportIso` remove
these extra functors. Here we prove that they also preserve the unit and composition
comparisons, so that reconstruction recovers coherent transport rather than just its
individual functors.

The prescribed transports form `transportPseudofunctor`. The strong transformations
`toLiftTransportHom` and `toLiftTransportInv` compare it with the transport pseudofunctor
of the reconstructed lift, and their composites are identities up to invertible modifications.
This compares transport along the parameter category; it does not yet construct a
biequivalence of the bicategories of equivariant lifts and normalized data.

The constructions use `NormalizedTransport.toLift` and its canonical comparison.
The pseudofunctor assembly follows `EquivariantGroupoidLift.transportPseudofunctor`,
and the strong transformations and modifications follow the identity-component constructions
in `CategoryTheory.Pseudofunctor.toEquivariantGroupoidLiftTransportHom` and its inverse.
The coherence conventions are those of Johnson–Yau, *2-Dimensional Categories*, Chapter 4.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift.NormalizedTransport

open CategoryTheory Bicategory CategoryTheory.Prod

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  (N : NormalizedTransport Γ actions)

private lemma toLift_jointMapId_hom_app (p : Γ) (x : fiber actions p) :
    (N.toLift.jointMapId p).hom.app x = (N.jointId (p, SingleObj.star H)).hom.app x := by
  rw [N.toLift.jointMapId_hom_app p x]
  -- Write the identity arrow in the product category explicitly, so its comparison
  -- has the same source and target types as the joint pseudofunctor's unit.
  change (N.joint.mapId'
    (𝟙 (⟨(p, SingleObj.star H)⟩ : LocallyDiscrete (Γ × SingleObj H)))).hom.toNatTrans.app x = _
  rw [Pseudofunctor.mapId'_eq_mapId]
  exact N.joint_mapId_hom_app ⟨(p, SingleObj.star H)⟩ x

/-- Reconstruction followed by normalization preserves the unit comparison of transport. -/
@[reassoc]
lemma toLiftTransportIso_hom_app_comp_transportId (p : Γ) (x : fiber actions p) :
    (N.toLiftTransportIso (𝟙 p)).hom.app x ≫ (N.transportId p).hom.app x =
      (N.toLift.transportId p).hom.app x := by
  have hrhs : (N.toLift.transportId p).hom.app x =
      (N.jointId (p, SingleObj.star H)).hom.app
          ((N.toLift.fiberEquivalence p).inverse.obj x) ≫
        (N.toLift.fiberEquivalence p).counit.app x :=
    (N.toLift.transportId_hom_app p x).trans
      (congrArg (· ≫ (N.toLift.fiberEquivalence p).counit.app x)
        (N.toLift_jointMapId_hom_app p _))
  have key (y : fiber actions p) (ε : y ⟶ x) :
      ((N.transport (𝟙 p)).map ((act actions p (𝟙 _)).map ε) ≫
        (N.transport (𝟙 p)).map ((actId actions p).hom.app x)) ≫
        (N.transportId p).hom.app x =
      (N.jointId (p, SingleObj.star H)).hom.app y ≫ ε := by
    rw [jointId_hom_app]
    simp only [Category.assoc]
    rw [← N.transportId_hom_naturality, ← Functor.map_comp_assoc,
      (actId actions p).hom.naturality]
    simp
  exact (congrArg (· ≫ (N.transportId p).hom.app x)
    (N.toLiftTransportIso_hom_app (𝟙 p) x)).trans
      ((key _ ((N.toLift.fiberEquivalence p).counit.app x)).trans hrhs.symm)

private lemma toLift_jointMapComp_hom_app {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r)
    (gh : p ⟶ r) (hgh : g ≫ h = gh) (x : fiber actions p) :
    (N.toLift.jointMapComp g h gh hgh).hom.app x =
      (N.jointComp (g ×ₘ 𝟙 _) (h ×ₘ 𝟙 _) (gh ×ₘ 𝟙 _) (by simp [hgh])).hom.app x := by
  rw [N.toLift.jointMapComp_hom_app g h gh hgh x]
  -- Expand the flexible compositor only, retaining the opaque joint construction.
  change (N.joint.map₂ (eqToHom (by simp [← Quiver.Hom.comp_toLoc, hgh] :
    (gh ×ₘ 𝟙 (SingleObj.star H)).toLoc =
      (g ×ₘ 𝟙 (SingleObj.star H)).toLoc ≫
        (h ×ₘ 𝟙 (SingleObj.star H)).toLoc))).toNatTrans.app x ≫
    (N.joint.mapComp (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
      (h ×ₘ 𝟙 (SingleObj.star H)).toLoc).hom.toNatTrans.app x = _
  exact N.joint_map₂_comp_mapComp_hom_app
    (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (h ×ₘ 𝟙 (SingleObj.star H)).toLoc
    (gh ×ₘ 𝟙 (SingleObj.star H)).toLoc
    (eqToHom (by simp [← Quiver.Hom.comp_toLoc, hgh])) x

private lemma jointComp_inv_app_comp_actId {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r)
    (gh : p ⟶ r) (hgh : g ≫ h = gh) (x : fiber actions p) :
    (N.jointComp (g ×ₘ 𝟙 _) (h ×ₘ 𝟙 _) (gh ×ₘ 𝟙 _) (by simp [hgh])).inv.app x ≫
        (N.transport gh).map ((actId actions p).hom.app x) =
      (N.transport h).map ((actId actions q).hom.app
          ((N.transport g).obj ((act actions p (𝟙 _)).obj x))) ≫
        (N.transport h).map ((N.transport g).map ((actId actions p).hom.app x)) ≫
          (N.transportComp g h gh hgh).hom.app x := by
  have hu : (actComp actions p (𝟙 _) (𝟙 _) (𝟙 _) (by simp)).inv.app x =
      (actId actions p).hom.app ((act actions p (𝟙 _)).obj x) := by
    rw [← cancel_epi ((actComp actions p (𝟙 _) (𝟙 _) (𝟙 _) (by simp)).hom.app x)]
    simpa using (actComp_right_unitality (actions := actions) p (𝟙 _) (by simp) x).symm
  rw [jointComp_inv_app, hu]
  simp only [Category.assoc]
  rw [← (N.transportComp g h gh hgh).hom.naturality_assoc,
    ← (N.transportComp g h gh hgh).hom.naturality]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc]
  rw [← cancel_epi ((N.transport h).map
    ((N.transportCommIso g (𝟙 _)).hom.app ((act actions p (𝟙 _)).obj x)))]
  simp only [← Functor.map_comp_assoc, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [N.transportCommIso_actId_assoc]
  rfl

private lemma toLift_jointMapComp_inv_app {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r)
    (gh : p ⟶ r) (hgh : g ≫ h = gh) (x : fiber actions p) :
    (N.toLift.jointMapComp g h gh hgh).inv.app x =
      (N.jointComp (g ×ₘ 𝟙 _) (h ×ₘ 𝟙 _) (gh ×ₘ 𝟙 _) (by simp [hgh])).inv.app x :=
  congrArg Iso.inv (Iso.ext (N.toLift_jointMapComp_hom_app g h gh hgh x) :
    (N.toLift.jointMapComp g h gh hgh).app x =
      (N.jointComp (g ×ₘ 𝟙 _) (h ×ₘ 𝟙 _) (gh ×ₘ 𝟙 _) (by simp [hgh])).app x)

/-- Reconstruction followed by normalization preserves composition of transport. -/
@[reassoc]
lemma toLiftTransportIso_transportComp_hom_app {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r)
    (gh : p ⟶ r) (hgh : g ≫ h = gh) (x : fiber actions p) :
    (N.toLift.transportComp g h gh hgh).hom.app x ≫
        (N.toLiftTransportIso gh).hom.app x =
      (N.toLift.transport h).map ((N.toLiftTransportIso g).hom.app x) ≫
        (N.toLiftTransportIso h).hom.app ((N.transport g).obj x) ≫
          (N.transportComp g h gh hgh).hom.app x := by
  have hc : (N.toLift.transportComp g h gh hgh).hom.app x =
      (N.transport h).map ((act actions q (𝟙 _)).map
        ((N.toLift.fiberEquivalence q).counit.app
          ((N.toLift.jointMap g).obj ((N.toLift.fiberEquivalence p).inverse.obj x)))) ≫
        (N.jointComp (g ×ₘ 𝟙 _) (h ×ₘ 𝟙 _) (gh ×ₘ 𝟙 _) (by simp [hgh])).inv.app
          ((N.toLift.fiberEquivalence p).inverse.obj x) := by
    refine (N.toLift.transportComp_hom_app g h gh hgh x).trans ?_
    have he := (N.toLift.fiberEquivalence q).counit_app_functor
      ((N.toLift.jointMap g).obj ((N.toLift.fiberEquivalence p).inverse.obj x))
    rw [Functor.map_comp]
    exact congrArg₂ (fun a b => a ≫ b)
      (congrArg (N.toLift.jointMap h).map he.symm)
      (N.toLift_jointMapComp_inv_app g h gh hgh _)
  have key (y : fiber actions p) (ε : y ⟶ x) :
      (N.jointComp (g ×ₘ 𝟙 _) (h ×ₘ 𝟙 _) (gh ×ₘ 𝟙 _) (by simp [hgh])).inv.app y ≫
          (N.transport gh).map ((act actions p (𝟙 _)).map ε) ≫
            (N.transport gh).map ((actId actions p).hom.app x) =
        (N.transport h).map ((actId actions q).hom.app
            ((N.transport g).obj ((act actions p (𝟙 _)).obj y))) ≫
          (N.transport h).map ((N.transport g).map
            ((act actions p (𝟙 _)).map ε) ≫
              (N.transport g).map ((actId actions p).hom.app x)) ≫
            (N.transportComp g h gh hgh).hom.app x := by
    rw [← Functor.map_comp, (actId actions p).hom.naturality, Functor.map_comp,
      ← Category.assoc, N.jointComp_inv_app_comp_actId g h gh hgh y]
    simp only [Category.assoc]
    rw [← (N.transportComp g h gh hgh).hom.naturality]
    simp only [Functor.comp_map, ← Functor.map_comp, ← Category.assoc]
    rw [← (actId actions p).hom.naturality]
    rfl
  rw [hc, toLiftTransportIso_hom_app]
  -- Work in the actual prescribed fibers: the comparison functors are identities,
  -- while the counits still record their chosen inverses.
  have hk := key ((N.toLift.fiberEquivalence p).inverse.obj x)
    ((N.toLift.fiberEquivalence p).counit.app x)
  have hn : (N.toLift.transport h).map ((N.toLiftTransportIso g).hom.app x) ≫
      (N.toLiftTransportIso h).hom.app ((N.transport g).obj x) =
    (N.toLiftTransportIso h).hom.app ((N.toLift.transport g).obj x) ≫
      (N.transport h).map ((N.toLiftTransportIso g).hom.app x) :=
    (N.toLiftTransportIso h).hom.naturality _
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hk).trans ?_)
  have he := N.toLiftTransportIso_hom_app h ((N.toLift.transport g).obj x)
  have hg := N.toLiftTransportIso_hom_app g x
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg₂ (fun a b => a ≫ b ≫ (N.transportComp g h gh hgh).hom.app x)
      he.symm (congrArg (N.transport h).map hg.symm)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ (N.transportComp g h gh hgh).hom.app x) hn.symm).trans
            (Category.assoc _ _ _))))

/-- The prescribed transport functors, with their given unit and composition cells,
form a pseudofunctor on the parameter category. -/
-- Expose the object assignment so components can be typed in the prescribed fibers.
@[expose] noncomputable def transportPseudofunctor : LocallyDiscrete Γ ⥤ᵖ Cat.{v, w} :=
  LocallyDiscrete.mkCatPseudofunctor (obj := fun p ↦ fiber actions p) N.transport N.transportId
    (fun g h gh hgh ↦ (N.transportComp g h gh hgh).symm)
    (fun f g h fg gh fgh hfg hgh hfgh hfgh' X ↦ by
      simp only [Iso.symm_hom]
      exact LocallyDiscrete.inv_associativity_of_hom_associativity
        (fun g h gh hgh ↦ N.transportComp g h gh hgh)
        (fun f g h fg gh fgh hfg hgh hfgh hfgh' X ↦
          N.transportComp_associativity f g h fg gh fgh hfg hgh hfgh hfgh' X)
        f g h fg gh fgh hfg hgh hfgh hfgh' X)
    (fun g hg X ↦ by
      rw [Iso.symm_hom, ← N.transportComp_left_unitality g hg X, Iso.inv_hom_id_app])
    (fun g hg X ↦ by
      rw [Iso.symm_hom, ← N.transportComp_right_unitality g hg X, Iso.inv_hom_id_app])

@[simp]
lemma transportPseudofunctor_obj (b : LocallyDiscrete Γ) :
    N.transportPseudofunctor.obj b = fiber actions b.as :=
  LocallyDiscrete.mkCatPseudofunctor_obj ..

@[simp]
lemma transportPseudofunctor_map_toFunctor {b b' : LocallyDiscrete Γ} (g : b ⟶ b') :
    (N.transportPseudofunctor.map g).toFunctor = N.transport g.as :=
  LocallyDiscrete.mkCatPseudofunctor_map_toFunctor ..

@[simp]
lemma transportPseudofunctor_mapId_hom_toNatTrans_app (b : LocallyDiscrete Γ)
    (X : fiber actions b.as) :
    (N.transportPseudofunctor.mapId b).hom.toNatTrans.app X = (N.transportId b.as).hom.app X :=
  LocallyDiscrete.mkCatPseudofunctor_mapId_hom_toNatTrans_app ..

@[simp]
lemma transportPseudofunctor_mapId_inv_toNatTrans_app (b : LocallyDiscrete Γ)
    (X : fiber actions b.as) :
    (N.transportPseudofunctor.mapId b).inv.toNatTrans.app X = (N.transportId b.as).inv.app X :=
  LocallyDiscrete.mkCatPseudofunctor_mapId_inv_toNatTrans_app ..

@[simp]
lemma transportPseudofunctor_mapComp_hom_toNatTrans_app {b₀ b₁ b₂ : LocallyDiscrete Γ}
    (g : b₀ ⟶ b₁) (h : b₁ ⟶ b₂) (X : fiber actions b₀.as) :
    (N.transportPseudofunctor.mapComp g h).hom.toNatTrans.app X =
      (N.transportComp g.as h.as (g.as ≫ h.as) rfl).inv.app X :=
  LocallyDiscrete.mkCatPseudofunctor_mapComp_hom_toNatTrans_app ..

@[simp]
lemma transportPseudofunctor_mapComp_inv_toNatTrans_app {b₀ b₁ b₂ : LocallyDiscrete Γ}
    (g : b₀ ⟶ b₁) (h : b₁ ⟶ b₂) (X : fiber actions b₀.as) :
    (N.transportPseudofunctor.mapComp g h).inv.toNatTrans.app X =
      (N.transportComp g.as h.as (g.as ≫ h.as) rfl).hom.app X :=
  LocallyDiscrete.mkCatPseudofunctor_mapComp_inv_toNatTrans_app ..

/-- The canonical return comparison respects the inverse composition cells used by
pseudofunctors. -/
lemma toLiftTransportIso_hom_app_comp_transportComp_inv_app {p q r : Γ}
    (g : p ⟶ q) (h : q ⟶ r) (x : fiber actions p) :
    (N.toLiftTransportIso (g ≫ h)).hom.app x ≫
        (N.transportComp g h (g ≫ h) rfl).inv.app x =
      (N.toLift.transportComp g h (g ≫ h) rfl).inv.app x ≫
        (N.toLiftTransportIso h).hom.app ((N.toLift.transport g).obj x) ≫
          (N.transport h).map ((N.toLiftTransportIso g).hom.app x) := by
  rw [← cancel_epi ((N.toLift.transportComp g h (g ≫ h) rfl).hom.app x)]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [N.toLiftTransportIso_transportComp_hom_app_assoc]
  simp only [Iso.hom_inv_id_app]
  exact (congrArg (_ ≫ ·) (Category.comp_id _)).trans
    ((N.toLiftTransportIso h).hom.naturality _)

/-- Reconstructing a lift recovers the prescribed transport pseudofunctor by a strong
transformation with identity components and canonical return naturality cells. -/
-- Expose the components so the formulas below have the identity functor as endpoint.
@[expose] noncomputable def toLiftTransportHom :
    Pseudofunctor.StrongTrans N.toLift.transportPseudofunctor N.transportPseudofunctor where
  app _ := 𝟙 _
  naturality g := ρ_ _ ≪≫ Cat.Hom.isoMk (N.toLiftTransportIso g.as) ≪≫ (λ_ _).symm
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    rw [Subsingleton.elim η (𝟙 _), PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]
    exact Bicategory.id_whiskerRight_comp_eq_comp_whiskerLeft_id _ _ _ _ _
  naturality_id b :=
    Cat.rightUnitor_trans_leftUnitor_symm_naturality_id _ _ _
      (N.toLiftTransportIso_hom_app_comp_transportId b.as)
  naturality_comp g h :=
    Cat.rightUnitor_trans_leftUnitor_symm_naturality_comp _ _ _ _ _
      (N.toLiftTransportIso_hom_app_comp_transportComp_inv_app g.as h.as)

@[simp]
lemma toLiftTransportHom_app (b : LocallyDiscrete Γ) :
    N.toLiftTransportHom.app b = 𝟙 (fiber actions b.as) :=
  (rfl)

@[simp]
lemma toLiftTransportHom_naturality_hom_app {p q : LocallyDiscrete Γ} (g : p ⟶ q)
    (x : fiber actions p.as) :
    (N.toLiftTransportHom.naturality g).hom.toNatTrans.app x =
      (N.toLiftTransportIso g.as).hom.app x :=
  Cat.rightUnitor_trans_leftUnitor_symm_hom_app _ _

@[simp]
lemma toLiftTransportHom_naturality_inv_app {p q : LocallyDiscrete Γ} (g : p ⟶ q)
    (x : fiber actions p.as) :
    (N.toLiftTransportHom.naturality g).inv.toNatTrans.app x =
      (N.toLiftTransportIso g.as).inv.app x :=
  Cat.rightUnitor_trans_leftUnitor_symm_inv_app _ _

private lemma toLiftTransportIso_inv_app_comp_transportComp_inv_app {p q r : Γ}
    (g : p ⟶ q) (h : q ⟶ r) (x : fiber actions p) :
    (N.toLiftTransportIso (g ≫ h)).inv.app x ≫
        (N.toLift.transportComp g h (g ≫ h) rfl).inv.app x =
      (N.transportComp g h (g ≫ h) rfl).inv.app x ≫
        (N.toLiftTransportIso h).inv.app ((N.transport g).obj x) ≫
          (N.toLift.transport h).map ((N.toLiftTransportIso g).inv.app x) := by
  rw [← cancel_epi ((N.toLiftTransportIso (g ≫ h)).hom.app x),
    Iso.hom_inv_id_app_assoc, ← Category.assoc,
    N.toLiftTransportIso_hom_app_comp_transportComp_inv_app]
  simp only [Category.assoc]
  rw [← (N.toLiftTransportIso h).hom.naturality_assoc,
    Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  exact ((congrArg (_ ≫ ·) ((N.toLift.transport h).map_id _)).trans
    (Category.comp_id _)).symm

/-- The inverse strong return comparison, with the inverse canonical naturality cells. -/
-- Expose the identity components so the naturality formulas can be stated on actual objects.
@[expose] noncomputable def toLiftTransportInv :
    Pseudofunctor.StrongTrans N.transportPseudofunctor N.toLift.transportPseudofunctor where
  app _ := 𝟙 _
  naturality g := ρ_ _ ≪≫ Cat.Hom.isoMk (N.toLiftTransportIso g.as).symm ≪≫ (λ_ _).symm
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    rw [Subsingleton.elim η (𝟙 _), PrelaxFunctor.map₂_id, PrelaxFunctor.map₂_id]
    exact Bicategory.id_whiskerRight_comp_eq_comp_whiskerLeft_id _ _ _ _ _
  naturality_id b :=
    Cat.rightUnitor_trans_leftUnitor_symm_naturality_id _ _ _ fun x ↦
      (Iso.inv_comp_eq ((N.toLiftTransportIso (𝟙 b.as)).app x)).2
        (N.toLiftTransportIso_hom_app_comp_transportId b.as x).symm
  naturality_comp g h := by
    exact Cat.rightUnitor_trans_leftUnitor_symm_naturality_comp _ _ _ _ _
      (toLiftTransportIso_inv_app_comp_transportComp_inv_app N g.as h.as)

@[simp]
lemma toLiftTransportInv_app (b : LocallyDiscrete Γ) :
    N.toLiftTransportInv.app b = 𝟙 (fiber actions b.as) :=
  (rfl)

@[simp]
lemma toLiftTransportInv_naturality_hom_app {p q : LocallyDiscrete Γ} (g : p ⟶ q)
    (x : fiber actions p.as) :
    (N.toLiftTransportInv.naturality g).hom.toNatTrans.app x =
      (N.toLiftTransportIso g.as).inv.app x :=
  Cat.rightUnitor_trans_leftUnitor_symm_hom_app _ _

@[simp]
lemma toLiftTransportInv_naturality_inv_app {p q : LocallyDiscrete Γ} (g : p ⟶ q)
    (x : fiber actions p.as) :
    (N.toLiftTransportInv.naturality g).inv.toNatTrans.app x =
      (N.toLiftTransportIso g.as).hom.app x :=
  Cat.rightUnitor_trans_leftUnitor_symm_inv_app _ _

open Pseudofunctor.StrongTrans

/-- The forward return comparison followed by its inverse is the identity, up to the
invertible modification with unitor components. -/
noncomputable def toLiftTransportHomInvIso :
    N.toLiftTransportHom ≫ N.toLiftTransportInv ≅ 𝟙 N.toLift.transportPseudofunctor :=
  isoMk (fun _ ↦ λ_ _) fun g ↦ by
    simp only [categoryStruct_comp_naturality_hom, categoryStruct_id_naturality_hom]
    exact Cat.rightUnitor_trans_leftUnitor_symm_comp_modification _ _ fun x ↦
      Iso.hom_inv_id_app _ x

/-- The inverse return comparison followed by the forward comparison is the identity,
up to the invertible modification with unitor components. -/
noncomputable def toLiftTransportInvHomIso :
    N.toLiftTransportInv ≫ N.toLiftTransportHom ≅ 𝟙 N.transportPseudofunctor :=
  isoMk (fun _ ↦ λ_ _) fun g ↦ by
    simp only [categoryStruct_comp_naturality_hom, categoryStruct_id_naturality_hom]
    exact Cat.rightUnitor_trans_leftUnitor_symm_comp_modification _ _ fun x ↦
      Iso.inv_hom_id_app _ x

@[simp]
lemma toLiftTransportHomInvIso_hom_as_app (b : LocallyDiscrete Γ) :
    N.toLiftTransportHomInvIso.hom.as.app b = (λ_ (𝟙 (fiber actions b.as))).hom :=
  (rfl)

@[simp]
lemma toLiftTransportHomInvIso_inv_as_app (b : LocallyDiscrete Γ) :
    N.toLiftTransportHomInvIso.inv.as.app b = (λ_ (𝟙 (fiber actions b.as))).inv :=
  (rfl)

@[simp]
lemma toLiftTransportInvHomIso_hom_as_app (b : LocallyDiscrete Γ) :
    N.toLiftTransportInvHomIso.hom.as.app b = (λ_ (𝟙 (fiber actions b.as))).hom :=
  (rfl)

@[simp]
lemma toLiftTransportInvHomIso_inv_as_app (b : LocallyDiscrete Γ) :
    N.toLiftTransportInvHomIso.inv.as.app b = (λ_ (𝟙 (fiber actions b.as))).inv :=
  (rfl)

end TauCeti.EquivariantGroupoidLift.NormalizedTransport
