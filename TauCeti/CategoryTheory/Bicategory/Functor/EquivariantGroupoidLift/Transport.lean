/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Hom
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Cat

/-!
# Coherent comparison of transport under morphisms of lifts

A morphism of equivariant groupoid lifts identifies their transport functors on the
prescribed fibers. These identifications preserve the units and compositors, so they
assemble into a strong transformation of the transport pseudofunctors, with identity
components on the prescribed categories. The inverse cells give an inverse strong
transformation, with invertible modifications comparing both composites to identities.

The comparison is the existing `EquivariantGroupoidLift.Hom.transportIso`, constructed
from the joint strong transformation and its prescribed-fiber isomorphisms. The
identity-component assembly follows `NormalizedTransport.toLiftTransportHom` and its inverse
in `EquivariantGroupoidLift.Comparison`. The coherence conventions are those of
Johnson–Yau, *2-Dimensional Categories*, Chapter 4.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift.Hom

open CategoryTheory Bicategory

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  {L L' : EquivariantGroupoidLift Γ actions} (φ : L.Hom L')

private lemma inverseFiberIso_hom_app_comp_map_unitInv (p : Γ) (Y : L.jointFiber p)
    {Z : L'.jointFiber p} (f : (φ.jointFunctor p).obj Y ⟶ Z) :
    (φ.inverseFiberIso p).hom.app ((L.fiberEquivalence p).functor.obj Y) ≫
        (L'.fiberEquivalence p).inverse.map ((φ.fiberFunctorIso p).inv.app Y ≫
          (L'.fiberEquivalence p).functor.map f) ≫
            (L'.fiberEquivalence p).unitInv.app Z =
      (φ.jointFunctor p).map ((L.fiberEquivalence p).unitInv.app Y) ≫ f := by
  simp only [Functor.map_comp, Category.assoc]
  erw [(L'.fiberEquivalence p).unitInv_naturality,
    φ.inverseFiberIso_hom_app_comp_unitInv_assoc]

/-- A morphism of lifts preserves the unit of transport on the prescribed fiber. -/
@[reassoc]
lemma transportIso_hom_app_comp_transportId (p : Γ) (X : fiber actions p) :
    (φ.transportIso (𝟙 p)).hom.app X ≫ (L'.transportId p).hom.app X =
      (L.transportId p).hom.app X := by
  dsimp only [EquivariantGroupoidLift.transport, Functor.comp_obj]
  erw [transportIso_hom_app, EquivariantGroupoidLift.transportId_hom_app,
    EquivariantGroupoidLift.transportId_hom_app]
  simp only [Category.assoc]
  simp only [← Functor.map_comp_assoc]
  erw [(L'.jointMapId p).hom.naturality,
    φ.jointMapIso_hom_app_comp_jointMapId_assoc]
  simp only [Functor.map_comp, Category.assoc]
  erw [φ.functor_map_inverseFiberIso_hom_app_comp_counit,
    ← (φ.fiberFunctorIso p).inv.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc]

/-- A morphism of lifts preserves composition of transport on the prescribed fibers. -/
@[reassoc]
lemma transportIso_transportComp_hom_app {p q r : Γ} (g : p ⟶ q) (h : q ⟶ r)
    (gh : p ⟶ r) (hgh : g ≫ h = gh) (X : fiber actions p) :
    (L.transportComp g h gh hgh).hom.app X ≫ (φ.transportIso gh).hom.app X =
      (φ.transportIso h).hom.app ((L.transport g).obj X) ≫
        (L'.transport h).map ((φ.transportIso g).hom.app X) ≫
          (L'.transportComp g h gh hgh).hom.app X := by
  simp only [transportIso_hom_app, EquivariantGroupoidLift.transportComp_hom_app,
    EquivariantGroupoidLift.transport_map, EquivariantGroupoidLift.transport_obj,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
  -- Cancel the inverse fiber comparison at the intermediate parameter.
  erw [φ.inverseFiberIso_hom_app_comp_map_unitInv]
  simp only [Functor.map_comp (L'.jointMap h), Category.assoc]
  erw [← (φ.jointMapIso h).hom.naturality_assoc,
    (L'.jointMapComp g h gh hgh).inv.naturality]
  simp only [Functor.comp_map]
  -- The remaining joint cells satisfy the original strong-transformation coherence.
  erw [φ.jointMapIso_comp_inv_app_assoc]
  simp only [← Functor.map_comp_assoc]
  simp only [Functor.map_comp, Category.assoc]
  -- Move the comparison back through the prescribed target fiber.
  erw [← (φ.fiberFunctorIso r).inv.naturality_assoc,
    ← (φ.fiberFunctorIso r).inv.naturality_assoc]
  exact Category.assoc _ _ _

/-- Compatibility with the inverse compositors used by transport pseudofunctors. -/
@[reassoc]
lemma transportIso_hom_app_comp_transportComp_inv_app {p q r : Γ}
    (g : p ⟶ q) (h : q ⟶ r) (X : fiber actions p) :
    (φ.transportIso (g ≫ h)).hom.app X ≫
        (L'.transportComp g h (g ≫ h) rfl).inv.app X =
      (L.transportComp g h (g ≫ h) rfl).inv.app X ≫
        (φ.transportIso h).hom.app ((L.transport g).obj X) ≫
          (L'.transport h).map ((φ.transportIso g).hom.app X) := by
  rw [← cancel_epi ((L.transportComp g h (g ≫ h) rfl).hom.app X)]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [φ.transportIso_transportComp_hom_app_assoc]
  simp only [Iso.hom_inv_id_app]
  exact congrArg (_ ≫ ·) (Category.comp_id _)

/-- A morphism of lifts gives a coherent comparison of transport on the prescribed fibers.
Its components are identity functors and its naturality cells are the canonical transport
isomorphisms, with the native unitors inserted. -/
-- Expose the identity components so their naturality formulas have the prescribed endpoints.
@[expose] noncomputable def transportHom :
    Pseudofunctor.StrongTrans L.transportPseudofunctor L'.transportPseudofunctor where
  app _ := 𝟙 _
  naturality g := ρ_ _ ≪≫ Cat.Hom.isoMk (φ.transportIso g.as) ≪≫ (λ_ _).symm
  naturality_naturality η :=
    Pseudofunctor.naturality_naturality_of_locallyDiscrete
      L.transportPseudofunctor L'.transportPseudofunctor (fun _ ↦ 𝟙 _)
      (fun g ↦ ρ_ _ ≪≫ Cat.Hom.isoMk (φ.transportIso g.as) ≪≫ (λ_ _).symm) η
  naturality_id b :=
    Cat.rightUnitor_trans_leftUnitor_symm_naturality_id _ _ _
      (φ.transportIso_hom_app_comp_transportId b.as)
  naturality_comp g h :=
    Cat.rightUnitor_trans_leftUnitor_symm_naturality_comp _ _ _ _ _
      (φ.transportIso_hom_app_comp_transportComp_inv_app g.as h.as)

@[simp]
lemma transportHom_app (b : LocallyDiscrete Γ) :
    φ.transportHom.app b = 𝟙 (fiber actions b.as) :=
  (rfl)

@[simp]
lemma transportHom_naturality_hom_app {p q : LocallyDiscrete Γ} (g : p ⟶ q)
    (X : fiber actions p.as) :
    (φ.transportHom.naturality g).hom.toNatTrans.app X = (φ.transportIso g.as).hom.app X :=
  Cat.rightUnitor_trans_leftUnitor_symm_hom_app _ _

@[simp]
lemma transportHom_naturality_inv_app {p q : LocallyDiscrete Γ} (g : p ⟶ q)
    (X : fiber actions p.as) :
    (φ.transportHom.naturality g).inv.toNatTrans.app X = (φ.transportIso g.as).inv.app X :=
  Cat.rightUnitor_trans_leftUnitor_symm_inv_app _ _

/-- The inverse transport isomorphisms respect the inverse compositors. -/
lemma transportIso_inv_app_comp_transportComp_inv_app {p q r : Γ}
    (g : p ⟶ q) (h : q ⟶ r) (X : fiber actions p) :
    (φ.transportIso (g ≫ h)).inv.app X ≫
        (L.transportComp g h (g ≫ h) rfl).inv.app X =
      (L'.transportComp g h (g ≫ h) rfl).inv.app X ≫
        (φ.transportIso h).inv.app ((L'.transport g).obj X) ≫
          (L.transport h).map ((φ.transportIso g).inv.app X) := by
  rw [← cancel_epi ((φ.transportIso (g ≫ h)).hom.app X),
    Iso.hom_inv_id_app_assoc, ← Category.assoc,
    φ.transportIso_hom_app_comp_transportComp_inv_app]
  simp only [Category.assoc]
  rw [← (φ.transportIso h).hom.naturality_assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp, Iso.hom_inv_id_app]
  exact ((congrArg (_ ≫ ·) ((L.transport h).map_id _)).trans (Category.comp_id _)).symm

/-- The inverse coherent transport comparison, with inverse canonical naturality cells. -/
-- Expose the identity components for the component equations below.
@[expose] noncomputable def transportInv :
    Pseudofunctor.StrongTrans L'.transportPseudofunctor L.transportPseudofunctor where
  app _ := 𝟙 _
  naturality g := ρ_ _ ≪≫ Cat.Hom.isoMk (φ.transportIso g.as).symm ≪≫ (λ_ _).symm
  naturality_naturality η :=
    Pseudofunctor.naturality_naturality_of_locallyDiscrete
      L'.transportPseudofunctor L.transportPseudofunctor (fun _ ↦ 𝟙 _)
      (fun g ↦ ρ_ _ ≪≫ Cat.Hom.isoMk (φ.transportIso g.as).symm ≪≫ (λ_ _).symm) η
  naturality_id b :=
    Cat.rightUnitor_trans_leftUnitor_symm_naturality_id _ _ _ fun X ↦
      (Iso.inv_comp_eq ((φ.transportIso (𝟙 b.as)).app X)).2
        (φ.transportIso_hom_app_comp_transportId b.as X).symm
  naturality_comp g h :=
    Cat.rightUnitor_trans_leftUnitor_symm_naturality_comp _ _ _ _ _
      (φ.transportIso_inv_app_comp_transportComp_inv_app g.as h.as)

@[simp]
lemma transportInv_app (b : LocallyDiscrete Γ) :
    φ.transportInv.app b = 𝟙 (fiber actions b.as) :=
  (rfl)

@[simp]
lemma transportInv_naturality_hom_app {p q : LocallyDiscrete Γ} (g : p ⟶ q)
    (X : fiber actions p.as) :
    (φ.transportInv.naturality g).hom.toNatTrans.app X = (φ.transportIso g.as).inv.app X :=
  Cat.rightUnitor_trans_leftUnitor_symm_hom_app _ _

@[simp]
lemma transportInv_naturality_inv_app {p q : LocallyDiscrete Γ} (g : p ⟶ q)
    (X : fiber actions p.as) :
    (φ.transportInv.naturality g).inv.toNatTrans.app X = (φ.transportIso g.as).hom.app X :=
  Cat.rightUnitor_trans_leftUnitor_symm_inv_app _ _

open Pseudofunctor.StrongTrans

/-- The forward comparison followed by its inverse is the identity up to an invertible
modification with unitor components. -/
noncomputable def transportHomInvIso :
    φ.transportHom ≫ φ.transportInv ≅ 𝟙 L.transportPseudofunctor :=
  Pseudofunctor.StrongTrans.isoMk (fun _ ↦ λ_ _) fun g ↦ by
    simp only [categoryStruct_comp_naturality_hom, categoryStruct_id_naturality_hom]
    exact Cat.rightUnitor_trans_leftUnitor_symm_comp_modification _ _ fun X ↦
      Iso.hom_inv_id_app _ X

/-- The inverse comparison followed by the forward comparison is the identity up to an
invertible modification with unitor components. -/
noncomputable def transportInvHomIso :
    φ.transportInv ≫ φ.transportHom ≅ 𝟙 L'.transportPseudofunctor :=
  Pseudofunctor.StrongTrans.isoMk (fun _ ↦ λ_ _) fun g ↦ by
    simp only [categoryStruct_comp_naturality_hom, categoryStruct_id_naturality_hom]
    exact Cat.rightUnitor_trans_leftUnitor_symm_comp_modification _ _ fun X ↦
      Iso.inv_hom_id_app _ X

@[simp]
lemma transportHomInvIso_hom_as_app (b : LocallyDiscrete Γ) :
    φ.transportHomInvIso.hom.as.app b = (λ_ (𝟙 (fiber actions b.as))).hom :=
  (rfl)

@[simp]
lemma transportHomInvIso_inv_as_app (b : LocallyDiscrete Γ) :
    φ.transportHomInvIso.inv.as.app b = (λ_ (𝟙 (fiber actions b.as))).inv :=
  (rfl)

@[simp]
lemma transportInvHomIso_hom_as_app (b : LocallyDiscrete Γ) :
    φ.transportInvHomIso.hom.as.app b = (λ_ (𝟙 (fiber actions b.as))).hom :=
  (rfl)

@[simp]
lemma transportInvHomIso_inv_as_app (b : LocallyDiscrete Γ) :
    φ.transportInvHomIso.inv.as.app b = (λ_ (𝟙 (fiber actions b.as))).inv :=
  (rfl)

end TauCeti.EquivariantGroupoidLift.Hom
