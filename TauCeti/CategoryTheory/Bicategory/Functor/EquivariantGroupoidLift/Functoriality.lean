/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Transport

/-!
# Functoriality of normalized transport comparisons

A morphism of equivariant lifts gives a coherent comparison of transport on the prescribed
fibers. These comparisons respect identity and composition of lift morphisms, and compatible
modifications induce the identity modification on the prescribed fibers. Thus normalization
acts on the categories of morphisms, retaining the chosen fiber comparisons and their mates.

We use `Hom.transportIso` and `Hom.transportHom`, rather than choosing new transport cells.
The mate equation `Hom.functor_map_inverseFiberIso_hom_app_comp_counit` controls the chosen
inverses of the fiber equivalences.

## References

* Niles Johnson and Donald Yau, *2-Dimensional Categories*, Chapter 4: strong transformations
  and modifications.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift.Hom

open CategoryTheory Bicategory CategoryTheory.Prod Pseudofunctor.StrongTrans

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  {L L' L'' : EquivariantGroupoidLift Γ actions}

lemma id_fiberFunctorIso_hom_app (L : EquivariantGroupoidLift Γ actions) (p : Γ)
    (Y : L.jointFiber p) :
    ((id L).fiberFunctorIso p).hom.app Y = 𝟙 _ := by
  rw [fiberFunctorIso_hom_app, id_fiberIso_hom_as_app]
  rfl

lemma id_fiberFunctorIso_inv_app (L : EquivariantGroupoidLift Γ actions) (p : Γ)
    (Y : L.jointFiber p) :
    ((id L).fiberFunctorIso p).inv.app Y = 𝟙 _ := by
  rw [fiberFunctorIso_inv_app, id_fiberIso_inv_as_app]
  rfl

lemma comp_fiberFunctorIso_hom_app (φ : L.Hom L') (ψ : L'.Hom L'') (p : Γ)
    (Y : L.jointFiber p) :
    ((φ.comp ψ).fiberFunctorIso p).hom.app Y =
      (ψ.fiberFunctorIso p).hom.app ((φ.jointFunctor p).obj Y) ≫
        (φ.fiberFunctorIso p).hom.app Y := by
  rw [fiberFunctorIso_hom_app, comp_fiberIso_hom_as_app]
  -- The composite joint functor is definitionally the composite of the two components.
  erw [Cat.Hom₂.comp_app, Cat.associator_hom_app, eqToHom_refl, Category.id_comp,
    Cat.Hom₂.comp_app, Cat.whiskerLeft_app]
  rw [fiberFunctorIso_hom_app, fiberFunctorIso_hom_app]
  rfl

lemma comp_fiberFunctorIso_inv_app (φ : L.Hom L') (ψ : L'.Hom L'') (p : Γ)
    (Y : L.jointFiber p) :
    ((φ.comp ψ).fiberFunctorIso p).inv.app Y =
      (φ.fiberFunctorIso p).inv.app Y ≫
        (ψ.fiberFunctorIso p).inv.app ((φ.jointFunctor p).obj Y) := by
  rw [fiberFunctorIso_inv_app, comp_fiberIso_inv_as_app]
  -- Evaluate the composite at the underlying joint-fiber object.
  erw [Cat.Hom₂.comp_app, Cat.Hom₂.comp_app, Cat.associator_inv_app,
    eqToHom_refl, Category.comp_id, Cat.whiskerLeft_app]
  rw [fiberFunctorIso_inv_app, fiberFunctorIso_inv_app]
  rfl

lemma id_jointMapIso_hom_app (L : EquivariantGroupoidLift Γ actions) {p q : Γ}
    (g : p ⟶ q) (Y : L.jointFiber p) :
    ((id L).jointMapIso g).hom.app Y = 𝟙 _ := by
  rw [jointMapIso_hom_app]
  -- The identity lift's joint component is the native identity transformation.
  erw [categoryStruct_id_naturality_hom, Cat.Hom₂.comp_app,
    Cat.rightUnitor_hom_app]
  erw [eqToHom_refl, Category.id_comp]
  rfl

lemma comp_jointMapIso_hom_app (φ : L.Hom L') (ψ : L'.Hom L'') {p q : Γ}
    (g : p ⟶ q) (Y : L.jointFiber p) :
    ((φ.comp ψ).jointMapIso g).hom.app Y =
      (ψ.jointFunctor q).map ((φ.jointMapIso g).hom.app Y) ≫
        (ψ.jointMapIso g).hom.app ((φ.jointFunctor p).obj Y) := by
  rw [jointMapIso_hom_app]
  -- Evaluate the native composite strong transformation at the joint-fiber object.
  erw [categoryStruct_comp_naturality_hom, Cat.Hom₂.comp_app, Cat.associator_inv_app,
    eqToHom_refl, Cat.Hom₂.comp_app, Cat.Hom₂.comp_app, Cat.associator_hom_app,
    eqToHom_refl, Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]
  rw [jointMapIso_hom_app, jointMapIso_hom_app]
  rfl

/-- The mate of the identity fiber comparison is the identity, even with arbitrary chosen
quasi-inverses for the fiber equivalences. -/
@[simp]
lemma id_inverseFiberIso_hom_app (L : EquivariantGroupoidLift Γ actions) (p : Γ)
    (X : fiber actions p) :
    ((id L).inverseFiberIso p).hom.app X = 𝟙 _ := by
  apply (L.fiberEquivalence p).functor.map_injective
  apply (cancel_mono ((L.fiberEquivalence p).counit.app X)).mp
  rw [functor_map_inverseFiberIso_hom_app_comp_counit, id_fiberFunctorIso_hom_app]
  -- The identity joint functor has identity object and morphism maps.
  erw [CategoryTheory.Functor.map_id]
  erw [Category.id_comp]

/-- Taking mates respects composition of the specified fiber comparisons. -/
@[simp, reassoc]
lemma comp_inverseFiberIso_hom_app (φ : L.Hom L') (ψ : L'.Hom L'') (p : Γ)
    (X : fiber actions p) :
    ((φ.comp ψ).inverseFiberIso p).hom.app X =
      (ψ.jointFunctor p).map ((φ.inverseFiberIso p).hom.app X) ≫
        (ψ.inverseFiberIso p).hom.app X := by
  apply (L''.fiberEquivalence p).functor.map_injective
  apply (cancel_mono ((L''.fiberEquivalence p).counit.app X)).mp
  -- Reduce the composite joint functor in the endpoints before rewriting its mate.
  erw [Functor.map_comp, Category.assoc,
    functor_map_inverseFiberIso_hom_app_comp_counit,
    functor_map_inverseFiberIso_hom_app_comp_counit, comp_fiberFunctorIso_hom_app]
  erw [(ψ.fiberFunctorIso p).hom.naturality_assoc]
  erw [Category.assoc, φ.functor_map_inverseFiberIso_hom_app_comp_counit]
  rfl

/-- Normalizing the identity morphism gives the identity comparison on every transport functor. -/
@[simp]
lemma id_transportIso (L : EquivariantGroupoidLift Γ actions) {p q : Γ} (g : p ⟶ q) :
    (id L).transportIso g = Iso.refl (L.transport g) := by
  ext X
  simp only [transportIso_hom_app, id_fiberFunctorIso_inv_app, id_jointMapIso_hom_app,
    id_inverseFiberIso_hom_app]
  -- The identity joint functor disappears from the endpoints of these maps.
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

/-- Normalization preserves composition of lift morphisms on the actual transport cells. -/
@[simp]
lemma comp_transportIso (φ : L.Hom L') (ψ : L'.Hom L'') {p q : Γ} (g : p ⟶ q) :
    (φ.comp ψ).transportIso g = φ.transportIso g ≪≫ ψ.transportIso g := by
  ext X
  simp only [transportIso_hom_app, comp_fiberFunctorIso_inv_app,
    comp_jointMapIso_hom_app, comp_inverseFiberIso_hom_app,
    Iso.trans_hom, NatTrans.comp_app]
  -- Reduce the composite joint functor in the types of the expanded components.
  erw [Functor.map_comp, Category.assoc, Functor.map_comp, Functor.map_comp, Category.assoc]
  erw [← (ψ.fiberFunctorIso q).inv.naturality_assoc]
  erw [← Functor.map_comp_assoc]
  erw [← (ψ.jointMapIso g).hom.naturality]
  erw [Functor.map_comp, Category.assoc, ← (ψ.fiberFunctorIso q).inv.naturality_assoc]
  erw [Category.assoc, Category.assoc]
  rfl

namespace Hom₂

variable {φ ψ : L.Hom L'} (Θ : φ ⟶ ψ)

/-- Compatibility of a modification with the prescribed fiber comparison, on objects. -/
@[reassoc]
lemma map_app_comp_fiberFunctorIso_hom_app (p : Γ) (Y : L.jointFiber p) :
    (L'.fiberEquivalence p).functor.map
        ((Θ.joint.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.app Y) ≫
      (ψ.fiberFunctorIso p).hom.app Y = (φ.fiberFunctorIso p).hom.app Y := by
  have h := congrArg (fun m => m.toNatTrans.app Y) (Θ.comm p ⟨SingleObj.star H⟩)
  -- Evaluate the whiskering in the joint fiber before using its prescribed presentation.
  erw [Cat.Hom₂.comp_app, Cat.whiskerRight_app] at h
  rw [fiberFunctorIso_hom_app, fiberFunctorIso_hom_app]
  -- Conversion identifies the Cat composite with its underlying composite functor.
  convert! h using 1

/-- Naturality of the joint modification along a parameter arrow, on objects. -/
@[reassoc]
lemma app_comp_jointMapIso_hom_app {p q : Γ} (g : p ⟶ q) (Y : L.jointFiber p) :
    (Θ.joint.as.app ⟨(q, SingleObj.star H)⟩).toNatTrans.app ((L.jointMap g).obj Y) ≫
        (ψ.jointMapIso g).hom.app Y =
      (φ.jointMapIso g).hom.app Y ≫ (L'.jointMap g).map
        ((Θ.joint.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.app Y) := by
  have h := congrArg (fun m => m.toNatTrans.app Y)
    (Θ.joint.as.naturality (g ×ₘ 𝟙 (SingleObj.star H)).toLoc)
  -- These whiskerings take place in Cat; their components are the underlying natural maps.
  erw [Cat.Hom₂.comp_app, Cat.Hom₂.comp_app, Cat.whiskerLeft_app,
    Cat.whiskerRight_app] at h
  simpa only [jointMapIso_hom_app] using h

/-- The comparison of chosen inverse fibers is compatible with a modification. -/
@[reassoc]
lemma app_comp_inverseFiberIso_hom_app (p : Γ) (X : fiber actions p) :
    (Θ.joint.as.app ⟨(p, SingleObj.star H)⟩).toNatTrans.app
        ((L.fiberEquivalence p).inverse.obj X) ≫ (ψ.inverseFiberIso p).hom.app X =
      (φ.inverseFiberIso p).hom.app X := by
  apply (L'.fiberEquivalence p).functor.map_injective
  apply (cancel_mono ((L'.fiberEquivalence p).counit.app X)).mp
  rw [Functor.map_comp, Category.assoc,
    functor_map_inverseFiberIso_hom_app_comp_counit,
    functor_map_inverseFiberIso_hom_app_comp_counit,
    Θ.map_app_comp_fiberFunctorIso_hom_app_assoc]

include Θ in
/-- Compatible modifications give the same normalized comparison on each transport functor.
This does not identify the original joint transformations. -/
lemma transportIso_eq {p q : Γ} (g : p ⟶ q) : φ.transportIso g = ψ.transportIso g := by
  ext X
  have hf (Y : L.jointFiber q) :
      (φ.fiberFunctorIso q).inv.app Y ≫
        (L'.fiberEquivalence q).functor.map
          ((Θ.joint.as.app ⟨(q, SingleObj.star H)⟩).toNatTrans.app Y) =
        (ψ.fiberFunctorIso q).inv.app Y := by
    exact (Iso.inv_comp_eq ((φ.fiberFunctorIso q).app Y)).mpr
      ((Iso.eq_comp_inv ((ψ.fiberFunctorIso q).app Y)).mpr
        (Θ.map_app_comp_fiberFunctorIso_hom_app q Y))
  simp only [transportIso_hom_app]
  rw [← Θ.app_comp_inverseFiberIso_hom_app]
  simp only [Functor.map_comp]
  erw [← Functor.map_comp_assoc, ← Θ.app_comp_jointMapIso_hom_app,
    Functor.map_comp, ← Category.assoc, ← Category.assoc, hf]
  exact Category.assoc _ _ _

include Θ in
/-- Compatible modifications identify the coherent transport transformations strictly:
their components are identities and their naturality cells coincide. -/
lemma transportHom_eq : φ.transportHom = ψ.transportHom := by
  unfold transportHom
  congr 1
  funext p q g
  rw [Θ.transportIso_eq g.as]

end Hom₂

/-- Normalization on a category of morphisms of lifts. A compatible modification is sent to
the identity-component modification between the induced coherent transport comparisons. -/
-- Expose the object assignment so modification components have the prescribed endpoints.
@[expose, simps obj map]
noncomputable def transportFunctor (L L' : EquivariantGroupoidLift Γ actions) :
    L.Hom L' ⥤ (L.transportPseudofunctor ⟶ L'.transportPseudofunctor) where
  obj φ := φ.transportHom
  map Θ := eqToHom Θ.transportHom_eq
  map_id φ := by simp
  map_comp Θ Ξ := by simp

end TauCeti.EquivariantGroupoidLift.Hom
