/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.EquivariantGroupoidLift.Hom

/-!
# Equivariance of transport comparisons

A morphism of equivariant lifts compares their transport functors on the prescribed
categories. This comparison commutes with the prescribed actions. The mixed square comes
from naturality of the joint strong transformation on the commuting square in the product
category, and from compatibility of its fiber isomorphisms with the actions.

The joint square uses `Pseudofunctor.StrongTrans.naturality_isoMapOfCommSq`; the coherence
conventions are those of Johnson–Yau, *2-Dimensional Categories*, Chapter 4.
-/

public section

universe w v u₂ v₁ u₁

namespace TauCeti.EquivariantGroupoidLift.Hom

open CategoryTheory Bicategory CategoryTheory.Prod Pseudofunctor.StrongTrans

variable {Γ : Type u₁} [Category.{v₁} Γ] {H : Type u₂} [Monoid H]
  {actions : Γ → LocallyDiscrete (SingleObj H) ⥤ᵖ Cat.{v, w}}
  {L L' : EquivariantGroupoidLift Γ actions} (φ : L.Hom L')

/-- The naturality isomorphism of the joint transformation along a symmetry arrow. -/
noncomputable def jointActIso (p : Γ) (a : SingleObj.star H ⟶ SingleObj.star H) :
    L.jointAct p a ⋙ φ.jointFunctor p ≅ φ.jointFunctor p ⋙ L'.jointAct p a :=
  Cat.Hom.toNatIso (φ.joint.naturality (𝟙 p ×ₘ a).toLoc)

@[simp]
lemma jointActIso_hom_app (p : Γ) (a : SingleObj.star H ⟶ SingleObj.star H)
    (Y : L.jointFiber p) :
    (φ.jointActIso p a).hom.app Y =
      (φ.joint.naturality (𝟙 p ×ₘ a).toLoc).hom.toNatTrans.app Y := (rfl)

@[simp]
lemma jointActIso_inv_app (p : Γ) (a : SingleObj.star H ⟶ SingleObj.star H)
    (Y : L.jointFiber p) :
    (φ.jointActIso p a).inv.app Y =
      (φ.joint.naturality (𝟙 p ×ₘ a).toLoc).inv.toNatTrans.app Y := (rfl)

/-- The joint transformation preserves the commuting square of a parameter arrow and a
symmetry arrow. -/
@[reassoc]
lemma jointActCommIso_naturality {p q : Γ} (g : p ⟶ q)
    (a : SingleObj.star H ⟶ SingleObj.star H) (Y : L.jointFiber p) :
    (φ.jointFunctor q).map ((L.jointActCommIso g a).hom.app Y) ≫
        (φ.jointActIso q a).hom.app ((L.jointMap g).obj Y) ≫
          (L'.jointAct q a).map ((φ.jointMapIso g).hom.app Y) =
      (φ.jointMapIso g).hom.app ((L.jointAct p a).obj Y) ≫
        (L'.jointMap g).map ((φ.jointActIso p a).hom.app Y) ≫
          (L'.jointActCommIso g a).hom.app ((φ.jointFunctor p).obj Y) := by
  have h := φ.joint.naturality_isoMapOfCommSq_app
    (CommSq.mk (by simp [← Quiver.Hom.comp_toLoc]) : CommSq (𝟙 p ×ₘ a).toLoc
      (g ×ₘ 𝟙 (SingleObj.star H)).toLoc
      (g ×ₘ 𝟙 (SingleObj.star H)).toLoc (𝟙 q ×ₘ a).toLoc) Y
  rw [L.joint.isoMapOfCommSq_eq _ (g ×ₘ a).toLoc
    (by simp [← Quiver.Hom.comp_toLoc]),
    L'.joint.isoMapOfCommSq_eq _ (g ×ₘ a).toLoc
      (by simp [← Quiver.Hom.comp_toLoc])] at h
  simpa only [Iso.trans_hom, Iso.symm_hom, Cat.Hom₂.comp_app,
    jointActIso_hom_app, jointMapIso_hom_app,
    EquivariantGroupoidLift.jointActCommIso_hom_app, Category.assoc] using h.symm

/-- Compatibility of the prescribed-fiber comparison with the symmetry naturality cells. -/
@[reassoc]
lemma fiberFunctorIso_comparisonNaturality (p : Γ)
    (a : SingleObj.star H ⟶ SingleObj.star H) (Y : L.jointFiber p) :
    (L'.fiberEquivalence p).functor.map ((φ.jointActIso p a).hom.app Y) ≫
        (L'.comparisonNaturality p a).hom.app ((φ.jointFunctor p).obj Y) ≫
          (act actions p a).map ((φ.fiberFunctorIso p).hom.app Y) =
      (φ.fiberFunctorIso p).hom.app ((L.jointAct p a).obj Y) ≫
        (L.comparisonNaturality p a).hom.app Y := by
  -- Pin the actual Cat arrows before evaluating the modification. The restriction
  -- pseudofunctor presents the same fibers through composition with `sectR`.
  let A : L.jointFiber p ⟶ L.jointFiber p := L.joint.map (𝟙 p ×ₘ a).toLoc
  let A' : L'.jointFiber p ⟶ L'.jointFiber p := L'.joint.map (𝟙 p ×ₘ a).toLoc
  let F : L.jointFiber p ⟶ L'.jointFiber p := φ.joint.app ⟨(p, SingleObj.star H)⟩
  let E : L.jointFiber p ⟶ fiber actions p := (L.comparison p).app ⟨SingleObj.star H⟩
  let E' : L'.jointFiber p ⟶ fiber actions p := (L'.comparison p).app ⟨SingleObj.star H⟩
  let T : fiber actions p ⟶ fiber actions p := (actions p).map a.toLoc
  let f : F ≫ E' ⟶ E := (φ.fiberIso p).hom.as.app ⟨SingleObj.star H⟩
  let n : A ≫ F ⟶ F ≫ A' := (φ.joint.naturality (𝟙 p ×ₘ a).toLoc).hom
  let c : A ≫ E ⟶ E ≫ T := ((L.comparison p).naturality a.toLoc).hom
  let c' : A' ≫ E' ⟶ E' ≫ T := ((L'.comparison p).naturality a.toLoc).hom
  have h : A ◁ f ≫ c =
      ((α_ A F E').inv ≫ n ▷ E' ≫ (α_ F A' E').hom ≫
        F ◁ c' ≫ (α_ F E' T).inv) ≫ f ▷ T := by
    exact (φ.fiberIso p).hom.as.naturality a.toLoc
  have h' := congrArg (fun m ↦ m.toNatTrans.app Y) h
  simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
    Cat.associator_hom_app, Cat.associator_inv_app, eqToHom_refl,
    Category.id_comp, Category.assoc] at h'
  simpa only [A, A', F, E, E', T, f, n, c, c',
    fiberFunctorIso_hom_app, jointActIso_hom_app,
    EquivariantGroupoidLift.comparisonNaturality_hom_app,
    EquivariantGroupoidLift.fiberEquivalence_functor,
    Cat.Hom.comp_toFunctor, Functor.comp_obj, Category.assoc] using h'.symm

/-- The inverse prescribed-fiber comparison intertwines the symmetry naturality cells. -/
@[reassoc]
lemma fiberFunctorIso_inv_comparisonNaturality (p : Γ)
    (a : SingleObj.star H ⟶ SingleObj.star H) (Y : L.jointFiber p) :
    (L.comparisonNaturality p a).hom.app Y ≫
        (act actions p a).map ((φ.fiberFunctorIso p).inv.app Y) =
      (φ.fiberFunctorIso p).inv.app ((L.jointAct p a).obj Y) ≫
        (L'.fiberEquivalence p).functor.map ((φ.jointActIso p a).hom.app Y) ≫
          (L'.comparisonNaturality p a).hom.app ((φ.jointFunctor p).obj Y) := by
  rw [← cancel_epi ((φ.fiberFunctorIso p).hom.app ((L.jointAct p a).obj Y))]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← φ.fiberFunctorIso_comparisonNaturality_assoc]
  simp only [← Functor.map_comp, Iso.hom_inv_id_app, Functor.comp_obj]
  simp

/-- The comparison of inverse fibers is equivariant for the prescribed actions. -/
@[reassoc]
lemma inverseFiberIso_actInverseIso (p : Γ)
    (a : SingleObj.star H ⟶ SingleObj.star H) (X : fiber actions p) :
    (φ.jointFunctor p).map ((L.actInverseIso p a).hom.app X) ≫
        (φ.jointActIso p a).hom.app ((L.fiberEquivalence p).inverse.obj X) ≫
          (L'.jointAct p a).map ((φ.inverseFiberIso p).hom.app X) =
      (φ.inverseFiberIso p).hom.app ((act actions p a).obj X) ≫
        (L'.actInverseIso p a).hom.app X := by
  apply (L'.fiberEquivalence p).functor.map_injective
  apply (cancel_mono ((L'.comparisonNaturality p a).hom.app
    ((L'.fiberEquivalence p).inverse.obj X) ≫
      (act actions p a).map ((L'.fiberEquivalence p).counit.app X))).mp
  simp only [Functor.map_comp, Category.assoc]
  erw [(L'.comparisonNaturality p a).hom.naturality_assoc]
  simp only [Functor.comp_map]
  rw [← (act actions p a).map_comp,
    φ.functor_map_inverseFiberIso_hom_app_comp_counit]
  simp only [Functor.map_comp]
  rw [φ.fiberFunctorIso_comparisonNaturality_assoc]
  erw [
    (φ.fiberFunctorIso p).hom.naturality_assoc,
    L.functor_map_actInverseIso_hom_app_comp_assoc,
    L'.functor_map_actInverseIso_hom_app_comp_assoc]
  simp only [← Functor.map_comp, Iso.inv_hom_id_app, Functor.comp_obj, Functor.id_obj]
  rw [(act actions p a).map_id, Category.comp_id, Category.comp_id]
  exact (φ.functor_map_inverseFiberIso_hom_app_comp_counit p _).symm

/-- The comparison induced by a morphism of lifts is equivariant: its transport
isomorphisms commute with each prescribed symmetry functor. -/
@[reassoc]
lemma transportIso_transportCommIso {p q : Γ} (g : p ⟶ q)
    (a : SingleObj.star H ⟶ SingleObj.star H) (X : fiber actions p) :
    (L.transportCommIso g a).hom.app X ≫
        (act actions q a).map ((φ.transportIso g).hom.app X) =
      (φ.transportIso g).hom.app ((act actions p a).obj X) ≫
        (L'.transportCommIso g a).hom.app X := by
  simp only [transportIso_hom_app, EquivariantGroupoidLift.transportCommIso_hom_app,
    EquivariantGroupoidLift.transport, Functor.comp_obj, Functor.map_comp, Category.assoc]
  rw [φ.fiberFunctorIso_inv_comparisonNaturality_assoc]
  -- Move the fiber comparison to the beginning, and the target action comparison to the end.
  erw [(φ.fiberFunctorIso q).inv.naturality_assoc,
    (φ.fiberFunctorIso q).inv.naturality_assoc,
    ← (L'.comparisonNaturality q a).hom.naturality_assoc]
  simp only [Functor.comp_map]
  erw [← (L'.comparisonNaturality q a).hom.naturality]
  simp only [Functor.comp_map]
  rw [cancel_epi]
  simp only [← Category.assoc]
  rw [cancel_mono]
  simp only [← Functor.map_comp]
  congr 1
  simp only [Functor.map_comp, Category.assoc]
  rw [φ.jointActCommIso_naturality_assoc]
  erw [(φ.jointMapIso g).hom.naturality_assoc]
  erw [← (L'.jointActCommIso g a).hom.naturality]
  simp only [Functor.comp_map]
  rw [← (L'.jointMap g).map_comp_assoc,
    ← (L'.jointMap g).map_comp_assoc]
  simp only [Category.assoc]
  rw [φ.inverseFiberIso_actInverseIso, Functor.map_comp, Category.assoc]

end TauCeti.EquivariantGroupoidLift.Hom
