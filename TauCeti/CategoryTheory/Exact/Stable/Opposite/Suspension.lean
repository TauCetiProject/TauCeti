/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Opposite.Basic
public import TauCeti.CategoryTheory.Exact.Stable.Loop
public import TauCeti.CategoryTheory.Exact.Stable.Suspension

/-!
# Suspension in the opposite stable category

For a Frobenius exact category, the comparison from the stable category of the opposite
to the opposite stable category carries suspension to the opposite loop functor. Thus
duality reverses the direction of translation. The comparison is canonical despite the
independent choices of presentations: an opposite loop presentation is an injective
presentation, and the stable comparison of injective presentations identifies it with
the chosen suspension presentation.

This file constructs that natural isomorphism and gives its components on representatives.
Compatibility with distinguished triangles is a separate assertion.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
* `TauCeti.CategoryTheory.Exact.Stable.Presentation`: the canonical stable comparison of
  injective presentations used here.
-/

public section

namespace TauCeti.ExactStructure.IsFrobenius

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {E : ExactStructure C} (hE : E.IsFrobenius)

private theorem map_opLoopPresentation_cokernelMap {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    E.op.projectiveStableFunctor.map
        ((hE.enoughProjectives.projectivePresentation X.unop).op.cokernelMap
          (hE.enoughProjectives.projectivePresentation Y.unop).op f) =
      E.op.projectiveStableFunctor.map
        (eqToHom (ProjectivePresentation.op_K _) ≫
          (hE.enoughProjectives.loopMap f.unop).op ≫
          eqToHom (ProjectivePresentation.op_K _).symm) := by
  apply E.op.projectiveStableFunctor_map_cokernelMap_eq
    (hE.enoughProjectives.projectivePresentation X.unop).op
    (hE.enoughProjectives.projectivePresentation Y.unop).op
    (hE.op.isProjective_I (hE.enoughProjectives.projectivePresentation Y.unop).op) f
    (eqToHom (ProjectivePresentation.op_I _) ≫
      (hE.enoughProjectives.loopMiddleMap f.unop).op ≫
      eqToHom (ProjectivePresentation.op_I _).symm)
  · rw [← cancel_mono (eqToHom (ProjectivePresentation.op_I _))]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rw [reassoc_of% (ProjectivePresentation.op_i
      (hE.enoughProjectives.projectivePresentation X.unop)),
      ProjectivePresentation.op_i]
    apply Quiver.Hom.unop_inj
    simpa only [CategoryTheory.unop_comp, Quiver.Hom.unop_op] using
      hE.enoughProjectives.loopMiddleMap_comp_loopDeflation f.unop
  · -- Identify both endpoints before comparing with the original loop square.
    rw [← cancel_mono (eqToHom (ProjectivePresentation.op_K _)),
      ← cancel_epi (eqToHom (ProjectivePresentation.op_I _).symm)]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id, Category.id_comp]
    rw [reassoc_of% (ProjectivePresentation.op_p
        (hE.enoughProjectives.projectivePresentation X.unop)),
      ProjectivePresentation.op_p]
    apply Quiver.Hom.unop_inj
    simpa only [CategoryTheory.unop_comp, Quiver.Hom.unop_op] using
      hE.enoughProjectives.loopMap_comp_loopInflation f.unop

private noncomputable def opSuspensionObjIso (X : Cᵒᵖ) :
    (E.projectiveStableOpFunctor hE.projective_iff_injective).obj
        (hE.op.stableSuspension.obj (E.op.projectiveStableFunctor.obj X)) ≅
      hE.enoughProjectives.stableLoop.op.obj
        ((E.projectiveStableOpFunctor hE.projective_iff_injective).obj
          (E.op.projectiveStableFunctor.obj X)) :=
  eqToIso (congrArg (E.projectiveStableOpFunctor hE.projective_iff_injective).obj
    (hE.op.stableSuspension_obj_projectiveStableFunctor_obj X)) ≪≫
  (E.projectiveStableOpFunctor hE.projective_iff_injective).mapIso
    (hE.op.projectiveStableIsoSuspensionObj
      (hE.enoughProjectives.projectivePresentation X.unop).op).symm ≪≫
  eqToIso (E.projectiveStableOpFunctor_obj hE.projective_iff_injective
    (hE.enoughProjectives.projectivePresentation X.unop).op.K) ≪≫
  eqToIso (congrArg (fun K ↦ Opposite.op (E.projectiveStableFunctor.obj K.unop))
    (ProjectivePresentation.op_K _)) ≪≫
  eqToIso (congrArg Opposite.op
    (hE.enoughProjectives.stableLoop_obj_projectiveStableFunctor_obj X.unop).symm) ≪≫
  eqToIso (congrArg hE.enoughProjectives.stableLoop.op.obj
    (E.projectiveStableOpFunctor_obj hE.projective_iff_injective X).symm)

private theorem opSuspensionObjIso_hom_naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (hE.op.stableSuspension ⋙ E.projectiveStableOpFunctor hE.projective_iff_injective).map
        (E.op.projectiveStableFunctor.map f) ≫ (opSuspensionObjIso hE Y).hom =
      (opSuspensionObjIso hE X).hom ≫
        (E.projectiveStableOpFunctor hE.projective_iff_injective ⋙
          hE.enoughProjectives.stableLoop.op).map (E.op.projectiveStableFunctor.map f) := by
  have h := (hE.op.projectiveStableIsoSuspensionObj_hom_naturality
    (hE.enoughProjectives.projectivePresentation X.unop).op
    (hE.enoughProjectives.projectivePresentation Y.unop).op f).symm
  rw [← Iso.eq_inv_comp, ← Category.assoc, ← Iso.comp_inv_eq] at h
  rw [map_opLoopPresentation_cokernelMap hE f] at h
  simp only [Functor.comp_map, stableSuspension_map_projectiveStableFunctor_map,
    Functor.map_comp, opSuspensionObjIso, Iso.trans_hom, eqToIso.hom,
    Functor.mapIso_hom, Iso.symm_hom, eqToHom_map, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  rw [← Functor.map_comp_assoc, h, Functor.map_comp_assoc]
  simp [E.projectiveStableOpFunctor_map, Functor.op_map,
    hE.enoughProjectives.stableLoop_map_projectiveStableFunctor_map,
    Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc]

/-- The canonical opposite stable comparison carries suspension in the opposite exact
category to the opposite of the loop functor in the original exact category. -/
noncomputable def stableSuspensionCompProjectiveStableOpFunctorIso :
    hE.op.stableSuspension ⋙ E.projectiveStableOpFunctor hE.projective_iff_injective ≅
      E.projectiveStableOpFunctor hE.projective_iff_injective ⋙
        hE.enoughProjectives.stableLoop.op :=
  CategoryTheory.Quotient.natIsoLift _ <|
    NatIso.ofComponents (opSuspensionObjIso hE)
      (opSuspensionObjIso_hom_naturality hE)

/-- On a represented object, the comparison is the image of the canonical comparison
from the chosen opposite suspension presentation to the opposite loop presentation. -/
@[simp]
theorem stableSuspensionCompProjectiveStableOpFunctorIso_hom_app (X : Cᵒᵖ) :
    (hE.stableSuspensionCompProjectiveStableOpFunctorIso).hom.app
        (E.op.projectiveStableFunctor.obj X) =
      eqToHom (congrArg (E.projectiveStableOpFunctor hE.projective_iff_injective).obj
        (hE.op.stableSuspension_obj_projectiveStableFunctor_obj X)) ≫
      (E.projectiveStableOpFunctor hE.projective_iff_injective).map
        (E.op.projectiveStableFunctor.map
          ((hE.op.suspensionPresentation X).cokernelMap
            (hE.enoughProjectives.projectivePresentation X.unop).op (𝟙 X))) ≫
      eqToHom (E.projectiveStableOpFunctor_obj hE.projective_iff_injective
        (hE.enoughProjectives.projectivePresentation X.unop).op.K) ≫
      eqToHom (congrArg (fun K ↦ Opposite.op (E.projectiveStableFunctor.obj K.unop))
        (ProjectivePresentation.op_K _)) ≫
      eqToHom (congrArg Opposite.op
        (hE.enoughProjectives.stableLoop_obj_projectiveStableFunctor_obj X.unop).symm) ≫
      eqToHom (congrArg hE.enoughProjectives.stableLoop.op.obj
        (E.projectiveStableOpFunctor_obj hE.projective_iff_injective X).symm) := by
  simp [stableSuspensionCompProjectiveStableOpFunctorIso, opSuspensionObjIso]

/-- The inverse component is induced by the comparison from the opposite loop
presentation to the chosen opposite suspension presentation. -/
@[simp]
theorem stableSuspensionCompProjectiveStableOpFunctorIso_inv_app (X : Cᵒᵖ) :
    (hE.stableSuspensionCompProjectiveStableOpFunctorIso).inv.app
        (E.op.projectiveStableFunctor.obj X) =
      eqToHom (congrArg hE.enoughProjectives.stableLoop.op.obj
        (E.projectiveStableOpFunctor_obj hE.projective_iff_injective X)) ≫
      eqToHom (congrArg Opposite.op
        (hE.enoughProjectives.stableLoop_obj_projectiveStableFunctor_obj X.unop)) ≫
      eqToHom (congrArg (fun K ↦ Opposite.op (E.projectiveStableFunctor.obj K.unop))
        (ProjectivePresentation.op_K _)).symm ≫
      eqToHom (E.projectiveStableOpFunctor_obj hE.projective_iff_injective
        (hE.enoughProjectives.projectivePresentation X.unop).op.K).symm ≫
      (E.projectiveStableOpFunctor hE.projective_iff_injective).map
        (E.op.projectiveStableFunctor.map
          ((hE.enoughProjectives.projectivePresentation X.unop).op.cokernelMap
            (hE.op.suspensionPresentation X) (𝟙 X))) ≫
      eqToHom (congrArg (E.projectiveStableOpFunctor hE.projective_iff_injective).obj
        (hE.op.stableSuspension_obj_projectiveStableFunctor_obj X)).symm := by
  simp [stableSuspensionCompProjectiveStableOpFunctorIso, opSuspensionObjIso]

end TauCeti.ExactStructure.IsFrobenius
