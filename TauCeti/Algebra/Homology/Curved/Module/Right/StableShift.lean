/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Stable
public import TauCeti.CategoryTheory.Exact.Stable.Shift
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# Stable suspension is cohomological shift

The identity-cone injective presentations have cokernel `M[1]`. Comparing these presentations
with the choices used for stable suspension gives a natural isomorphism from stable suspension
to cohomological shift under the stable-to-homotopy equivalence. The latter comparison is
negated: with cone differential `(-dM x, f x + dN y)`, this makes the cone triangle have the
positive cone projection as its third arrow and the usual negative shifted map after rotation.

## References

* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 7.6.
* The Tau Ceti contributors, `TauCeti.Algebra.Homology.Curved.Shift`: the presentation comparison
  and quotient descent proofs adapt the corresponding parity-shift construction.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti.CurvedDGRightModuleCat

universe u

attribute [local implicit_reducible] ForgetEnrichment dgClosedToHomotopy
  DGHomotopyCategory.of DGHomotopyCategory.underlying
  EnrichedFunctor.ofDGMap EnrichedFunctor.mapDGHomotopyCategory

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w}

/-- The map on cokernels of the identity-cone presentations represents the shifted map. -/
theorem projectiveStableFunctor_map_coneIdentityInjectivePresentation_cokernelMap
    {M N : CurvedDGRightModuleCat.{u, u, u} h}
    (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N) :
    (gradedSplitExact (h := h)).projectiveStableFunctor.map
        ((coneIdentityInjectivePresentation M).cokernelMap
          (coneIdentityInjectivePresentation N) f) =
      (gradedSplitExact (h := h)).projectiveStableFunctor.map
        (eqToHom ((coneIdentityInjectivePresentation_K M).trans
        (closedShiftFunctor_obj_of 1 M).symm) ≫
          (closedShiftFunctor 1).map f ≫
            eqToHom ((coneIdentityInjectivePresentation_K N).trans
        (closedShiftFunctor_obj_of 1 N).symm).symm) := by
  let k : dgRightModuleCochains (R := R) (A := A) (ℳ := M.grading) (ℳN := N.grading) (-1) := 0
  have hsq : ∀ x : M, closedHom f (closedHom (𝟙 (ForgetEnrichment.of _ M)) x) -
      closedHom (𝟙 (ForgetEnrichment.of _ N)) (closedHom f x) =
        N.differential (k.1 x) + k.1 (M.differential x) := by
    intro x
    simp [k]
  have hN : (gradedSplitExact (h := h)).isProjective
      (coneIdentityInjectivePresentation N).I := by
    rw [coneIdentityInjectivePresentation_I]
    exact gradedSplitExact_isProjective_of_isZero_homotopy
      (isZero_homotopy_cone_isIso (𝟙 (ForgetEnrichment.of _ N)))
  apply ExactStructure.projectiveStableFunctor_map_cokernelMap_eq
    (coneIdentityInjectivePresentation M) (coneIdentityInjectivePresentation N) hN f
    (eqToHom (coneIdentityInjectivePresentation_I M) ≫
      coneMap _ _ f f k hsq ≫ eqToHom (coneIdentityInjectivePresentation_I N).symm)
    (eqToHom ((coneIdentityInjectivePresentation_K M).trans
        (closedShiftFunctor_obj_of 1 M).symm) ≫
      (closedShiftFunctor 1).map f ≫ eqToHom ((coneIdentityInjectivePresentation_K N).trans
        (closedShiftFunctor_obj_of 1 N).symm).symm)
  · apply (cancel_mono (eqToHom (coneIdentityInjectivePresentation_I N))).mp
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
      coneIdentityInjectivePresentation_i]
    rw [← Category.assoc, coneIdentityInjectivePresentation_i]
    exact coneInclusion_comp_coneMap _ _ f f k hsq
  · apply (cancel_mono (eqToHom ((coneIdentityInjectivePresentation_K N).trans
        (closedShiftFunctor_obj_of 1 N).symm))).mp
    apply (cancel_epi (eqToHom (coneIdentityInjectivePresentation_I M).symm)).mp
    have hpM := coneIdentityInjectivePresentation_p M
    have hpN := coneIdentityInjectivePresentation_p N
    rw [eqToHom_comp_iff, comp_eqToHom_iff] at hpM hpN
    rw [hpM, hpN]
    -- Only the already exposed closed-shift/forgetful object wrappers reduce here.
    -- The presentation itself has been replaced by its public projection equation above.
    simpa only [closedShiftFunctor, EnrichedFunctor.forget_obj, dgShiftFunctor_obj,
      Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Category.comp_id] using (coneMap_comp_coneProjection _ _ f f k hsq).symm

/-- Under the stable quotient, stable suspension is naturally cohomological shift by one. -/
noncomputable def gradedSplitStableSuspensionIsoShift :
    (gradedSplitExact (h := h)).projectiveStableFunctor ⋙
        (gradedSplitExact_isFrobenius (h := h)).stableSuspension ≅
      closedShiftFunctor 1 ⋙ (gradedSplitExact (h := h)).projectiveStableFunctor :=
  (NatIso.ofComponents (fun X ↦ Iso.trans
    (X := (closedShiftFunctor 1 ⋙ (gradedSplitExact (h := h)).projectiveStableFunctor).obj X)
    (Z := (((gradedSplitExact (h := h)).projectiveStableFunctor ⋙
      (gradedSplitExact_isFrobenius (h := h)).stableSuspension).obj X))
    ((gradedSplitExact (h := h)).projectiveStableFunctor.mapIso
        (eqToIso ((coneIdentityInjectivePresentation_K (ForgetEnrichment.to _ X)).trans
        (closedShiftFunctor_obj_of 1 (ForgetEnrichment.to _ X)).symm).symm) ≪≫
      (gradedSplitExact_isFrobenius (h := h)).projectiveStableIsoSuspensionObj
        (coneIdentityInjectivePresentation (ForgetEnrichment.to _ X)))
    (eqToIso
      ((gradedSplitExact_isFrobenius (h := h)).stableSuspension_obj_projectiveStableFunctor_obj
        X).symm)) (fun {X Y} f ↦ by
    have hnat :=
      (gradedSplitExact_isFrobenius (h := h)).projectiveStableIsoSuspensionObj_hom_naturality
        (coneIdentityInjectivePresentation (ForgetEnrichment.to _ X))
        (coneIdentityInjectivePresentation (ForgetEnrichment.to _ Y)) f
    rw [projectiveStableFunctor_map_coneIdentityInjectivePresentation_cokernelMap] at hnat
    simp only [Functor.map_comp, eqToHom_map, Category.assoc] at hnat
    rw [Functor.comp_map, Functor.comp_map,
      ExactStructure.IsFrobenius.stableSuspension_map_projectiveStableFunctor_map]
    erw [Iso.trans_hom, Iso.trans_hom]
    simp only [Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom]
    apply (cancel_epi ((gradedSplitExact (h := h)).projectiveStableFunctor.map
      (eqToHom ((coneIdentityInjectivePresentation_K (ForgetEnrichment.to _ X)).trans
        (closedShiftFunctor_obj_of 1 (ForgetEnrichment.to _ X)).symm)))).mp
    simpa only [Functor.map_comp, eqToIso.hom, eqToIso.inv, ForgetEnrichment.of_to,
      eqToHom_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Category.comp_id] using (reassoc_of% hnat)
        (eqToHom
          ((gradedSplitExact_isFrobenius (h := h)).stableSuspension_obj_projectiveStableFunctor_obj
            Y).symm))).symm

/-- The suspension comparison is the stable map on cokernels induced by the identity. -/
@[simp]
theorem gradedSplitStableSuspensionIsoShift_hom_app
    (X : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ)
      (CurvedDGRightModuleCat.{u, u, u} h)) :
    (gradedSplitStableSuspensionIsoShift (h := h)).hom.app X =
      eqToHom
        ((gradedSplitExact_isFrobenius (h := h)).stableSuspension_obj_projectiveStableFunctor_obj
          X) ≫ (gradedSplitExact (h := h)).projectiveStableFunctor.map
          (((gradedSplitExact_isFrobenius (h := h)).suspensionPresentation X).cokernelMap
            (coneIdentityInjectivePresentation (ForgetEnrichment.to _ X)) (𝟙 X) ≫
              eqToHom ((coneIdentityInjectivePresentation_K (ForgetEnrichment.to _ X)).trans
        (closedShiftFunctor_obj_of 1 (ForgetEnrichment.to _ X)).symm)) := by
  simp only [gradedSplitStableSuspensionIsoShift, Iso.symm_hom, NatIso.ofComponents_inv_app]
  erw [Iso.trans_inv]
  simp only [Iso.trans_inv, Functor.mapIso_inv, eqToIso.inv,
    ExactStructure.IsFrobenius.projectiveStableIsoSuspensionObj_inv, Functor.map_comp]
  simp only [ForgetEnrichment.of_to]

/-- The stable comparison intertwines stable suspension with cohomological shift, with the
negative sign that gives the cone triangle its positive projection as third arrow. -/
noncomputable def stableSuspensionCompGradedSplitStableToHomotopyIso :
    (gradedSplitExact_isFrobenius (h := h)).stableSuspension ⋙
        gradedSplitStableToHomotopy (h := h) ≅
      gradedSplitStableToHomotopy (h := h) ⋙ homotopyShiftFunctor 1 := by
  let e : (gradedSplitExact_isFrobenius (h := h)).stableSuspension ⋙
      gradedSplitStableToHomotopy (h := h) ≅
      gradedSplitStableToHomotopy (h := h) ⋙ homotopyShiftFunctor 1 :=
    Quotient.natIsoLift _ <|
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight gradedSplitStableSuspensionIsoShift _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _
          (eqToIso projectiveStableFunctor_comp_gradedSplitStableToHomotopy) ≪≫
        (dgShiftFunctor (h := h) 1).forgetCompDgClosedToHomotopyIso ≪≫
        Functor.isoWhiskerRight
          (eqToIso projectiveStableFunctor_comp_gradedSplitStableToHomotopy.symm) _ ≪≫
            Functor.associator _ _ _
  exact
    { hom := -e.hom
      inv := -e.inv
      hom_inv_id := by simp
      inv_hom_id := by simp }

/-- On the stable image of a closed object, the signed suspension comparison is the negative
image of the identity-cone presentation comparison, transported to the actual shifted object. -/
private theorem stableSuspensionCompGradedSplitStableToHomotopyIso_hom_app_aux
    (X : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ)
      (CurvedDGRightModuleCat.{u, u, u} h)) :
    (stableSuspensionCompGradedSplitStableToHomotopyIso (h := h)).hom.app
        ((gradedSplitExact (h := h)).projectiveStableFunctor.obj X) =
      -((gradedSplitStableToHomotopy (h := h)).map
        ((gradedSplitStableSuspensionIsoShift (h := h)).hom.app X) ≫
          eqToHom (by
            simpa using congrArg (dgClosedToHomotopy R).obj
              (closedShiftFunctor_obj_of 1 (ForgetEnrichment.to _ X)))) := by
  simp only [Functor.comp_obj, stableSuspensionCompGradedSplitStableToHomotopyIso,
    Quotient.natIsoLift_hom, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Quotient.natIsoLift_inv, Iso.trans_inv, Category.assoc, Functor.isoWhiskerRight_inv,
    Iso.symm_inv, NatTrans.app_neg, Quotient.natTransLift_app, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, EnrichedFunctor.forgetCompDgClosedToHomotopyIso_hom_app,
    EnrichedFunctor.forget_obj, Category.id_comp, neg_inj]
  simp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, eqToIso.hom,
    eqToHom_app, eqToHom_map, Functor.comp_obj]
  erw [Category.id_comp]
  apply congrArg (fun f ↦ (gradedSplitStableToHomotopy (h := h)).map
    ((gradedSplitStableSuspensionIsoShift (h := h)).hom.app X) ≫ f)
  erw [Category.comp_id]
  exact eqToHom_trans (C := DGHomotopyCategory R (CurvedDGRightModuleCat.{u, u, u} h)) _ _

/-- The stable comparison commutes coherently with the stable and cohomological integer shifts. -/
@[instance_reducible]
noncomputable def gradedSplitStableToHomotopyCommShift :
    letI := (gradedSplitExact_isFrobenius (h := h)).stableHasShift
    (gradedSplitStableToHomotopy (h := h)).CommShift ℤ := by
  exact (gradedSplitExact_isFrobenius (h := h)).commShiftOfIntertwiningStableSuspensionShift
    gradedSplitStableToHomotopy stableSuspensionCompGradedSplitStableToHomotopyIso

/-- At degree one the coherent shift comparison is the identity-cone suspension comparison. -/
theorem gradedSplitStableToHomotopyCommShift_iso_one :
    letI := (gradedSplitExact_isFrobenius (h := h)).stableHasShift
    letI := gradedSplitStableToHomotopyCommShift (h := h)
    (gradedSplitStableToHomotopy (h := h)).commShiftIso (1 : ℤ) =
      Functor.isoWhiskerRight (gradedSplitExact_isFrobenius (h := h)).stableShiftFunctorOneIso
        gradedSplitStableToHomotopy ≪≫ stableSuspensionCompGradedSplitStableToHomotopyIso := by
  unfold gradedSplitStableToHomotopyCommShift
  exact
    (gradedSplitExact_isFrobenius (h := h)).commShiftOfIntertwiningStableSuspensionShift_iso_one
    gradedSplitStableToHomotopy stableSuspensionCompGradedSplitStableToHomotopyIso

/-- The signed suspension component is the negative homotopy class of the identity-induced
map from the chosen suspension presentation to the identity-cone presentation. -/
theorem stableSuspensionCompGradedSplitStableToHomotopyIso_hom_app
    (X : ForgetEnrichment (CochainComplex (ModuleCat R) ℤ)
      (CurvedDGRightModuleCat.{u, u, u} h)) :
    (stableSuspensionCompGradedSplitStableToHomotopyIso (h := h)).hom.app
        ((gradedSplitExact (h := h)).projectiveStableFunctor.obj X) =
      -(eqToHom (by
          simp [ExactStructure.IsFrobenius.stableSuspension_obj_projectiveStableFunctor_obj]) ≫
        (dgClosedToHomotopy R).map
          (((gradedSplitExact_isFrobenius (h := h)).suspensionPresentation X).cokernelMap
            (coneIdentityInjectivePresentation (ForgetEnrichment.to _ X)) (𝟙 X)) ≫
        eqToHom (by
          simp only [Functor.comp_obj,
            gradedSplitStableToHomotopy_obj_projectiveStableFunctor_obj,
            coneIdentityInjectivePresentation_K, dgClosedToHomotopy_obj,
            homotopyShiftFunctor_obj_of, ForgetEnrichment.to_of])) := by
  rw [stableSuspensionCompGradedSplitStableToHomotopyIso_hom_app_aux,
    gradedSplitStableSuspensionIsoShift_hom_app]
  -- The public cokernel equation supplies the transport to the shifted module; functoriality
  -- combines it with the object transports in the stable comparison's public map equation.
  simp [Functor.map_comp, eqToHom_map, Category.assoc,
    gradedSplitStableToHomotopy_map_projectiveStableFunctor_map]

end TauCeti.CurvedDGRightModuleCat
