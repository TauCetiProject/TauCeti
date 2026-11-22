/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Autoequivalence
public import TauCeti.CategoryTheory.Exact.Stable.Functor.Basic

/-!
# Stable functors commute with suspension

An exact functor between Frobenius exact categories which preserves projective-injective objects
descends to their stable categories. This file constructs the canonical comparison between that
stable functor and suspension, and proves compatibility with the connecting maps of conflations.

Apply the original functor to a chosen injective presentation `X ⟶ I(X) ⟶ ΣX`. Its image
is an injective presentation of `F(X)`, because the functor preserves conflations and
projective-injective objects. Independence of injective presentations then identifies `F(ΣX)`
with `Σ(F(X))` in the target stable category. These identifications are natural and descend to
the source stable category.

## Main definitions

* `TauCeti.StableConflationExact.mapSuspensionPresentation`: the image of the chosen suspension
  presentation under a stable conflation-exact functor.
* `TauCeti.StableConflationExact.stableSuspensionCompStableFunctorIso`: the natural isomorphism
  comparing suspension composed with the induced stable functor to the opposite composite.

## Main results

* `TauCeti.StableConflationExact.stableSuspensionCompStableFunctorIso_hom_app_eq_connectingMap`:
  on the class of an object, the comparison is the connecting map of the image of its suspension
  presentation.
* `TauCeti.StableConflationExact.stableSuspensionCompStableFunctorIso_comp`: compatibility of the
  suspension comparison with composition of stable conflation-exact functors.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

namespace StableConflationExact

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
variable [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
variable {E : ExactStructure C} {E' : ExactStructure D}
variable {F : Functor C D} [F.Additive]

/-- Applying a stable conflation-exact functor to the chosen suspension presentation of `X`
gives an injective presentation of `F.obj X` in the target exact category. -/
noncomputable def mapSuspensionPresentation (hF : StableConflationExact E E' F)
    (hE : E.IsFrobenius) (X : C) :
    E'.InjectivePresentation (F.obj X) where
  I := F.obj (hE.suspensionInjective X)
  K := F.obj (hE.suspensionObj X)
  i := F.map (hE.suspensionInflation X)
  p := F.map (hE.suspensionDeflation X)
  zero := by rw [← F.map_comp, (hE.suspensionPresentation X).zero, F.map_zero]
  conflation := hF.isConflationExact.map_conflation (hE.suspensionPresentation X).conflation
  isInjective := ((E'.projectiveInjective_iff _).1 <| hF.map_projectiveInjective <|
    (E.projectiveInjective_iff _).2
      ⟨hE.isProjective_I (hE.suspensionPresentation X),
        (hE.suspensionPresentation X).isInjective⟩).2

/-- The middle term of the mapped suspension presentation is the image of the chosen middle
term. -/
@[simp]
theorem mapSuspensionPresentation_I (hF : StableConflationExact E E' F)
    (hE : E.IsFrobenius) (X : C) :
    (hF.mapSuspensionPresentation hE X).I = F.obj (hE.suspensionInjective X) := by
  simp [mapSuspensionPresentation]

/-- The cokernel term of the mapped suspension presentation is the image of the chosen
suspension object. -/
@[simp]
theorem mapSuspensionPresentation_K (hF : StableConflationExact E E' F)
    (hE : E.IsFrobenius) (X : C) :
    (hF.mapSuspensionPresentation hE X).K = F.obj (hE.suspensionObj X) := by
  simp [mapSuspensionPresentation]

/-- The inflation in the mapped suspension presentation is the image of the chosen inflation. -/
@[simp]
theorem mapSuspensionPresentation_i (hF : StableConflationExact E E' F)
    (hE : E.IsFrobenius) (X : C) :
    HEq (hF.mapSuspensionPresentation hE X).i (F.map (hE.suspensionInflation X)) := by
  simp [mapSuspensionPresentation]

/-- The deflation in the mapped suspension presentation is the image of the chosen deflation. -/
@[simp]
theorem mapSuspensionPresentation_p (hF : StableConflationExact E E' F)
    (hE : E.IsFrobenius) (X : C) :
    HEq (hF.mapSuspensionPresentation hE X).p (F.map (hE.suspensionDeflation X)) := by
  simp [mapSuspensionPresentation]

/-- The middle term of the mapped suspension presentation remains projective. -/
theorem isProjective_I_mapSuspensionPresentation (hF : StableConflationExact E E' F)
    (hE : E.IsFrobenius) (X : C) :
    E'.isProjective (hF.mapSuspensionPresentation hE X).I :=
  ((E'.projectiveInjective_iff _).1 <| hF.map_projectiveInjective <|
    (E.projectiveInjective_iff _).2
      ⟨hE.isProjective_I (hE.suspensionPresentation X),
        (hE.suspensionPresentation X).isInjective⟩).1

/-- The image of a connecting map, followed by the comparison from the mapped suspension
presentation to the chosen target presentation, is the connecting map of the image conflation
in the target stable category. -/
@[reassoc (attr := simp)]
theorem map_connectingMap_comp_suspensionComparison
    (hF : StableConflationExact E E' F) (hE : E.IsFrobenius) (hE' : E'.IsFrobenius)
    {S : ShortComplex C} (hS : E.Conflation S) :
    E'.projectiveStableFunctor.map (F.map (hE.connectingMap hS)) ≫
        eqToHom (congrArg E'.projectiveStableFunctor.obj
          (hF.mapSuspensionPresentation_K hE S.X₁).symm) ≫
        E'.projectiveStableFunctor.map
          ((hF.mapSuspensionPresentation hE S.X₁).cokernelMap
            (hE'.suspensionPresentation (F.obj S.X₁)) (𝟙 _)) =
      E'.projectiveStableFunctor.map
        (hE'.connectingMap (hF.isConflationExact.map_conflation hS)) := by
  let P := hF.mapSuspensionPresentation hE S.X₁
  let Q := hE'.suspensionPresentation (F.obj S.X₁)
  -- The mapped presentation has opaque, dependently typed component maps. Transport the
  -- image of the connecting map to its cokernel term before applying the comparison.
  let δ : (S.map F).X₃ ⟶ P.K :=
    F.map (hE.connectingMap hS) ≫ eqToHom (hF.mapSuspensionPresentation_K hE S.X₁).symm
  let a : (S.map F).X₂ ⟶ P.I :=
    F.map (hE.connectingMiddleMap hS) ≫ eqToHom (hF.mapSuspensionPresentation_I hE S.X₁).symm
  have ha : (S.map F).f ≫ a = P.i := by
    have hf : F.map S.f ≫ F.map (hE.connectingMiddleMap hS) =
        F.map (hE.suspensionInflation S.X₁) := by
      rw [← F.map_comp, hE.f_comp_connectingMiddleMap hS]
    dsimp [a, P]
    rw [← Category.assoc]
    apply eq_of_heq
    exact (comp_eqToHom_heq _ _).trans <|
      (heq_of_eq hf).trans (hF.mapSuspensionPresentation_i hE S.X₁).symm
  have hδ : (S.map F).g ≫ δ = a ≫ P.p := by
    have hg : F.map S.g ≫ F.map (hE.connectingMap hS) =
        F.map (hE.connectingMiddleMap hS) ≫ F.map (hE.suspensionDeflation S.X₁) := by
      rw [← F.map_comp, hE.g_comp_connectingMap hS, F.map_comp]
    have hp : a ≫ P.p ≍
        F.map (hE.connectingMiddleMap hS) ≫ F.map (hE.suspensionDeflation S.X₁) :=
      heq_comp rfl (hF.mapSuspensionPresentation_I hE S.X₁)
        (hF.mapSuspensionPresentation_K hE S.X₁)
        (comp_eqToHom_heq _ _) (hF.mapSuspensionPresentation_p hE S.X₁)
    dsimp [δ]
    rw [← Category.assoc]
    exact eq_of_heq ((comp_eqToHom_heq _ _).trans ((heq_of_eq hg).trans hp.symm))
  have h := hE'.projectiveStableFunctor_map_connectingMap_eq
    (hF.isConflationExact.map_conflation hS)
    (a ≫ P.middleMap Q (𝟙 _)) (δ ≫ P.cokernelMap Q (𝟙 _))
    (by
      rw [← Category.assoc, ha, P.i_comp_middleMap]
      simp [Q])
    (by
      rw [← Category.assoc, hδ, Category.assoc, P.p_comp_cokernelMap]
      simp [Q])
  rw [Functor.map_comp] at h
  simpa [δ, P, Q, Functor.map_comp, eqToHom_map, Category.assoc] using h.symm

/-- The map induced between mapped suspension presentations agrees in the stable category with
the image of the map induced between the original suspension presentations. -/
private theorem projectiveStableFunctor_map_mapSuspensionPresentation_cokernelMap
    (hF : StableConflationExact E E' F) (hE : E.IsFrobenius) {X Y : C} (f : X ⟶ Y) :
    E'.projectiveStableFunctor.map
        (F.map ((hE.suspensionPresentation X).cokernelMap
          (hE.suspensionPresentation Y) f)) ≫
          eqToHom (congrArg E'.projectiveStableFunctor.obj
            (hF.mapSuspensionPresentation_K hE Y).symm) =
      eqToHom (congrArg E'.projectiveStableFunctor.obj
          (hF.mapSuspensionPresentation_K hE X).symm) ≫
        E'.projectiveStableFunctor.map
          ((hF.mapSuspensionPresentation hE X).cokernelMap
            (hF.mapSuspensionPresentation hE Y) (F.map f)) := by
  have h := E'.projectiveStableFunctor_map_cokernelMap_eq
      (hF.mapSuspensionPresentation hE X)
      (hF.mapSuspensionPresentation hE Y)
      (hF.isProjective_I_mapSuspensionPresentation hE Y)
      (F.map f)
      (F.map ((hE.suspensionPresentation X).middleMap
        (hE.suspensionPresentation Y) f))
      (F.map ((hE.suspensionPresentation X).cokernelMap
        (hE.suspensionPresentation Y) f))
      (by
        -- Expose the bundled presentation maps through their characteristic component formulas.
        change F.map (hE.suspensionInflation X) ≫
          F.map ((hE.suspensionPresentation X).middleMap
            (hE.suspensionPresentation Y) f) =
            F.map f ≫ F.map (hE.suspensionInflation Y)
        rw [← F.map_comp, ← F.map_comp,
          (hE.suspensionPresentation X).i_comp_middleMap])
      (by
        -- Expose the bundled presentation maps through their characteristic component formulas.
        change F.map (hE.suspensionDeflation X) ≫
          F.map ((hE.suspensionPresentation X).cokernelMap
            (hE.suspensionPresentation Y) f) =
            F.map ((hE.suspensionPresentation X).middleMap
              (hE.suspensionPresentation Y) f) ≫ F.map (hE.suspensionDeflation Y)
        rw [← F.map_comp, ← F.map_comp,
          (hE.suspensionPresentation X).p_comp_cokernelMap])
  -- The `K` projection equalities change both endpoints; heterogeneous equality inserts exactly
  -- those transports without unfolding the now-opaque presentation.
  apply eq_of_heq
  exact (comp_eqToHom_heq _ _).trans <|
    (heq_of_eq h.symm).trans (eqToHom_comp_heq _ _).symm

/-- Naturality of the comparison with the suspension, at the mapped suspension presentations:
the image under `F` of the map induced by `f` between the chosen suspension presentations is
carried to the map induced by `F.map f` between the chosen suspension presentations of the
images. -/
@[reassoc]
private theorem projectiveStableIsoSuspensionObj_hom_naturality_mapSuspensionPresentation
    (hF : StableConflationExact E E' F) (hE : E.IsFrobenius) (hE' : E'.IsFrobenius)
    {X Y : C} (f : X ⟶ Y) :
    E'.projectiveStableFunctor.map
          (F.map ((hE.suspensionPresentation X).cokernelMap (hE.suspensionPresentation Y) f)) ≫
        eqToHom (congrArg E'.projectiveStableFunctor.obj
          (hF.mapSuspensionPresentation_K hE Y).symm) ≫
          (hE'.projectiveStableIsoSuspensionObj (hF.mapSuspensionPresentation hE Y)).hom =
      eqToHom (congrArg E'.projectiveStableFunctor.obj
          (hF.mapSuspensionPresentation_K hE X).symm) ≫
        (hE'.projectiveStableIsoSuspensionObj (hF.mapSuspensionPresentation hE X)).hom ≫
        E'.projectiveStableFunctor.map ((hE'.suspensionPresentation (F.obj X)).cokernelMap
          (hE'.suspensionPresentation (F.obj Y)) (F.map f)) := by
  have h := hE'.projectiveStableIsoSuspensionObj_hom_naturality
    (hF.mapSuspensionPresentation hE X) (hF.mapSuspensionPresentation hE Y) (F.map f)
  rw [← Category.assoc,
    projectiveStableFunctor_map_mapSuspensionPresentation_cokernelMap
      (hF := hF) (hE := hE) f]
  rw [Category.assoc, h]

/-- The stable functor induced by a stable conflation-exact functor commutes with suspension.
Its component at `X` is the canonical comparison from the image of the chosen suspension
presentation of `X` to the chosen suspension presentation of `F.obj X`. -/
noncomputable def stableSuspensionCompStableFunctorIso (hF : StableConflationExact E E' F)
    (hE : E.IsFrobenius) (hE' : E'.IsFrobenius) :
    hE.stableSuspension ⋙ hF.stableFunctor hE ≅
      hF.stableFunctor hE ⋙ hE'.stableSuspension :=
  CategoryTheory.Quotient.natIsoLift _ <| NatIso.ofComponents (fun X ↦
    eqToIso (congrArg (hF.stableFunctor hE).obj
      (hE.stableSuspension_obj_projectiveStableFunctor_obj X)) ≪≫
    eqToIso (hF.stableFunctor_obj_projectiveStableFunctor_obj hE (hE.suspensionObj X)) ≪≫
    eqToIso (congrArg E'.projectiveStableFunctor.obj
      (hF.mapSuspensionPresentation_K hE X).symm) ≪≫
      hE'.projectiveStableIsoSuspensionObj (hF.mapSuspensionPresentation hE X) ≪≫
    eqToIso (hE'.stableSuspension_obj_projectiveStableFunctor_obj (F.obj X)).symm ≪≫
    eqToIso (congrArg hE'.stableSuspension.obj
      (hF.stableFunctor_obj_projectiveStableFunctor_obj hE X)).symm) (fun {X Y} f ↦ by
          simp only [Functor.comp_map, Functor.map_comp, Iso.trans_hom,
            eqToIso.hom, eqToHom_map, eqToHom_trans, eqToHom_trans_assoc,
            Category.assoc,
            ExactStructure.IsFrobenius.stableSuspension_map_projectiveStableFunctor_map]
          rw [hF.stableFunctor_map_projectiveStableFunctor_map_eq hE f]
          simp only [Functor.map_comp, eqToHom_map, Category.assoc,
            ExactStructure.IsFrobenius.stableSuspension_map_projectiveStableFunctor_map,
            eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
          rw [hF.stableFunctor_map_projectiveStableFunctor_map_eq hE
            ((hE.suspensionPresentation X).cokernelMap (hE.suspensionPresentation Y) f)]
          simp only [Category.assoc, eqToHom_trans_assoc]
          rw [projectiveStableIsoSuspensionObj_hom_naturality_mapSuspensionPresentation_assoc
            (hF := hF) (hE := hE) (hE' := hE') f]
          simp only [eqToHom_trans, eqToHom_trans_assoc])

/-- On an object represented by `X`, the suspension comparison is the canonical comparison
between the mapped suspension presentation and the chosen presentation of `F.obj X`. -/
@[simp]
theorem stableSuspensionCompStableFunctorIso_hom_app
    (hF : StableConflationExact E E' F) (hE : E.IsFrobenius) (hE' : E'.IsFrobenius) (X : C) :
    (hF.stableSuspensionCompStableFunctorIso hE hE').hom.app
        (E.projectiveStableFunctor.obj X) =
      eqToHom (congrArg (hF.stableFunctor hE).obj
        (hE.stableSuspension_obj_projectiveStableFunctor_obj X)) ≫
      eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE (hE.suspensionObj X)) ≫
      eqToHom (congrArg E'.projectiveStableFunctor.obj
        (hF.mapSuspensionPresentation_K hE X).symm) ≫
      (hE'.projectiveStableIsoSuspensionObj (hF.mapSuspensionPresentation hE X)).hom ≫
      eqToHom (hE'.stableSuspension_obj_projectiveStableFunctor_obj (F.obj X)).symm ≫
      eqToHom (congrArg hE'.stableSuspension.obj
        (hF.stableFunctor_obj_projectiveStableFunctor_obj hE X)).symm := by
  simp [stableSuspensionCompStableFunctorIso]

/-- On an object represented by `X`, the inverse suspension comparison is the inverse canonical
comparison, with the object-identification maps reversed. -/
@[simp]
theorem stableSuspensionCompStableFunctorIso_inv_app
    (hF : StableConflationExact E E' F) (hE : E.IsFrobenius) (hE' : E'.IsFrobenius) (X : C) :
    (hF.stableSuspensionCompStableFunctorIso hE hE').inv.app
        (E.projectiveStableFunctor.obj X) =
      eqToHom (congrArg hE'.stableSuspension.obj
        (hF.stableFunctor_obj_projectiveStableFunctor_obj hE X)) ≫
      eqToHom (hE'.stableSuspension_obj_projectiveStableFunctor_obj (F.obj X)) ≫
      (hE'.projectiveStableIsoSuspensionObj (hF.mapSuspensionPresentation hE X)).inv ≫
      eqToHom (congrArg E'.projectiveStableFunctor.obj
        (hF.mapSuspensionPresentation_K hE X)) ≫
      eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE (hE.suspensionObj X)).symm ≫
      eqToHom (congrArg (hF.stableFunctor hE).obj
        (hE.stableSuspension_obj_projectiveStableFunctor_obj X)).symm := by
  simp [stableSuspensionCompStableFunctorIso]

/-- On the class of an object `A`, the suspension comparison of the stable functor is the
connecting map of the image of the suspension presentation of `A`. -/
theorem stableSuspensionCompStableFunctorIso_hom_app_eq_connectingMap
    (hF : StableConflationExact E E' F) (hE : E.IsFrobenius) (hE' : E'.IsFrobenius) (A : C) :
    (hF.stableSuspensionCompStableFunctorIso hE hE').hom.app (E.projectiveStableFunctor.obj A) =
      eqToHom (congrArg (hF.stableFunctor hE).obj
        (hE.stableSuspension_obj_projectiveStableFunctor_obj A)) ≫
      eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE (hE.suspensionObj A)) ≫
      E'.projectiveStableFunctor.map (hE'.connectingMap
        (hF.isConflationExact.map_conflation (hE.suspensionPresentation A).conflation)) ≫
      eqToHom (hE'.stableSuspension_obj_projectiveStableFunctor_obj (F.obj A)).symm ≫
      eqToHom (congrArg hE'.stableSuspension.obj
        (hF.stableFunctor_obj_projectiveStableFunctor_obj hE A)).symm := by
  have hc : E'.projectiveStableFunctor.map
      (F.map (hE.connectingMap (hE.suspensionPresentation A).conflation)) = 𝟙 _ := by
    have h := hF.stableFunctor_map_projectiveStableFunctor_map hE
      (hE.connectingMap (hE.suspensionPresentation A).conflation)
    rw [hE.projectiveStableFunctor_map_connectingMap_suspensionPresentation,
      CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact (cancel_epi (eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE _))).1
      (h.symm.trans (Category.comp_id _).symm)
  have h := hF.map_connectingMap_comp_suspensionComparison hE hE'
    (hE.suspensionPresentation A).conflation
  rw [hc, Category.id_comp] at h
  rw [stableSuspensionCompStableFunctorIso_hom_app,
    ExactStructure.IsFrobenius.projectiveStableIsoSuspensionObj_hom, reassoc_of% h]

section Composition

variable {K : Type u₃} [Category.{v₃} K] [Preadditive K] [HasZeroObject K] [HasBinaryBiproducts K]
  {E'' : ExactStructure K} {G : Functor D K} [G.Additive]

/-- Comparing mapped suspension presentations along a composition `F ⋙ G`: the comparison from
the composite mapped presentation `(hF.comp hG).mapSuspensionPresentation hE X` to the target
suspension presentation factors through `G` applied to `hF`'s comparison and `hG`'s comparison. -/
private theorem projectiveStableIsoSuspensionObj_hom_mapSuspensionPresentation_comp
    (hF : StableConflationExact E E' F) (hG : StableConflationExact E' E'' G)
    (hE : E.IsFrobenius) (hE' : E'.IsFrobenius) (hE'' : E''.IsFrobenius) (X : C) :
    eqToHom (congrArg E''.projectiveStableFunctor.obj
      ((hF.comp hG).mapSuspensionPresentation_K hE X).symm) ≫
      (hE''.projectiveStableIsoSuspensionObj
        ((hF.comp hG).mapSuspensionPresentation hE X)).hom =
      eqToHom (congrArg E''.projectiveStableFunctor.obj
        (congrArg G.obj (hF.mapSuspensionPresentation_K hE X).symm)) ≫
      E''.projectiveStableFunctor.map (G.map
        ((hF.mapSuspensionPresentation hE X).cokernelMap
          (hE'.suspensionPresentation (F.obj X)) (𝟙 _))) ≫
      eqToHom (congrArg E''.projectiveStableFunctor.obj
        (hG.mapSuspensionPresentation_K hE' (F.obj X)).symm) ≫
      (hE''.projectiveStableIsoSuspensionObj
        (hG.mapSuspensionPresentation hE' (F.obj X))).hom := by
  let P₁ := hF.mapSuspensionPresentation hE X
  let Q₁ := hE'.suspensionPresentation (F.obj X)
  let P₂ := hG.mapSuspensionPresentation hE' (F.obj X)
  let Q₂ := hE''.suspensionPresentation (G.obj (F.obj X))
  let P₁₂ := (hF.comp hG).mapSuspensionPresentation hE X
  have hp1K : P₁₂.K = G.obj P₁.K :=
    ((hF.comp hG).mapSuspensionPresentation_K hE X).trans
      (congrArg G.obj (hF.mapSuspensionPresentation_K hE X).symm)
  have hp1I : P₁₂.I = G.obj P₁.I :=
    ((hF.comp hG).mapSuspensionPresentation_I hE X).trans
      (congrArg G.obj (hF.mapSuspensionPresentation_I hE X).symm)
  have hp2K : P₂.K = G.obj Q₁.K := hG.mapSuspensionPresentation_K hE' (F.obj X)
  have hp2I : P₂.I = G.obj Q₁.I := hG.mapSuspensionPresentation_I hE' (F.obj X)
  let a : P₁₂.I ⟶ Q₂.I :=
    eqToHom hp1I ≫ G.map (P₁.middleMap Q₁ (𝟙 _)) ≫ eqToHom hp2I.symm ≫ P₂.middleMap Q₂ (𝟙 _)
  let g : P₁₂.K ⟶ Q₂.K :=
    eqToHom hp1K ≫ G.map (P₁.cokernelMap Q₁ (𝟙 _)) ≫ eqToHom hp2K.symm ≫ P₂.cokernelMap Q₂ (𝟙 _)
  have ha : P₁₂.i ≫ a = 𝟙 _ ≫ Q₂.i := by
    have h₁ : G.map P₁.i ≫ G.map (P₁.middleMap Q₁ (𝟙 _)) = G.map Q₁.i := by
      rw [← G.map_comp, P₁.i_comp_middleMap, Category.id_comp]
    have hP1i := (conj_eqToHom_iff_heq _ _ rfl
      ((hF.comp hG).mapSuspensionPresentation_I hE X)).2
      ((hF.comp hG).mapSuspensionPresentation_i hE X)
    have hP1i' := (conj_eqToHom_iff_heq _ _ rfl
      (hF.mapSuspensionPresentation_I hE X)).2
      (hF.mapSuspensionPresentation_i hE X)
    have hP2i := (conj_eqToHom_iff_heq _ _ rfl hp2I).2
      (hG.mapSuspensionPresentation_i hE' (F.obj X))
    dsimp only [a, P₁₂, P₁, P₂]
    rw [Category.id_comp]
    calc
      ((hF.comp hG).mapSuspensionPresentation hE X).i ≫
          eqToHom hp1I ≫ G.map (P₁.middleMap Q₁ (𝟙 _)) ≫ eqToHom hp2I.symm ≫
            P₂.middleMap Q₂ (𝟙 _)
        = G.map (hF.mapSuspensionPresentation hE X).i ≫ G.map (P₁.middleMap Q₁ (𝟙 _)) ≫
            eqToHom hp2I.symm ≫ P₂.middleMap Q₂ (𝟙 _) := by
          simp only [hP1i, hP1i', Functor.comp_map, G.map_comp, eqToHom_map, Category.assoc,
            eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      _ = G.map Q₁.i ≫ eqToHom hp2I.symm ≫ P₂.middleMap Q₂ (𝟙 _) := by
          rw [← Category.assoc, h₁]
      _ = P₂.i ≫ P₂.middleMap Q₂ (𝟙 _) := by
          rw [hP2i]
          simp only [Category.assoc, eqToHom_refl, Category.id_comp]
          rfl
      _ = Q₂.i := by rw [P₂.i_comp_middleMap, Category.id_comp]
  have hg : P₁₂.p ≫ g = a ≫ Q₂.p := by
    have h₁ : G.map P₁.p ≫ G.map (P₁.cokernelMap Q₁ (𝟙 _)) =
        G.map (P₁.middleMap Q₁ (𝟙 _)) ≫ G.map Q₁.p := by
      rw [← G.map_comp, P₁.p_comp_cokernelMap, G.map_comp]
    have hP12p := (conj_eqToHom_iff_heq _ _
      ((hF.comp hG).mapSuspensionPresentation_I hE X)
      ((hF.comp hG).mapSuspensionPresentation_K hE X)).2
      ((hF.comp hG).mapSuspensionPresentation_p hE X)
    have hP1p := (conj_eqToHom_iff_heq _ _
      (hF.mapSuspensionPresentation_I hE X)
      (hF.mapSuspensionPresentation_K hE X)).2
      (hF.mapSuspensionPresentation_p hE X)
    have hP2p := (conj_eqToHom_iff_heq _ _ hp2I hp2K).2
      (hG.mapSuspensionPresentation_p hE' (F.obj X))
    dsimp only [a, g]
    calc
      P₁₂.p ≫
          eqToHom hp1K ≫ G.map (P₁.cokernelMap Q₁ (𝟙 _)) ≫ eqToHom hp2K.symm ≫
            P₂.cokernelMap Q₂ (𝟙 _)
        = eqToHom hp1I ≫ G.map P₁.p ≫ G.map (P₁.cokernelMap Q₁ (𝟙 _)) ≫
            eqToHom hp2K.symm ≫ P₂.cokernelMap Q₂ (𝟙 _) := by
          rw [hP12p, hP1p]
          simp only [Functor.comp_map, G.map_comp, eqToHom_map, Category.assoc,
            eqToHom_trans_assoc]
      _ = eqToHom hp1I ≫ G.map (P₁.middleMap Q₁ (𝟙 _)) ≫ G.map Q₁.p ≫
            eqToHom hp2K.symm ≫ P₂.cokernelMap Q₂ (𝟙 _) := by
          rw [reassoc_of% h₁]
      _ = eqToHom hp1I ≫ G.map (P₁.middleMap Q₁ (𝟙 _)) ≫ eqToHom hp2I.symm ≫
            P₂.p ≫ P₂.cokernelMap Q₂ (𝟙 _) := by
          rw [hP2p]
          simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
          rfl
      _ = a ≫ Q₂.p := by
          simp only [a, Category.assoc, P₂.p_comp_cokernelMap]
  have hcmp := E''.projectiveStableFunctor_map_cokernelMap_eq P₁₂ Q₂
    (hE''.isProjective_I Q₂) (𝟙 _) a g ha hg
  dsimp only [Q₂] at hcmp
  change E''.projectiveStableFunctor.map (P₁₂.cokernelMap
      (hE''.suspensionPresentation ((F ⋙ G).obj X)) (𝟙 ((F ⋙ G).obj X))) =
    E''.projectiveStableFunctor.map g at hcmp
  rw [← hE''.projectiveStableIsoSuspensionObj_hom P₁₂] at hcmp
  dsimp only [g, Q₂] at hcmp
  simp only [Functor.map_comp, eqToHom_map] at hcmp
  rw [← hE''.projectiveStableIsoSuspensionObj_hom P₂] at hcmp
  simpa only [eqToHom_trans_assoc, Category.assoc, eqToHom_map] using
    congrArg (eqToHom (congrArg E''.projectiveStableFunctor.obj
      ((hF.comp hG).mapSuspensionPresentation_K hE X).symm) ≫ ·) hcmp

/-- The suspension comparison of a composite stable conflation-exact functor factors through the
suspension comparisons of its two factors and the composition equality `stableFunctor_comp`. -/
theorem stableSuspensionCompStableFunctorIso_comp
    (hF : StableConflationExact E E' F) (hG : StableConflationExact E' E'' G)
    (hE : E.IsFrobenius) (hE' : E'.IsFrobenius) (hE'' : E''.IsFrobenius) :
    (Functor.isoWhiskerLeft hE.stableSuspension
        (eqToIso (hF.stableFunctor_comp hG hE hE'))).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (hF.stableSuspensionCompStableFunctorIso hE hE').hom
        (hG.stableFunctor hE') ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (hF.stableFunctor hE)
        (hG.stableSuspensionCompStableFunctorIso hE' hE'').hom ≫
      (Functor.associator _ _ _).inv =
    ((hF.comp hG).stableSuspensionCompStableFunctorIso hE hE'').hom ≫
      Functor.whiskerRight (eqToIso (hF.stableFunctor_comp hG hE hE')).hom
        hE''.stableSuspension := by
  apply CategoryTheory.Quotient.natTrans_ext
  ext X
  simp only [NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Functor.associator_hom_app,
    eqToIso.hom, eqToHom_app, Functor.comp_obj, Category.id_comp, Category.comp_id]
  have hIsoG :
      (hG.stableSuspensionCompStableFunctorIso hE' hE'').hom.app
          ((hF.stableFunctor hE).obj (E.projectiveStableFunctor.obj X)) =
        eqToHom (congrArg (hG.stableFunctor hE').obj (congrArg hE'.stableSuspension.obj
          (hF.stableFunctor_obj_projectiveStableFunctor_obj hE X))) ≫
          (hG.stableSuspensionCompStableFunctorIso hE' hE'').hom.app
            (E'.projectiveStableFunctor.obj (F.obj X)) ≫
          eqToHom (congrArg hE''.stableSuspension.obj (congrArg (hG.stableFunctor hE').obj
            (hF.stableFunctor_obj_projectiveStableFunctor_obj hE X).symm)) := by
    have hn := (hG.stableSuspensionCompStableFunctorIso hE' hE'').hom.naturality
      (eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE X))
    dsimp only [Functor.comp_obj, Functor.comp_map] at hn
    simp only [eqToHom_map] at hn
    rw [← cancel_mono (eqToHom (congrArg hE''.stableSuspension.obj
      (congrArg (hG.stableFunctor hE').obj
        (hF.stableFunctor_obj_projectiveStableFunctor_obj hE X)))),
      Category.assoc, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    exact hn.symm
  rw [(hF.comp hG).stableSuspensionCompStableFunctorIso_hom_app hE hE'' X,
    hF.stableSuspensionCompStableFunctorIso_hom_app hE hE' X,
    hIsoG, hG.stableSuspensionCompStableFunctorIso_hom_app hE' hE'' (F.obj X)]
  let P₁ := hF.mapSuspensionPresentation hE X
  let Q₁ := hE'.suspensionPresentation (F.obj X)
  have hmap :
      (hG.stableFunctor hE').map ((hE'.projectiveStableIsoSuspensionObj P₁).hom) =
        eqToHom (hG.stableFunctor_obj_projectiveStableFunctor_obj hE' P₁.K) ≫
          E''.projectiveStableFunctor.map (G.map (P₁.cokernelMap Q₁ (𝟙 _))) ≫
          eqToHom (hG.stableFunctor_obj_projectiveStableFunctor_obj hE'
            (hE'.suspensionObj (F.obj X))).symm := by
    rw [hE'.projectiveStableIsoSuspensionObj_hom P₁]
    exact hG.stableFunctor_map_projectiveStableFunctor_map_eq hE' (P₁.cokernelMap Q₁ (𝟙 _))
  simp only [Functor.map_comp, eqToHom_map, Category.assoc]
  rw [show (hG.stableFunctor hE').map
      (hE'.projectiveStableIsoSuspensionObj (hF.mapSuspensionPresentation hE X)).hom = _ from hmap]
  simp only [Category.assoc]
  have hpre :
      eqToHom (congrArg (hG.stableFunctor hE').obj
        (congrArg E'.projectiveStableFunctor.obj (hF.mapSuspensionPresentation_K hE X).symm)) ≫
      eqToHom (hG.stableFunctor_obj_projectiveStableFunctor_obj hE' P₁.K) =
        eqToHom (hG.stableFunctor_obj_projectiveStableFunctor_obj hE'
          (F.obj (hE.suspensionObj X))) ≫
        eqToHom (congrArg E''.projectiveStableFunctor.obj
          (congrArg G.obj (hF.mapSuspensionPresentation_K hE X).symm)) := by
    simp only [eqToHom_trans]
  have hpost :
      eqToHom (hG.stableFunctor_obj_projectiveStableFunctor_obj hE'
        (hE'.suspensionObj (F.obj X))).symm ≫
      eqToHom (congrArg (hG.stableFunctor hE').obj
        (hE'.stableSuspension_obj_projectiveStableFunctor_obj (F.obj X)).symm) ≫
      eqToHom (congrArg (hG.stableFunctor hE').obj (congrArg hE'.stableSuspension.obj
        (hF.stableFunctor_obj_projectiveStableFunctor_obj hE X)).symm) ≫
      eqToHom (congrArg (hG.stableFunctor hE').obj (congrArg hE'.stableSuspension.obj
        (hF.stableFunctor_obj_projectiveStableFunctor_obj hE X))) ≫
      eqToHom (congrArg (hG.stableFunctor hE').obj
        (hE'.stableSuspension_obj_projectiveStableFunctor_obj (F.obj X))) ≫
      eqToHom (hG.stableFunctor_obj_projectiveStableFunctor_obj hE'
        (hE'.suspensionObj (F.obj X))) = 𝟙 _ := by
    simp only [eqToHom_trans, eqToHom_refl]
  rw [reassoc_of% hpost]
  rw [← Category.assoc (eqToHom (congrArg (hG.stableFunctor hE').obj
      (congrArg E'.projectiveStableFunctor.obj (hF.mapSuspensionPresentation_K hE X).symm)))]
  rw [hpre]
  simp only [Category.assoc]
  have hcmp := projectiveStableIsoSuspensionObj_hom_mapSuspensionPresentation_comp
    hF hG hE hE' hE'' X
  have hcmp' :
      eqToHom (congrArg E''.projectiveStableFunctor.obj
        (congrArg G.obj (hF.mapSuspensionPresentation_K hE X).symm)) ≫
      E''.projectiveStableFunctor.map (G.map (P₁.cokernelMap Q₁ (𝟙 _))) ≫
      eqToHom (congrArg E''.projectiveStableFunctor.obj
        (hG.mapSuspensionPresentation_K hE' (F.obj X)).symm) ≫
      (hE''.projectiveStableIsoSuspensionObj (hG.mapSuspensionPresentation hE' (F.obj X))).hom =
      eqToHom (congrArg E''.projectiveStableFunctor.obj
        ((hF.comp hG).mapSuspensionPresentation_K hE X).symm) ≫
      (hE''.projectiveStableIsoSuspensionObj
        ((hF.comp hG).mapSuspensionPresentation hE X)).hom :=
    hcmp.symm
  rw [reassoc_of% hcmp']
  simp only [eqToHom_trans_assoc, eqToHom_trans]

end Composition

end StableConflationExact

end TauCeti
