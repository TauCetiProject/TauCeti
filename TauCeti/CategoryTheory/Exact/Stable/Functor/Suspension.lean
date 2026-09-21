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
stable functor and suspension.

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

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
-/

public section

universe v₁ v₂ u₁ u₂

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
          have hmapF {A B : C} (g : A ⟶ B) :
              (hF.stableFunctor hE).map (E.projectiveStableFunctor.map g) =
                eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE A) ≫
                  E'.projectiveStableFunctor.map (F.map g) ≫
                    eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE B).symm := by
            apply (cancel_mono
              (eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE B))).1
            simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using
              hF.stableFunctor_map_projectiveStableFunctor_map hE g
          simp only [Functor.comp_map, Functor.map_comp, Iso.trans_hom,
            eqToIso.hom, eqToHom_map, eqToHom_trans, eqToHom_trans_assoc,
            Category.assoc,
            ExactStructure.IsFrobenius.stableSuspension_map_projectiveStableFunctor_map]
          rw [hmapF f]
          simp only [Functor.map_comp, eqToHom_map, Category.assoc,
            ExactStructure.IsFrobenius.stableSuspension_map_projectiveStableFunctor_map,
            eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
          rw [hmapF ((hE.suspensionPresentation X).cokernelMap
            (hE.suspensionPresentation Y) f)]
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

end StableConflationExact

end TauCeti
