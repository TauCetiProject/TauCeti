/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Cone
public import TauCeti.CategoryTheory.Exact.HomologicalComplex.HomotopyCategory
public import TauCeti.CategoryTheory.Exact.Stable.Suspension

/-!
# Stable suspension is the signed periodic shift

The componentwise split exact category of cyclic cochain complexes is Frobenius. Its
suspension can be computed from the conflation `X ⟶ cone(id_X) ⟶ X⟦1⟧`: the middle term is
contractible, hence relatively injective and projective. The resulting identification is
natural, since a chain map induces a map of these cone sequences whose cokernel component
is its signed shift.

This file identifies stable suspension with the signed cyclic shift and shows that the
canonical stable-to-homotopy equivalence intertwines suspension with the existing shift by
one on the periodic homotopy category. This identifies the translation functors needed to
compare the stable triangulation with mapping-cone triangles; it does not yet identify their
distinguished triangles.

No positivity hypothesis on the period is needed: at period zero these constructions apply
to integer-indexed cochain complexes.

## References

* B. Keller, *Chain complexes and stable categories*, Manuscripta Mathematica **67**
  (1990), 379–417, Section 1.
* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.

The presentation comparison is `ExactStructure.IsFrobenius.projectiveStableIsoSuspensionObj`.
The natural-isomorphism construction follows the analogous finite-projective duplex
comparison in `TauCeti.CommutativeAlgebra.MatrixFactorization.Shift`.
-/

public section

universe v u

namespace TauCeti.PeriodicComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {n : ℕ}

local notation "E" => ExactStructure.homologicalComplex (ExactStructure.split C)
  (ComplexShape.up (ZMod n))
local notation "hE" => ExactStructure.homologicalComplex_split_isFrobenius
  (C := C) (c := ComplexShape.up (ZMod n))
  (fun j => Exists.intro (j - 1) (sub_add_cancel j 1))
  (fun i => Exists.intro (i + 1) rfl)

/-- The identity-cone injective presentation of a periodic complex. Its cokernel is the
signed cyclic shift, and its middle term is contractible. -/
-- The presentation's endpoints must compute when typing maps between presentations.
@[expose] noncomputable def coneInjectivePresentation (X : CochainComplex C (ZMod n)) :
    (E).InjectivePresentation X where
  I := homotopyCofiber (𝟙 X)
  K := X⟦(1 : ℤ)⟧
  i := homotopyCofiber.inr (𝟙 X)
  p := coneProjection (𝟙 X)
  zero := coneInclusion_comp_coneProjection (𝟙 X)
  conflation := conflation_coneSequence (ExactStructure.split C) (𝟙 X)
  isInjective := ExactStructure.homologicalComplex_split_isInjective_of_homotopy
    (homotopyCofiber.homotopyToZeroOfId X (fun j => ⟨j - 1, by simp⟩))

@[simp] theorem coneInjectivePresentation_I (X : CochainComplex C (ZMod n)) :
    (coneInjectivePresentation X).I = homotopyCofiber (𝟙 X) := (rfl)

@[simp] theorem coneInjectivePresentation_K (X : CochainComplex C (ZMod n)) :
    (coneInjectivePresentation X).K = X⟦(1 : ℤ)⟧ := (rfl)

@[simp] theorem coneInjectivePresentation_i (X : CochainComplex C (ZMod n)) :
    (coneInjectivePresentation X).i = homotopyCofiber.inr (𝟙 X) := (rfl)

@[simp] theorem coneInjectivePresentation_p (X : CochainComplex C (ZMod n)) :
    (coneInjectivePresentation X).p = coneProjection (𝟙 X) := (rfl)

/-- The map induced on the cokernels of identity-cone presentations is the signed shift of
the original chain map, in the projective stable category. -/
@[simp]
theorem projectiveStableFunctor_map_coneInjectivePresentation_cokernelMap
    {X Y : CochainComplex C (ZMod n)} (f : X ⟶ Y) :
    (E).projectiveStableFunctor.map
        ((coneInjectivePresentation X).cokernelMap (coneInjectivePresentation Y) f) =
      (E).projectiveStableFunctor.map (f⟦(1 : ℤ)⟧') := by
  let α : Arrow.mk (𝟙 X) ⟶ Arrow.mk (𝟙 Y) := Arrow.homMk f f (by simp)
  apply ExactStructure.projectiveStableFunctor_map_cokernelMap_eq
    (coneInjectivePresentation X) (coneInjectivePresentation Y)
    ((hE).isProjective_I (coneInjectivePresentation Y)) f
    (homotopyCofiber.mapArrowHom (𝟙 X) (𝟙 Y) (fun j => ⟨j - 1, by simp⟩) α)
    (f⟦(1 : ℤ)⟧')
  · -- Reduce the presentation endpoints to align the dependent hom-group instances.
    dsimp only [coneInjectivePresentation]
    exact homotopyCofiber.inr_mapArrowHom _ _ _ α
  · dsimp only [coneInjectivePresentation]
    exact (mapArrowHom_comp_coneProjection _ _ α).symm

variable (C n)

/-- Stable suspension of the componentwise split exact category is naturally the image of
the signed cyclic shift. -/
noncomputable def splitStableSuspensionIsoShift :
    (E).projectiveStableFunctor ⋙ (hE).stableSuspension ≅
      CategoryTheory.shiftFunctor (CochainComplex C (ZMod n)) (1 : ℤ) ⋙
        (E).projectiveStableFunctor :=
  (NatIso.ofComponents (fun X => Iso.trans
    (X := (CategoryTheory.shiftFunctor (CochainComplex C (ZMod n)) (1 : ℤ) ⋙
      (E).projectiveStableFunctor).obj X)
    (Z := ((E).projectiveStableFunctor ⋙ (hE).stableSuspension).obj X)
    ((hE).projectiveStableIsoSuspensionObj (coneInjectivePresentation X))
    (eqToIso ((hE).stableSuspension_obj_projectiveStableFunctor_obj X).symm))
    (fun {X Y} f => by
      have h := (hE).projectiveStableIsoSuspensionObj_hom_naturality
        (coneInjectivePresentation X) (coneInjectivePresentation Y) f
      rw [projectiveStableFunctor_map_coneInjectivePresentation_cokernelMap] at h
      rw [Functor.comp_map, Functor.comp_map,
        ExactStructure.IsFrobenius.stableSuspension_map_projectiveStableFunctor_map]
      -- The isomorphism endpoints are displayed as composite-functor objects. Reduction
      -- aligns them with the presentation endpoints so that the component lemmas apply.
      erw [Iso.trans_hom, Iso.trans_hom]
      rw [eqToIso.hom, eqToIso.hom]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      exact (Category.assoc _ _ _).symm.trans ((reassoc_of% h) _))).symm

/-- The suspension comparison is induced by the identity from the chosen injective
presentation to the identity-cone presentation. -/
@[simp]
theorem splitStableSuspensionIsoShift_hom_app (X : CochainComplex C (ZMod n)) :
    (splitStableSuspensionIsoShift C n).hom.app X =
      eqToHom ((hE).stableSuspension_obj_projectiveStableFunctor_obj X) ≫
        (E).projectiveStableFunctor.map
          (((hE).suspensionPresentation X).cokernelMap (coneInjectivePresentation X) (𝟙 X)) := by
  simp only [splitStableSuspensionIsoShift, Iso.symm_hom, NatIso.ofComponents_inv_app]
  -- Align the composite-functor endpoints as in the definition.
  erw [Iso.trans_inv]
  rw [eqToIso.inv, ExactStructure.IsFrobenius.projectiveStableIsoSuspensionObj_inv]
  rfl

/-- The inverse suspension comparison is induced by the identity in the other direction. -/
@[simp]
theorem splitStableSuspensionIsoShift_inv_app (X : CochainComplex C (ZMod n)) :
    (splitStableSuspensionIsoShift C n).inv.app X =
      (E).projectiveStableFunctor.map
          ((coneInjectivePresentation X).cokernelMap ((hE).suspensionPresentation X) (𝟙 X)) ≫
        eqToHom ((hE).stableSuspension_obj_projectiveStableFunctor_obj X).symm := by
  simp only [splitStableSuspensionIsoShift, Iso.symm_inv, NatIso.ofComponents_hom_app]
  -- Align the composite-functor endpoints as in the definition.
  erw [Iso.trans_hom]
  rw [eqToIso.hom, ExactStructure.IsFrobenius.projectiveStableIsoSuspensionObj_hom]
  rfl

/-- The stable-to-homotopy equivalence intertwines stable suspension with the existing
signed shift by one on the periodic homotopy category. -/
noncomputable def stableSuspensionCompStableToHomotopyIso :
    (hE).stableSuspension ⋙ ExactStructure.homologicalComplexSplitStableToHomotopy C
        (ComplexShape.up (ZMod n)) (fun i => ⟨i + 1, rfl⟩) ≅
      ExactStructure.homologicalComplexSplitStableToHomotopy C
        (ComplexShape.up (ZMod n)) (fun i => ⟨i + 1, rfl⟩) ⋙
          CategoryTheory.shiftFunctor (HomotopyCategory C (ComplexShape.up (ZMod n))) (1 : ℤ) :=
  Quotient.natIsoLift _ <|
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (splitStableSuspensionIsoShift C n) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (eqToIso
        (ExactStructure.projectiveStableFunctor_comp_homologicalComplexSplitStableToHomotopy
          C (ComplexShape.up (ZMod n)) (fun i => ⟨i + 1, rfl⟩))) ≪≫
      (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).commShiftIso (1 : ℤ) ≪≫
      Functor.isoWhiskerRight (eqToIso
        (ExactStructure.projectiveStableFunctor_comp_homologicalComplexSplitStableToHomotopy
          C (ComplexShape.up (ZMod n)) (fun i => ⟨i + 1, rfl⟩)).symm) _ ≪≫
      Functor.associator _ _ _

/-- On a represented complex, the intertwining isomorphism is the image of the suspension
comparison, followed by the quotient's shift comparison. -/
@[simp]
theorem stableSuspensionCompStableToHomotopyIso_hom_app (X : CochainComplex C (ZMod n)) :
    (stableSuspensionCompStableToHomotopyIso C n).hom.app
        ((E).projectiveStableFunctor.obj X) =
      (ExactStructure.homologicalComplexSplitStableToHomotopy C
        (ComplexShape.up (ZMod n)) (fun i => ⟨i + 1, rfl⟩)).map
          ((splitStableSuspensionIsoShift C n).hom.app X) ≫
        eqToHom (by simp only [Functor.comp_obj,
          ExactStructure.homologicalComplexSplitStableToHomotopy_obj]) ≫
          ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).commShiftIso
            (1 : ℤ)).hom.app X ≫
            eqToHom (by simp only [Functor.comp_obj,
              ExactStructure.homologicalComplexSplitStableToHomotopy_obj, shift_quotient_obj]) := by
  simp [stableSuspensionCompStableToHomotopyIso, eqToHom_map]

/-- The inverse intertwining comparison uses the inverse quotient shift comparison and
then the image of the inverse suspension comparison. -/
@[simp]
theorem stableSuspensionCompStableToHomotopyIso_inv_app (X : CochainComplex C (ZMod n)) :
    (stableSuspensionCompStableToHomotopyIso C n).inv.app
        ((E).projectiveStableFunctor.obj X) =
      eqToHom (by simp only [Functor.comp_obj,
        ExactStructure.homologicalComplexSplitStableToHomotopy_obj, shift_quotient_obj]) ≫
        ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).commShiftIso (1 : ℤ)).inv.app X ≫
          eqToHom (by simp only [Functor.comp_obj,
            ExactStructure.homologicalComplexSplitStableToHomotopy_obj]) ≫
            (ExactStructure.homologicalComplexSplitStableToHomotopy C
              (ComplexShape.up (ZMod n)) (fun i => ⟨i + 1, rfl⟩)).map
                ((splitStableSuspensionIsoShift C n).inv.app X) := by
  simp [stableSuspensionCompStableToHomotopyIso, eqToHom_map]

end TauCeti.PeriodicComplex
