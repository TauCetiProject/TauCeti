/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.Suspension
public import TauCeti.CategoryTheory.Exact.Stable.Pretriangulated

/-!
# Connecting maps of periodic cone conflations

The identity-cone presentation computes suspension in the componentwise split exact category
of periodic complexes. This file computes connecting maps through that presentation and
expresses Happel's conflation triangles using the signed cyclic shift of actual complexes.
In particular, the conflation `Y ⟶ cone(f) ⟶ X⟦1⟧` has connecting map `f⟦1⟧`, after identifying
the two suspension objects. Rotation then shows that the usual mapping-cone triangle is
distinguished in the stable category.

The cone differential has lower-left block `f`. Thus the connecting map of this cone
*conflation* is positive; the last map of the usual triangle `X ⟶ Y ⟶ cone(f) ⟶ X⟦1⟧` has
minus the cone projection, as required by rotation. The results here concern the stable
triangulation and do not install a triangulation on the periodic homotopy category.

These comparisons apply to every positive period and also to the integer-indexed case
`ZMod 0`. The base category needs only a preadditive structure, a zero object, and binary
biproducts.

## References

* B. Keller, *Chain complexes and stable categories*, Manuscripta Mathematica **67**
  (1990), 379–417, Section 1.
* D. Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.

The construction uses `PeriodicComplex.splitStableSuspensionIsoShift` and the
presentation-independent connecting-map API
`ExactStructure.IsFrobenius.projectiveStableFunctor_map_eq_connectingMap_comp`.
-/

public section

universe v u

namespace TauCeti.PeriodicComplex

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {n : ℕ}

local notation "E" => ExactStructure.homologicalComplex (ExactStructure.split C)
  (ComplexShape.up (ZMod n))
local notation "hE" => ExactStructure.homologicalComplex_split_isFrobenius
  (C := C) (c := ComplexShape.up (ZMod n))
  (fun j => Exists.intro (j - 1) (by simp))
  (fun i => Exists.intro (i + 1) (by simp))

variable (C n)

/-- The stable image of the signed cyclic shift is isomorphic to the stable shift by one.
The isomorphism comes from the identity-cone injective presentation. -/
noncomputable def splitStableShiftObjIso (X : CochainComplex C (ZMod n)) :
    letI := (hE).stableHasShift
    (E).projectiveStableFunctor.obj (X⟦(1 : ℤ)⟧) ≅ ((E).projectiveStableFunctor.obj X)⟦(1 : ℤ)⟧ :=
  letI := (hE).stableHasShift
  ((splitStableSuspensionIsoShift C n).symm.app X) ≪≫
    ((hE).stableShiftFunctorOneIso.app ((E).projectiveStableFunctor.obj X)).symm

/-- The forward shift comparison passes through stable suspension. -/
@[simp]
theorem splitStableShiftObjIso_hom (X : CochainComplex C (ZMod n)) :
    letI := (hE).stableHasShift
    (splitStableShiftObjIso C n X).hom =
      (splitStableSuspensionIsoShift C n).inv.app X ≫
        (hE).stableShiftFunctorOneIso.inv.app ((E).projectiveStableFunctor.obj X) := (rfl)

/-- The inverse shift comparison passes from the stable shift through stable suspension. -/
@[simp]
theorem splitStableShiftObjIso_inv (X : CochainComplex C (ZMod n)) :
    letI := (hE).stableHasShift
    (splitStableShiftObjIso C n X).inv =
      (hE).stableShiftFunctorOneIso.hom.app ((E).projectiveStableFunctor.obj X) ≫
        (splitStableSuspensionIsoShift C n).hom.app X := (rfl)

variable {C n}

/-- The comparison between the two shifts is natural in periodic chain maps. -/
@[reassoc]
theorem splitStableShiftObjIso_hom_naturality {X Y : CochainComplex C (ZMod n)}
    (f : X ⟶ Y) :
    letI := (hE).stableHasShift
    (E).projectiveStableFunctor.map (f⟦(1 : ℤ)⟧') ≫ (splitStableShiftObjIso C n Y).hom =
      (splitStableShiftObjIso C n X).hom ≫ ((E).projectiveStableFunctor.map f)⟦(1 : ℤ)⟧' := by
  let := (hE).stableHasShift
  have h := (splitStableSuspensionIsoShift C n).inv.naturality f
  simp only [Functor.comp_map] at h
  simp only [splitStableShiftObjIso_hom, ← Category.assoc]
  rw [h, Category.assoc]
  simpa only [Category.assoc] using
    congrArg ((splitStableSuspensionIsoShift C n).inv.app X ≫ ·)
      ((hE).stableShiftFunctorOneIso.inv.naturality ((E).projectiveStableFunctor.map f))

variable {T : ShortComplex (CochainComplex C (ZMod n))}

/-- A connecting map computed with the identity-cone presentation agrees with Happel's
connecting map, after passing to the stable category and identifying the shifts. -/
theorem projectiveStableFunctor_map_comp_splitStableShiftObjIso
    (hT : (E).Conflation T) (a : T.X₂ ⟶ homotopyCofiber (𝟙 T.X₁))
    (δ : T.X₃ ⟶ T.X₁⟦(1 : ℤ)⟧)
    (ha : T.f ≫ a = homotopyCofiber.inr (𝟙 T.X₁))
    (hδ : T.g ≫ δ = a ≫ coneProjection (𝟙 T.X₁)) :
    letI := (hE).stableHasShift
    (E).projectiveStableFunctor.map δ ≫ (splitStableShiftObjIso C n T.X₁).hom =
      (E).projectiveStableFunctor.map ((hE).connectingMap hT) ≫
        ((hE).stableSuspensionObjIsoShift T.X₁).hom := by
  let := (hE).stableHasShift
  have h := (hE).projectiveStableFunctor_map_eq_connectingMap_comp hT
    (coneInjectivePresentation T.X₁) a δ ha hδ
  -- Align the presentation cokernel with the cyclic shift in the equality of homs.
  dsimp only [coneInjectivePresentation] at h
  rw [h, splitStableShiftObjIso_hom, splitStableSuspensionIsoShift_inv_app,
    ExactStructure.IsFrobenius.stableSuspensionObjIsoShift_hom,
    ExactStructure.IsFrobenius.projectiveStableIsoSuspensionObj_inv]
  -- The presentation cokernel is the cyclic shift; reducing it aligns the dependent homs.
  dsimp only [coneInjectivePresentation]
  simp only [Category.assoc]
  -- Imported comparison formulas retain the presentation endpoints in their hom instances.
  -- Reduce those instances when matching the composition law.
  erw [← reassoc_of% (ExactStructure.projectiveStableFunctor_map_cokernelMap_comp
    ((hE).suspensionPresentation T.X₁) (coneInjectivePresentation T.X₁)
    ((hE).suspensionPresentation T.X₁) ((hE).isProjective_I _) (𝟙 _) (𝟙 _))]
  erw [ExactStructure.projectiveStableFunctor_map_cokernelMap_id
    _ ((hE).isProjective_I _), Category.id_comp]

/-- The standard stable triangle of a componentwise split conflation can be written using
any connecting map computed through the identity cone. -/
theorem stableConflationTriangle_eq_mk_of_conePresentation
    (hT : (E).Conflation T) (a : T.X₂ ⟶ homotopyCofiber (𝟙 T.X₁))
    (δ : T.X₃ ⟶ T.X₁⟦(1 : ℤ)⟧)
    (ha : T.f ≫ a = homotopyCofiber.inr (𝟙 T.X₁))
    (hδ : T.g ≫ δ = a ≫ coneProjection (𝟙 T.X₁)) :
    letI := (hE).stableHasShift
    (hE).stableConflationTriangle T hT =
      Triangle.mk ((E).projectiveStableFunctor.map T.f) ((E).projectiveStableFunctor.map T.g)
      ((E).projectiveStableFunctor.map δ ≫ (splitStableShiftObjIso C n T.X₁).hom) := by
  let := (hE).stableHasShift
  rw [ExactStructure.IsFrobenius.stableConflationTriangle_eq_mk,
    projectiveStableFunctor_map_comp_splitStableShiftObjIso hT a δ ha hδ,
    ExactStructure.IsFrobenius.stableSuspensionObjIsoShift_hom]

/-- The connecting map of `Y ⟶ cone(f) ⟶ X⟦1⟧` is the signed shift of `f`, under the
identity-cone comparison of suspension objects. -/
theorem projectiveStableFunctor_map_shift_comp_splitStableShiftObjIso
    {X Y : CochainComplex C (ZMod n)} (f : X ⟶ Y) :
    letI := (hE).stableHasShift
    (E).projectiveStableFunctor.map (f⟦(1 : ℤ)⟧') ≫ (splitStableShiftObjIso C n Y).hom =
      (E).projectiveStableFunctor.map
          ((hE).connectingMap (conflation_coneSequence (ExactStructure.split C) f)) ≫
        ((hE).stableSuspensionObjIsoShift Y).hom := by
  let := (hE).stableHasShift
  let α : Arrow.mk f ⟶ Arrow.mk (𝟙 Y) := Arrow.homMk f (𝟙 Y) (by simp)
  apply projectiveStableFunctor_map_comp_splitStableShiftObjIso
    (conflation_coneSequence (ExactStructure.split C) f)
    (homotopyCofiber.mapArrowHom f (𝟙 Y) (fun j => ⟨j - 1, by simp⟩) α)
  · simp [coneSequence, α]
  · exact (mapArrowHom_comp_coneProjection f (𝟙 Y) α).symm

/-- The standard triangle of the cone conflation has the shifted original map as its
connecting arrow, expressed through the stable shift comparison. -/
theorem stableConflationTriangle_coneSequence_eq_mk
    {X Y : CochainComplex C (ZMod n)} (f : X ⟶ Y) :
    letI := (hE).stableHasShift
    (hE).stableConflationTriangle (coneSequence f)
        (conflation_coneSequence (ExactStructure.split C) f) =
      Triangle.mk ((E).projectiveStableFunctor.map (homotopyCofiber.inr f))
        ((E).projectiveStableFunctor.map (coneProjection f))
        ((E).projectiveStableFunctor.map (f⟦(1 : ℤ)⟧') ≫
          (splitStableShiftObjIso C n Y).hom) := by
  let := (hE).stableHasShift
  rw [projectiveStableFunctor_map_shift_comp_splitStableShiftObjIso,
    ExactStructure.IsFrobenius.stableSuspensionObjIsoShift_hom,
    ExactStructure.IsFrobenius.stableConflationTriangle_eq_mk]
  simp only [coneSequence_f, coneSequence_g]
  -- The remaining dependent endpoint is the first object of the cone short complex.
  rfl

/-- The periodic cone conflation gives a distinguished stable triangle with explicit
connecting map `f⟦1⟧`. -/
theorem coneSequence_distinguished {X Y : CochainComplex C (ZMod n)} (f : X ⟶ Y) :
    letI := (hE).stableHasShift
    letI := (hE).stableShiftFunctor_additive
    letI := (hE).stablePretriangulated
    Triangle.mk ((E).projectiveStableFunctor.map (homotopyCofiber.inr f))
      ((E).projectiveStableFunctor.map (coneProjection f))
      ((E).projectiveStableFunctor.map (f⟦(1 : ℤ)⟧') ≫ (splitStableShiftObjIso C n Y).hom) ∈
        distTriang (E).ProjectiveStableCategory := by
  let := (hE).stableHasShift
  let := (hE).stableShiftFunctor_additive
  let := (hE).stablePretriangulated
  rw [← stableConflationTriangle_coneSequence_eq_mk,
    ExactStructure.IsFrobenius.stablePretriangulated_distinguishedTriangles]
  exact (hE).stableConflationTriangle_mem _
    (conflation_coneSequence (ExactStructure.split C) f)

/-- The concrete periodic mapping cone realizes a distinguished stable triangle. Its last
arrow is minus the cone projection, followed by the comparison with stable suspension. -/
theorem mappingCone_distinguished {X Y : CochainComplex C (ZMod n)} (f : X ⟶ Y) :
    letI := (hE).stableHasShift
    letI := (hE).stableShiftFunctor_additive
    letI := (hE).stablePretriangulated
    Triangle.mk ((E).projectiveStableFunctor.map f)
      ((E).projectiveStableFunctor.map (homotopyCofiber.inr f))
      (-(E).projectiveStableFunctor.map (coneProjection f) ≫
        (splitStableShiftObjIso C n X).hom) ∈ distTriang (E).ProjectiveStableCategory := by
  let := (hE).stableHasShift
  let := (hE).stableShiftFunctor_additive
  let := (hE).stablePretriangulated
  rw [rotate_distinguished_triangle]
  refine isomorphic_distinguished _ (coneSequence_distinguished f) _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      (-(splitStableShiftObjIso C n X).symm) ?_ ?_ ?_)
  · -- Reduce the rotated triangle endpoints before simplifying their hom-group operations.
    dsimp only [Triangle.rotate, Triangle.mk, Iso.refl_hom]
    simp only [Category.id_comp, Category.comp_id]
  · dsimp only [Triangle.rotate, Triangle.mk, Iso.refl_hom]
    simp only [Preadditive.neg_iso_hom, Iso.symm_hom, Category.id_comp,
      Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  · dsimp only [Triangle.rotate, Triangle.mk, Iso.refl_hom]
    simp only [Preadditive.neg_iso_hom, Iso.symm_hom, Preadditive.neg_comp,
      splitStableShiftObjIso_hom_naturality, Iso.inv_hom_id_assoc]
    -- Naturality retains a composite-functor endpoint in the shifted identity.
    erw [CategoryTheory.Functor.map_id, Category.comp_id]

end TauCeti.PeriodicComplex
