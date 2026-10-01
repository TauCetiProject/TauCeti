/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Functor.Shift
public import TauCeti.CategoryTheory.Exact.Stable.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Exact functors induce triangle functors on stable categories

An exact functor between Frobenius exact categories that preserves projective-injective objects
induces a triangle functor on their stable categories, with the suspension comparison obtained
from injective presentations. The essential compatibility is that the image of a connecting map,
followed by this comparison, is the connecting map of the image conflation. Consequently the
image of a standard conflation triangle is isomorphic to the standard triangle of the image
conflation, and every distinguished triangle is preserved.

`StableConflationExact.stableFunctorIsTriangulated` supplies Mathlib's
`Functor.IsTriangulated` structure for the previously constructed shift compatibility.
As for the stable shift and pretriangulated structure, the Frobenius hypotheses are explicit
propositions: install the resulting structures with `letI`.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
-/

public section

universe v₁ v₂ u₁ u₂

namespace TauCeti.StableConflationExact

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
variable [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
variable {E : ExactStructure C} {E' : ExactStructure D}
variable {F : C ⥤ D} [F.Additive]
variable (hF : StableConflationExact E E' F) (hE : E.IsFrobenius) (hE' : E'.IsFrobenius)

/-- The stable image of a standard conflation triangle is canonically isomorphic to the
standard triangle of the image conflation. Its three components identify the images of the
three terms with their representatives in the target stable category. -/
private noncomputable def mapStableConflationTriangleIso
    (S : ShortComplex C) (hS : E.Conflation S) :
    letI := hE.stableHasShift
    letI := hE'.stableHasShift
    letI := hF.stableFunctorCommShift hE hE'
    (hF.stableFunctor hE).mapTriangle.obj (hE.stableConflationTriangle S hS) ≅
      hE'.stableConflationTriangle (S.map F) (hF.isConflationExact.map_conflation hS) := by
  letI := hE.stableHasShift
  letI := hE'.stableHasShift
  letI := hF.stableFunctorCommShift hE hE'
  rw [hE.stableConflationTriangle_eq_mk, hE'.stableConflationTriangle_eq_mk]
  refine Triangle.isoMk _ _
    (eqToIso (hF.stableFunctor_obj_projectiveStableFunctor_obj hE S.X₁))
    (eqToIso (hF.stableFunctor_obj_projectiveStableFunctor_obj hE S.X₂))
    (eqToIso (hF.stableFunctor_obj_projectiveStableFunctor_obj hE S.X₃)) ?_ ?_ ?_
  · exact hF.stableFunctor_map_projectiveStableFunctor_map hE S.f
  · exact hF.stableFunctor_map_projectiveStableFunctor_map hE S.g
  · dsimp
    rw [hF.stableFunctorCommShift_iso_one hE hE']
    -- Expand the degree-one comparison and cancel the suspension/shift bridges.
    simp only [Functor.map_comp, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc]
    simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
      stableSuspensionCompStableFunctorIso_hom_app, eqToHom_map, Category.assoc,
      eqToHom_trans_assoc]
    rw [(hF.stableFunctor hE).map_id]
    simp only [Category.id_comp, eqToHom_trans_assoc]
    have hmap : (hF.stableFunctor hE).map
        (E.projectiveStableFunctor.map (hE.connectingMap hS)) =
        eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE S.X₃) ≫
          E'.projectiveStableFunctor.map (F.map (hE.connectingMap hS)) ≫
          eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE
            (hE.suspensionObj S.X₁)).symm := by
      apply (cancel_mono (eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE
        (hE.suspensionObj S.X₁)))).1
      simp [Category.assoc, hF.stableFunctor_map_projectiveStableFunctor_map hE]
    rw [hmap]
    simp only [Category.assoc, eqToHom_trans_assoc]
    rw [hF.map_connectingMap_comp_suspensionComparison_assoc hE hE']
    have hn := hE'.stableShiftFunctorOneIso.inv.naturality
      (eqToHom (hF.stableFunctor_obj_projectiveStableFunctor_obj hE S.X₁))
    simp only [eqToHom_map] at hn
    rw [← hn]
    simp

/-- An exact functor preserving projective-injectives induces a triangle functor between
Frobenius stable categories, with the shift comparison constructed from injective presentations.
-/
theorem stableFunctorIsTriangulated :
    let := hE.stableHasShift
    let := hE'.stableHasShift
    let : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
      hE.stableShiftFunctor_additive
    let : ∀ n : ℤ, (shiftFunctor E'.ProjectiveStableCategory n).Additive :=
      hE'.stableShiftFunctor_additive
    let := hE.stablePretriangulated
    let := hE'.stablePretriangulated
    let := hF.stableFunctorCommShift hE hE'
    (hF.stableFunctor hE).IsTriangulated := by
  let := hE.stableHasShift
  let := hE'.stableHasShift
  let : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
    hE.stableShiftFunctor_additive
  let : ∀ n : ℤ, (shiftFunctor E'.ProjectiveStableCategory n).Additive :=
    hE'.stableShiftFunctor_additive
  let := hE.stablePretriangulated
  let := hE'.stablePretriangulated
  let := hF.stableFunctorCommShift hE hE'
  constructor
  intro T hT
  rw [hE.stablePretriangulated_distinguishedTriangles] at hT
  rw [hE'.stablePretriangulated_distinguishedTriangles]
  obtain ⟨S, hS, ⟨e⟩⟩ := (hE.mem_stableDistinguishedTriangles_iff T).1 hT
  exact (hE'.mem_stableDistinguishedTriangles_iff _).2
    ⟨S.map F, hF.isConflationExact.map_conflation hS,
      ⟨(hF.stableFunctor hE).mapTriangle.mapIso e ≪≫
        hF.mapStableConflationTriangleIso hE hE' S hS⟩⟩

end TauCeti.StableConflationExact
