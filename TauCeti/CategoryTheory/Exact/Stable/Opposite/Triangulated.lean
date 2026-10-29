/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Opposite.Connecting
public import TauCeti.CategoryTheory.Exact.Stable.Opposite.Shift
public import TauCeti.CategoryTheory.Exact.Stable.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated

/-!
# Triangulated opposite stable categories

For a Frobenius exact category `C`, the additive equivalence from the stable category of `Cᵒᵖ`
to the opposite of the stable category of `C` is a triangle equivalence. Here the source carries
Happel's triangulation for the opposite Frobenius exact structure `E.op`, while the target carries
Mathlib's opposite triangulation `CategoryTheory.Pretriangulated.Opposite`, whose shift by `n` is
the opposite of shift by `-n` and whose distinguished triangles are the opposites of
distinguished triangles in the stable category of `C` without additional signs.

For a conflation `S` in `C`, the standard triangle of `S.op` in the stable category of `Cᵒᵖ`
maps under `projectiveStableOpFunctor` to a triangle in `(E.ProjectiveStableCategory)ᵒᵖ` whose
unopposite under `triangleOpEquivalence` is canonically isomorphic to the standard triangle of `S`.
The third-arrow compatibility combines the degree-one formula for
`projectiveStableOpFunctorCommShift`, the transpose connecting-map formula `stableConnectingMapOp`,
and the suspension-loop relation `stableSuspension_map_stableConnectingMapOp`.

Consequently `projectiveStableOpFunctor` and both directions of `projectiveStableOpEquivalence`
are triangulated, and a triangle in `E.op.ProjectiveStableCategory` is distinguished if and only
if its opposite-stable image corresponds under `triangleOpEquivalence` to a distinguished triangle
in `E.ProjectiveStableCategory`.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
* `TauCeti.ExactStructure.IsFrobenius.stableSuspension_map_stableConnectingMapOp`: the
  suspension-loop compatibility for the transpose of the opposite connecting map.
* `TauCeti.ExactStructure.IsFrobenius.projectiveStableOpFunctorCommShift`: the coherent integral
  shift compatibility of the opposite stable comparison functor.
* `CategoryTheory.Pretriangulated.triangleOpEquivalence`: Mathlib's opposite triangulation.
-/

public section

namespace TauCeti.ExactStructure.IsFrobenius

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] {E : ExactStructure C} (hE : E.IsFrobenius)

/-- Unopposing the opposite-stable image of the standard triangle of `S.op` via
`triangleOpEquivalence` recovers the standard triangle of `S`. Its three components identify the
unopposed images of the three terms with their representatives in the original stable category. -/
private noncomputable def mapStableConflationTriangleOpIso
    (S : ShortComplex C) (hS : E.Conflation S) :
    letI := hE.stableHasShift
    letI := hE.op.stableHasShift
    letI := hE.projectiveStableOpFunctorCommShift
    ((triangleOpEquivalence E.ProjectiveStableCategory).inverse.obj
      ((E.projectiveStableOpFunctor hE.projective_iff_injective).mapTriangle.obj
        (hE.op.stableConflationTriangle S.op ((E.op_conflation_op_iff S).mpr hS)))).unop ≅
      hE.stableConflationTriangle S hS := by
  let := hE.stableHasShift
  let := hE.op.stableHasShift
  let := hE.projectiveStableOpFunctorCommShift
  let hS_op : E.op.Conflation S.op := (E.op_conflation_op_iff S).mpr hS
  rw [hE.op.stableConflationTriangle_eq_mk S.op hS_op, hE.stableConflationTriangle_eq_mk S hS]
  have hX₁' : (E.projectiveStableOpFunctor hE.projective_iff_injective).obj
      (E.op.projectiveStableFunctor.obj S.op.X₃) =
      Opposite.op (E.projectiveStableFunctor.obj S.X₁) :=
    E.projectiveStableOpFunctor_obj hE.projective_iff_injective (Opposite.op S.X₁)
  have hX₂' : (E.projectiveStableOpFunctor hE.projective_iff_injective).obj
      (E.op.projectiveStableFunctor.obj S.op.X₂) =
      Opposite.op (E.projectiveStableFunctor.obj S.X₂) :=
    E.projectiveStableOpFunctor_obj hE.projective_iff_injective (Opposite.op S.X₂)
  have hX₃' : (E.projectiveStableOpFunctor hE.projective_iff_injective).obj
      (E.op.projectiveStableFunctor.obj S.op.X₁) =
      Opposite.op (E.projectiveStableFunctor.obj S.X₃) :=
    E.projectiveStableOpFunctor_obj hE.projective_iff_injective (Opposite.op S.X₃)
  have hX₁ : ((E.projectiveStableOpFunctor hE.projective_iff_injective).obj
      (E.op.projectiveStableFunctor.obj S.op.X₃)).unop =
      E.projectiveStableFunctor.obj S.X₁ :=
    congrArg Opposite.unop hX₁'
  have hX₂ : ((E.projectiveStableOpFunctor hE.projective_iff_injective).obj
      (E.op.projectiveStableFunctor.obj S.op.X₂)).unop =
      E.projectiveStableFunctor.obj S.X₂ :=
    congrArg Opposite.unop hX₂'
  have hX₃ : ((E.projectiveStableOpFunctor hE.projective_iff_injective).obj
      (E.op.projectiveStableFunctor.obj S.op.X₁)).unop =
      E.projectiveStableFunctor.obj S.X₃ :=
    congrArg Opposite.unop hX₃'
  refine Triangle.isoMk _ _ (eqToIso hX₁) (eqToIso hX₂) (eqToIso hX₃) ?_ ?_ ?_
  · dsimp [triangleOpEquivalence, TriangleOpEquivalence.inverse, Functor.mapTriangle]
    rw [E.projectiveStableOpFunctor_map hE.projective_iff_injective S.op.g]
    simp only [unop_comp, Quiver.Hom.unop_op, eqToHom_unop, Category.assoc,
      eqToHom_trans]
    dsimp [ShortComplex.op]
    simp
  · dsimp [triangleOpEquivalence, TriangleOpEquivalence.inverse, Functor.mapTriangle]
    rw [E.projectiveStableOpFunctor_map hE.projective_iff_injective S.op.f]
    simp only [unop_comp, Quiver.Hom.unop_op, eqToHom_unop, Category.assoc,
      eqToHom_trans]
    dsimp [ShortComplex.op]
    simp
  · -- Expand the degree-one shift comparison and cancel the source suspension identification.
    dsimp [triangleOpEquivalence, TriangleOpEquivalence.inverse]
    rw [← unop_comp, hE.projectiveStableOpFunctorCommShift_iso_one]
    simp only [Functor.map_comp, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Iso.symm_hom, NatIso.op_hom, NatTrans.op_app, Category.assoc]
    rw [← Functor.map_comp_assoc _ (hE.op.stableShiftFunctorOneIso.inv.app _),
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
    -- Express the opposite connecting map through its transpose in the original stable category.
    -- Keep the local endpoint equalities explicit when using the imported identity.
    have hconn :
        (E.projectiveStableOpFunctor hE.projective_iff_injective).map
            (E.op.projectiveStableFunctor.map (hE.op.connectingMap hS_op)) ≫
          (E.projectiveStableOpFunctor hE.projective_iff_injective).map
            (eqToHom (hE.op.stableSuspension_obj_projectiveStableFunctor_obj S.op.X₁).symm) ≫
          hE.stableSuspensionCompProjectiveStableOpFunctorIso.hom.app
            (E.op.projectiveStableFunctor.obj S.op.X₁) =
        eqToHom hX₁' ≫
          (hE.stableConnectingMapOp hS).op ≫
          hE.enoughProjectives.stableLoop.op.map (eqToHom hX₃'.symm) :=
      hE.projectiveStableOpFunctor_map_connectingMap S hS
    rw [reassoc_of% hconn]
    -- Move the endpoint identification through the degree -1 comparison by naturality.
    have hn := (NatIso.op hE.stableShiftFunctorNegOneIso).hom.naturality (eqToHom hX₃'.symm)
    simp only [Functor.op_obj, NatIso.op_hom, NatTrans.op_app] at hn
    rw [reassoc_of% hn]
    -- Expand the opposite-shift unit and cancel the bridge to the original shift.
    rw [opShiftFunctorEquivalence_unitIso_inv_app
      ((E.projectiveStableOpFunctor hE.projective_iff_injective).obj
        (E.op.projectiveStableFunctor.obj S.op.X₁)) 1 (-1) (by simp)]
    simp only [unop_comp, Quiver.Hom.unop_op, Functor.op_map, eqToHom_unop,
      Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc _
      (((shiftFunctorOpIso E.ProjectiveStableCategory 1 (-1) (by simp)).hom.app _).unop),
      ← unop_comp, Iso.inv_hom_id_app]
    simp only [Functor.op_obj, unop_id, CategoryTheory.Functor.map_id, Category.id_comp]
    -- Cancel the successive shifts by -1 and 1 using the suspension-loop counit.
    have hunit :=
      ((shiftFunctorCompIsoId E.ProjectiveStableCategory (-1 : ℤ) 1 (by omega)).inv.naturality
        (eqToHom hX₃)).symm
    simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at hunit
    rw [reassoc_of% hunit]
    rw [hE.shiftFunctorCompIsoId_inv_comp_shift_stableShiftFunctorNegOneIso_hom_app_assoc]
    -- Suspending the transpose recovers the original connecting map.
    have hshift := (hE.stableShiftFunctorOneIso.inv.naturality (hE.stableConnectingMapOp hS)).symm
    rw [reassoc_of% hshift, reassoc_of% (hE.stableSuspension_map_stableConnectingMapOp hS),
      Iso.inv_hom_id_app_assoc]
    simp only [← Functor.map_comp, eqToHom_trans, eqToHom_refl,
      CategoryTheory.Functor.map_id, Category.comp_id]

/-- The opposite-stable image of the standard triangle of `S.op` is distinguished in
`E.ProjectiveStableCategoryᵒᵖ`. -/
theorem map_stableConflationTriangle_op_mem_distTriang
    (S : ShortComplex C) (hS : E.Conflation S) :
    letI := hE.stableHasShift
    letI := hE.op.stableHasShift
    letI : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
      hE.stableShiftFunctor_additive
    letI := hE.stablePretriangulated
    letI := hE.projectiveStableOpFunctorCommShift
    (E.projectiveStableOpFunctor hE.projective_iff_injective).mapTriangle.obj
      (hE.op.stableConflationTriangle S.op ((E.op_conflation_op_iff S).mpr hS)) ∈
      distTriang E.ProjectiveStableCategoryᵒᵖ := by
  let := hE.stableHasShift
  let := hE.op.stableHasShift
  let : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
    hE.stableShiftFunctor_additive
  let := hE.stablePretriangulated
  let := hE.projectiveStableOpFunctorCommShift
  rw [mem_distTriang_op_iff, hE.stablePretriangulated_distinguishedTriangles]
  exact hE.stableDistinguishedTriangles_isomorphic (hE.stableConflationTriangle_mem S hS)
    (hE.mapStableConflationTriangleOpIso S hS).symm

/-- The opposite stable comparison functor preserves distinguished triangles for Happel's
triangulation on the source and Mathlib's opposite triangulation on the target. -/
theorem projectiveStableOpFunctorIsTriangulated :
    letI := hE.stableHasShift
    letI := hE.op.stableHasShift
    letI : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
      hE.stableShiftFunctor_additive
    letI : ∀ n : ℤ, (shiftFunctor E.op.ProjectiveStableCategory n).Additive :=
      hE.op.stableShiftFunctor_additive
    letI := hE.stablePretriangulated
    letI := hE.op.stablePretriangulated
    letI := hE.projectiveStableOpFunctorCommShift
    (E.projectiveStableOpFunctor hE.projective_iff_injective).IsTriangulated := by
  let := hE.stableHasShift
  let := hE.op.stableHasShift
  let : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
    hE.stableShiftFunctor_additive
  let : ∀ n : ℤ, (shiftFunctor E.op.ProjectiveStableCategory n).Additive :=
    hE.op.stableShiftFunctor_additive
  let := hE.stablePretriangulated
  let := hE.op.stablePretriangulated
  let := hE.projectiveStableOpFunctorCommShift
  constructor
  intro T hT
  rw [hE.op.stablePretriangulated_distinguishedTriangles] at hT
  obtain ⟨S, hS, ⟨e⟩⟩ := (hE.op.mem_stableDistinguishedTriangles_iff T).1 hT
  have hS' : E.Conflation S.unop := (E.op_conflation S).mp hS
  exact Pretriangulated.isomorphic_distinguished _
    (hE.map_stableConflationTriangle_op_mem_distTriang S.unop hS') _
    ((E.projectiveStableOpFunctor hE.projective_iff_injective).mapTriangle.mapIso e)

/-- The additive equivalence between the stable category of `Cᵒᵖ` and the opposite stable category
of `C` is a triangle equivalence. -/
theorem projectiveStableOpEquivalenceIsTriangulated :
    letI := hE.stableHasShift
    letI := hE.op.stableHasShift
    letI : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
      hE.stableShiftFunctor_additive
    letI : ∀ n : ℤ, (shiftFunctor E.op.ProjectiveStableCategory n).Additive :=
      hE.op.stableShiftFunctor_additive
    letI := hE.stablePretriangulated
    letI := hE.op.stablePretriangulated
    letI := hE.projectiveStableOpFunctorCommShift
    letI := hE.projectiveStableOpEquivalenceFunctorCommShift
    letI := (E.projectiveStableOpEquivalence hE.projective_iff_injective).commShiftInverse ℤ
    letI := (E.projectiveStableOpEquivalence hE.projective_iff_injective).commShift_of_functor ℤ
    (E.projectiveStableOpEquivalence hE.projective_iff_injective).IsTriangulated := by
  let := hE.stableHasShift
  let := hE.op.stableHasShift
  let : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
    hE.stableShiftFunctor_additive
  let : ∀ n : ℤ, (shiftFunctor E.op.ProjectiveStableCategory n).Additive :=
    hE.op.stableShiftFunctor_additive
  let := hE.stablePretriangulated
  let := hE.op.stablePretriangulated
  let := hE.projectiveStableOpFunctorCommShift
  let := hE.projectiveStableOpEquivalenceFunctorCommShift
  let := (E.projectiveStableOpEquivalence hE.projective_iff_injective).commShiftInverse ℤ
  let := (E.projectiveStableOpEquivalence hE.projective_iff_injective).commShift_of_functor ℤ
  have := hE.projectiveStableOpFunctorIsTriangulated
  have := hE.projectiveStableOpEquivalence_functor_commShift
  exact Equivalence.IsTriangulated.mk' _ (Functor.isTriangulated_of_iso
    (eqToIso (E.projectiveStableOpEquivalence_functor hE.projective_iff_injective)).symm)

end TauCeti.ExactStructure.IsFrobenius
