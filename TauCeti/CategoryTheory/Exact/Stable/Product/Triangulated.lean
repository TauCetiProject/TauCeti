/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Stable.Product.Basic
public import TauCeti.CategoryTheory.Exact.Stable.Functor.Triangulated
public import TauCeti.CategoryTheory.Exact.Stable.Triangulated
public import TauCeti.CategoryTheory.Triangulated.Prod
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Triangulated stable categories of products

For Frobenius exact categories, the additive equivalence from the stable category of their
product to the product of their stable categories is a triangle equivalence. Its shift
comparison pairs the comparisons of the two descended projection functors. Consequently a
stable triangle in the product is distinguished exactly when both of its projected triangles
are distinguished.

The source has Happel's triangulation for the product exact structure; the target has the
componentwise shift and distinguished triangles. The Frobenius hypotheses are explicit
propositions, so the shift compatibility and triangle-functor structure are installed with
`letI`, as for the stable categories themselves.

## References

* Dieter Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2.
-/

public section

namespace TauCeti.ExactStructure

open CategoryTheory Limits Pretriangulated

universe v v' u u'

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasBinaryBiproducts D]
  {E : ExactStructure C} {E' : ExactStructure D}
  (hE : E.IsFrobenius) (hE' : E'.IsFrobenius)

/-- The stable product comparison commutes with all integral shifts. Its comparison is the
pairing of the shift comparisons of the descended exact projections. -/
@[instance_reducible]
noncomputable def projectiveStableProdFunctorCommShift :
    letI := (hE.prod hE').stableHasShift
    letI := hE.stableHasShift
    letI := hE'.stableHasShift
    (projectiveStableProdFunctor E E').CommShift ℤ := by
  letI := (hE.prod hE').stableHasShift
  letI := hE.stableHasShift
  letI := hE'.stableHasShift
  letI := (stableConflationExact_fst_prod E E').stableFunctorCommShift (hE.prod hE') hE
  letI := (stableConflationExact_snd_prod E E').stableFunctorCommShift (hE.prod hE') hE'
  exact Functor.CommShift.ofIso
    (projectiveStableProdFunctorIsoProd' E E' hE hE').symm ℤ

/-- The stable product shift comparison is obtained from the paired projection comparisons
by the canonical identification of the two underlying functors. -/
theorem projectiveStableProdFunctorCommShift_iso (n : ℤ) :
    letI := (hE.prod hE').stableHasShift
    letI := hE.stableHasShift
    letI := hE'.stableHasShift
    letI := (stableConflationExact_fst_prod E E').stableFunctorCommShift (hE.prod hE') hE
    letI := (stableConflationExact_snd_prod E E').stableFunctorCommShift (hE.prod hE') hE'
    letI := projectiveStableProdFunctorCommShift hE hE'
    (projectiveStableProdFunctor E E').commShiftIso n =
      Functor.isoWhiskerLeft (shiftFunctor (E.prod E').ProjectiveStableCategory n)
        (projectiveStableProdFunctorIsoProd' E E' hE hE') ≪≫
      (((stableConflationExact_fst_prod E E').stableFunctor (hE.prod hE')).prod'
        ((stableConflationExact_snd_prod E E').stableFunctor (hE.prod hE'))).commShiftIso n ≪≫
      Functor.isoWhiskerRight
        (projectiveStableProdFunctorIsoProd' E E' hE hE').symm
        (shiftFunctor (E.ProjectiveStableCategory × E'.ProjectiveStableCategory) n) :=
  (rfl)

/-- The first component of the stable product shift comparison is the
corresponding descended projection comparison, transported along the projection equalities. -/
@[simp]
theorem projectiveStableProdFunctor_commShiftIso_hom_app_fst (n : ℤ)
    (X : (E.prod E').ProjectiveStableCategory) :
    letI := (hE.prod hE').stableHasShift
    letI := hE.stableHasShift
    letI := hE'.stableHasShift
    letI := (stableConflationExact_fst_prod E E').stableFunctorCommShift (hE.prod hE') hE
    letI := (stableConflationExact_snd_prod E E').stableFunctorCommShift (hE.prod hE') hE'
    letI := projectiveStableProdFunctorCommShift hE hE'
    (((projectiveStableProdFunctor E E').commShiftIso n).hom.app X).1 =
      eqToHom (congrArg
        (fun F => F.obj ((shiftFunctor (E.prod E').ProjectiveStableCategory n).obj X))
        (projectiveStableProdFunctor_comp_fst E E' hE hE')) ≫
      (((stableConflationExact_fst_prod E E').stableFunctor (hE.prod hE')).commShiftIso
        n).hom.app X ≫
      (shiftFunctor E.ProjectiveStableCategory n).map
        (eqToHom (congrArg (fun F => F.obj X)
          (projectiveStableProdFunctor_comp_fst E E' hE hE').symm)) := by
  dsimp
  rw [projectiveStableProdFunctorCommShift_iso hE hE' n]
  simp

/-- The second component of the stable product shift comparison is the
corresponding descended projection comparison, transported along the projection equalities. -/
@[simp]
theorem projectiveStableProdFunctor_commShiftIso_hom_app_snd (n : ℤ)
    (X : (E.prod E').ProjectiveStableCategory) :
    letI := (hE.prod hE').stableHasShift
    letI := hE.stableHasShift
    letI := hE'.stableHasShift
    letI := (stableConflationExact_fst_prod E E').stableFunctorCommShift (hE.prod hE') hE
    letI := (stableConflationExact_snd_prod E E').stableFunctorCommShift (hE.prod hE') hE'
    letI := projectiveStableProdFunctorCommShift hE hE'
    (((projectiveStableProdFunctor E E').commShiftIso n).hom.app X).2 =
      eqToHom (congrArg
        (fun F => F.obj ((shiftFunctor (E.prod E').ProjectiveStableCategory n).obj X))
        (projectiveStableProdFunctor_comp_snd E E' hE hE')) ≫
      (((stableConflationExact_snd_prod E E').stableFunctor (hE.prod hE')).commShiftIso
        n).hom.app X ≫
      (shiftFunctor E'.ProjectiveStableCategory n).map
        (eqToHom (congrArg (fun F => F.obj X)
          (projectiveStableProdFunctor_comp_snd E E' hE hE').symm)) := by
  dsimp
  rw [projectiveStableProdFunctorCommShift_iso hE hE' n]
  simp

/-- The first component of the inverse stable product shift comparison is the
corresponding descended projection comparison, transported along the projection equalities. -/
@[simp]
theorem projectiveStableProdFunctor_commShiftIso_inv_app_fst (n : ℤ)
    (X : (E.prod E').ProjectiveStableCategory) :
    letI := (hE.prod hE').stableHasShift
    letI := hE.stableHasShift
    letI := hE'.stableHasShift
    letI := (stableConflationExact_fst_prod E E').stableFunctorCommShift (hE.prod hE') hE
    letI := (stableConflationExact_snd_prod E E').stableFunctorCommShift (hE.prod hE') hE'
    letI := projectiveStableProdFunctorCommShift hE hE'
    (((projectiveStableProdFunctor E E').commShiftIso n).inv.app X).1 =
      (shiftFunctor E.ProjectiveStableCategory n).map
        (eqToHom (congrArg (fun F => F.obj X) (projectiveStableProdFunctor_comp_fst E E' hE hE'))) ≫
      (((stableConflationExact_fst_prod E E').stableFunctor (hE.prod hE')).commShiftIso
        n).inv.app X ≫
      eqToHom (congrArg
        (fun F => F.obj ((shiftFunctor (E.prod E').ProjectiveStableCategory n).obj X))
        (projectiveStableProdFunctor_comp_fst E E' hE hE').symm) := by
  dsimp
  rw [projectiveStableProdFunctorCommShift_iso hE hE' n]
  simp

/-- The second component of the inverse stable product shift comparison is the
corresponding descended projection comparison, transported along the projection equalities. -/
@[simp]
theorem projectiveStableProdFunctor_commShiftIso_inv_app_snd (n : ℤ)
    (X : (E.prod E').ProjectiveStableCategory) :
    letI := (hE.prod hE').stableHasShift
    letI := hE.stableHasShift
    letI := hE'.stableHasShift
    letI := (stableConflationExact_fst_prod E E').stableFunctorCommShift (hE.prod hE') hE
    letI := (stableConflationExact_snd_prod E E').stableFunctorCommShift (hE.prod hE') hE'
    letI := projectiveStableProdFunctorCommShift hE hE'
    (((projectiveStableProdFunctor E E').commShiftIso n).inv.app X).2 =
      (shiftFunctor E'.ProjectiveStableCategory n).map
        (eqToHom (congrArg (fun F => F.obj X) (projectiveStableProdFunctor_comp_snd E E' hE hE'))) ≫
      (((stableConflationExact_snd_prod E E').stableFunctor (hE.prod hE')).commShiftIso
        n).inv.app X ≫
      eqToHom (congrArg
        (fun F => F.obj ((shiftFunctor (E.prod E').ProjectiveStableCategory n).obj X))
        (projectiveStableProdFunctor_comp_snd E E' hE hE').symm) := by
  dsimp
  rw [projectiveStableProdFunctorCommShift_iso hE hE' n]
  simp

/-- The stable product equivalence preserves distinguished triangles for Happel's source
triangulation and the componentwise target triangulation. -/
theorem projectiveStableProdFunctorIsTriangulated :
    letI := (hE.prod hE').stableHasShift
    letI := hE.stableHasShift
    letI := hE'.stableHasShift
    letI : ∀ n : ℤ, (shiftFunctor (E.prod E').ProjectiveStableCategory n).Additive :=
      (hE.prod hE').stableShiftFunctor_additive
    letI : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
      hE.stableShiftFunctor_additive
    letI : ∀ n : ℤ, (shiftFunctor E'.ProjectiveStableCategory n).Additive :=
      hE'.stableShiftFunctor_additive
    letI := (hE.prod hE').stablePretriangulated
    letI := hE.stablePretriangulated
    letI := hE'.stablePretriangulated
    letI := projectiveStableProdFunctorCommShift hE hE'
    (projectiveStableProdFunctor E E').IsTriangulated := by
  let := (hE.prod hE').stableHasShift
  let := hE.stableHasShift
  let := hE'.stableHasShift
  let : ∀ n : ℤ, (shiftFunctor (E.prod E').ProjectiveStableCategory n).Additive :=
    (hE.prod hE').stableShiftFunctor_additive
  let : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
    hE.stableShiftFunctor_additive
  let : ∀ n : ℤ, (shiftFunctor E'.ProjectiveStableCategory n).Additive :=
    hE'.stableShiftFunctor_additive
  let := (hE.prod hE').stablePretriangulated
  let := hE.stablePretriangulated
  let := hE'.stablePretriangulated
  let := (stableConflationExact_fst_prod E E').stableFunctorCommShift (hE.prod hE') hE
  let := (stableConflationExact_snd_prod E E').stableFunctorCommShift (hE.prod hE') hE'
  let := (stableConflationExact_fst_prod E E').stableFunctorIsTriangulated (hE.prod hE') hE
  let := (stableConflationExact_snd_prod E E').stableFunctorIsTriangulated (hE.prod hE') hE'
  let := projectiveStableProdFunctorCommShift hE hE'
  have := Functor.CommShift.ofIso_compatibility
    (projectiveStableProdFunctorIsoProd' E E' hE hE').symm ℤ
  exact Functor.isTriangulated_of_iso
    (projectiveStableProdFunctorIsoProd' E E' hE hE').symm

/-- A stable triangle for the product exact structure is distinguished precisely when its
images under both descended exact projections are distinguished. -/
theorem mem_distTriang_projectiveStableProd_iff :
    letI := (hE.prod hE').stableHasShift
    letI := hE.stableHasShift
    letI := hE'.stableHasShift
    letI : ∀ n : ℤ, (shiftFunctor (E.prod E').ProjectiveStableCategory n).Additive :=
      (hE.prod hE').stableShiftFunctor_additive
    letI : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
      hE.stableShiftFunctor_additive
    letI : ∀ n : ℤ, (shiftFunctor E'.ProjectiveStableCategory n).Additive :=
      hE'.stableShiftFunctor_additive
    letI := (hE.prod hE').stablePretriangulated
    letI := hE.stablePretriangulated
    letI := hE'.stablePretriangulated
    letI := (stableConflationExact_fst_prod E E').stableFunctorCommShift (hE.prod hE') hE
    letI := (stableConflationExact_snd_prod E E').stableFunctorCommShift (hE.prod hE') hE'
    ∀ T : Triangle (E.prod E').ProjectiveStableCategory,
      T ∈ distTriang (E.prod E').ProjectiveStableCategory ↔
        ((stableConflationExact_fst_prod E E').stableFunctor (hE.prod hE')).mapTriangle.obj T ∈
          distTriang E.ProjectiveStableCategory ∧
        ((stableConflationExact_snd_prod E E').stableFunctor (hE.prod hE')).mapTriangle.obj T ∈
          distTriang E'.ProjectiveStableCategory := by
  let := (hE.prod hE').stableHasShift
  let := hE.stableHasShift
  let := hE'.stableHasShift
  let : ∀ n : ℤ, (shiftFunctor (E.prod E').ProjectiveStableCategory n).Additive :=
    (hE.prod hE').stableShiftFunctor_additive
  let : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
    hE.stableShiftFunctor_additive
  let : ∀ n : ℤ, (shiftFunctor E'.ProjectiveStableCategory n).Additive :=
    hE'.stableShiftFunctor_additive
  let := (hE.prod hE').stablePretriangulated
  let := hE.stablePretriangulated
  let := hE'.stablePretriangulated
  let := (stableConflationExact_fst_prod E E').stableFunctorCommShift (hE.prod hE') hE
  let := (stableConflationExact_snd_prod E E').stableFunctorCommShift (hE.prod hE') hE'
  let := projectiveStableProdFunctorCommShift hE hE'
  have := projectiveStableProdFunctorIsTriangulated hE hE'
  have := Functor.CommShift.ofIso_compatibility
    (projectiveStableProdFunctorIsoProd' E E' hE hE').symm ℤ
  let F := (stableConflationExact_fst_prod E E').stableFunctor (hE.prod hE')
  let G := (stableConflationExact_snd_prod E E').stableFunctor (hE.prod hE')
  intro T
  rw [← (projectiveStableProdFunctor E E').map_distinguished_iff T]
  exact (distinguished_iff_of_iso
    ((Functor.mapTriangleIso
      (projectiveStableProdFunctorIsoProd' E E' hE hE').symm).app T)).symm.trans
    ((mem_distTriang_prod_iff _).trans (and_congr
      (distinguished_iff_of_iso
        ((Functor.mapTriangleCompIso (F.prod' G)
          (CategoryTheory.Prod.fst _ _)).symm.app T ≪≫
          (Functor.mapTriangleIso (Functor.prod'CompFst F G)).app T))
      (distinguished_iff_of_iso
        ((Functor.mapTriangleCompIso (F.prod' G)
          (CategoryTheory.Prod.snd _ _)).symm.app T ≪≫
          (Functor.mapTriangleIso (Functor.prod'CompSnd F G)).app T))))

/-- The forward functor of the stable product equivalence commutes with integral shifts,
using the paired comparisons of the descended projections. -/
@[instance_reducible]
noncomputable def projectiveStableProdEquivalenceFunctorCommShift :
    letI := (hE.prod hE').stableHasShift
    letI := hE.stableHasShift
    letI := hE'.stableHasShift
    (projectiveStableProdEquivalence E E').functor.CommShift ℤ := by
  letI := (hE.prod hE').stableHasShift
  letI := hE.stableHasShift
  letI := hE'.stableHasShift
  letI := projectiveStableProdFunctorCommShift hE hE'
  exact Functor.CommShift.ofIso
    (eqToIso (projectiveStableProdEquivalence_functor E E')).symm ℤ

/-- The forward equivalence uses the stable product functor's shift comparison, transported
along the equality identifying the forward functor with the product comparison. -/
@[simp]
theorem projectiveStableProdEquivalenceFunctor_commShiftIso (n : ℤ) :
    letI := (hE.prod hE').stableHasShift
    letI := hE.stableHasShift
    letI := hE'.stableHasShift
    letI := projectiveStableProdFunctorCommShift hE hE'
    letI := projectiveStableProdEquivalenceFunctorCommShift hE hE'
    (projectiveStableProdEquivalence E E').functor.commShiftIso n =
      Functor.isoWhiskerLeft (shiftFunctor (E.prod E').ProjectiveStableCategory n)
        (eqToIso (projectiveStableProdEquivalence_functor E E')) ≪≫
      (projectiveStableProdFunctor E E').commShiftIso n ≪≫
      Functor.isoWhiskerRight (eqToIso (projectiveStableProdEquivalence_functor E E')).symm
        (shiftFunctor (E.ProjectiveStableCategory × E'.ProjectiveStableCategory) n) :=
  (rfl)

/-- The inverse stable product equivalence commutes with integral shifts via the canonical
mate of its forward comparison. -/
@[instance_reducible]
noncomputable def projectiveStableProdEquivalenceInverseCommShift :
    letI := (hE.prod hE').stableHasShift
    letI := hE.stableHasShift
    letI := hE'.stableHasShift
    (projectiveStableProdEquivalence E E').inverse.CommShift ℤ := by
  letI := (hE.prod hE').stableHasShift
  letI := hE.stableHasShift
  letI := hE'.stableHasShift
  letI := projectiveStableProdEquivalenceFunctorCommShift hE hE'
  exact (projectiveStableProdEquivalence E E').commShiftInverse ℤ

/-- The additive stable product equivalence is a triangle equivalence. The inverse shift
comparison is the canonical mate of the forward comparison. -/
theorem projectiveStableProdEquivalenceIsTriangulated :
    letI := (hE.prod hE').stableHasShift
    letI := hE.stableHasShift
    letI := hE'.stableHasShift
    letI : ∀ n : ℤ, (shiftFunctor (E.prod E').ProjectiveStableCategory n).Additive :=
      (hE.prod hE').stableShiftFunctor_additive
    letI : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
      hE.stableShiftFunctor_additive
    letI : ∀ n : ℤ, (shiftFunctor E'.ProjectiveStableCategory n).Additive :=
      hE'.stableShiftFunctor_additive
    letI := (hE.prod hE').stablePretriangulated
    letI := hE.stablePretriangulated
    letI := hE'.stablePretriangulated
    letI := projectiveStableProdFunctorCommShift hE hE'
    letI := projectiveStableProdEquivalenceFunctorCommShift hE hE'
    letI := projectiveStableProdEquivalenceInverseCommShift hE hE'
    letI := (projectiveStableProdEquivalence E E').commShift_of_functor ℤ
    (projectiveStableProdEquivalence E E').IsTriangulated := by
  let := (hE.prod hE').stableHasShift
  let := hE.stableHasShift
  let := hE'.stableHasShift
  let : ∀ n : ℤ, (shiftFunctor (E.prod E').ProjectiveStableCategory n).Additive :=
    (hE.prod hE').stableShiftFunctor_additive
  let : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
    hE.stableShiftFunctor_additive
  let : ∀ n : ℤ, (shiftFunctor E'.ProjectiveStableCategory n).Additive :=
    hE'.stableShiftFunctor_additive
  let := (hE.prod hE').stablePretriangulated
  let := hE.stablePretriangulated
  let := hE'.stablePretriangulated
  let := projectiveStableProdFunctorCommShift hE hE'
  let := projectiveStableProdEquivalenceFunctorCommShift hE hE'
  let := projectiveStableProdEquivalenceInverseCommShift hE hE'
  let := (projectiveStableProdEquivalence E E').commShift_of_functor ℤ
  have := projectiveStableProdFunctorIsTriangulated hE hE'
  have := Functor.CommShift.ofIso_compatibility
    (eqToIso (projectiveStableProdEquivalence_functor E E')).symm ℤ
  exact Equivalence.IsTriangulated.mk' _ (Functor.isTriangulated_of_iso
    (eqToIso (projectiveStableProdEquivalence_functor E E')).symm)

/-- The componentwise pretriangulated product of two Frobenius stable categories satisfies
the octahedral axiom, by its triangle equivalence with the stable category of the product. -/
theorem stableProdIsTriangulated :
    letI := hE.stableHasShift
    letI := hE'.stableHasShift
    letI : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
      hE.stableShiftFunctor_additive
    letI : ∀ n : ℤ, (shiftFunctor E'.ProjectiveStableCategory n).Additive :=
      hE'.stableShiftFunctor_additive
    letI := hE.stablePretriangulated
    letI := hE'.stablePretriangulated
    IsTriangulated (E.ProjectiveStableCategory × E'.ProjectiveStableCategory) := by
  let := (hE.prod hE').stableHasShift
  let := hE.stableHasShift
  let := hE'.stableHasShift
  let : ∀ n : ℤ, (shiftFunctor (E.prod E').ProjectiveStableCategory n).Additive :=
    (hE.prod hE').stableShiftFunctor_additive
  let : ∀ n : ℤ, (shiftFunctor E.ProjectiveStableCategory n).Additive :=
    hE.stableShiftFunctor_additive
  let : ∀ n : ℤ, (shiftFunctor E'.ProjectiveStableCategory n).Additive :=
    hE'.stableShiftFunctor_additive
  let := (hE.prod hE').stablePretriangulated
  let := hE.stablePretriangulated
  let := hE'.stablePretriangulated
  have := (hE.prod hE').stableIsTriangulated
  let := projectiveStableProdFunctorCommShift hE hE'
  let := projectiveStableProdEquivalenceFunctorCommShift hE hE'
  let := projectiveStableProdEquivalenceInverseCommShift hE hE'
  have := (projectiveStableProdEquivalence E E').commShift_of_functor ℤ
  have := projectiveStableProdEquivalenceIsTriangulated hE hE'
  exact IsTriangulated.of_fully_faithful_triangulated_functor
    (projectiveStableProdEquivalence E E').inverse

end TauCeti.ExactStructure
