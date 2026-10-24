/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.DifferentialModule.Frobenius
public import TauCeti.Algebra.Homology.Periodic.Triangulated
public import TauCeti.CategoryTheory.Exact.Stable.Functor.Equivalence

/-!
# The stable category of differential modules is the one-periodic homotopy category

Let `C` be an additive category. The componentwise split exact structure on differential
modules in `C` is Frobenius (`TauCeti.ExactStructure.differentialModule_split_isFrobenius`), so
Happel's construction triangulates its stable category. This file identifies that triangulated
category with `K₁(C)`, Mathlib's homotopy category of one-periodic complexes, which carries the
mapping-cone triangulation of `TauCeti.Algebra.Homology.Periodic.Triangulated`.

The comparison functor `TauCeti.DifferentialModule.stableToHomotopy` is the stable equivalence
induced by the exact equivalence between differential modules and one-periodic complexes,
followed by the identification of the split stable category of one-periodic complexes with
their homotopy category. It sends the stable class of a morphism of differential modules to the
homotopy class of the same morphism of one-periodic complexes
(`TauCeti.DifferentialModule.projectiveStableFunctor_comp_stableToHomotopy`), and it is an
equivalence (`TauCeti.DifferentialModule.stableHomotopyEquivalence`). It commutes with the
integral shifts, Happel's stable suspension on the source and the signed cyclic shift on the
target (`TauCeti.DifferentialModule.stableToHomotopyCommShift`), and it is a triangle functor
(`TauCeti.DifferentialModule.stableToHomotopy_isTriangulated`). Consequently a triangle in the
stable category of differential modules is distinguished exactly when its image in `K₁(C)` is
(`TauCeti.DifferentialModule.stableToHomotopy_mapTriangle_mem_distTriang_iff`): Happel's
triangulation of differential modules and the mapping-cone triangulation of `K₁(C)` agree.

## References

* D. Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2, Theorem 2.6.
* Luchezar L. Avramov, Ragnar-Olaf Buchweitz and Srikanth Iyengar, *Class and rank of
  differential modules*, Invent. Math. **169** (2007), 1–35, Section 1.
* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.
-/

public section

namespace TauCeti.DifferentialModule

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

/-- Passing to one-periodic complexes is stable conflation-exact for the componentwise split
exact structures. -/
theorem stableConflationExact_onePeriodicComplexEquivalence_functor :
    StableConflationExact (ExactStructure.split C).differentialModule
      ((ExactStructure.split C).homologicalComplex (ComplexShape.up (ZMod 1)))
      (onePeriodicComplexEquivalence C).functor :=
  (ExactStructure.split C).isConflationExact_onePeriodicComplexEquivalence_functor
    |>.stableConflationExact_of_equivalence
      (ExactStructure.split C).isConflationExact_onePeriodicComplexEquivalence_inverse
      (ExactStructure.homologicalComplex_split_isFrobenius
        (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (fun i ↦ ⟨i + 1, rfl⟩))

/-- Passing from one-periodic complexes to differential modules is stable conflation-exact for
the componentwise split exact structures. -/
theorem stableConflationExact_onePeriodicComplexEquivalence_inverse :
    StableConflationExact
      ((ExactStructure.split C).homologicalComplex (ComplexShape.up (ZMod 1)))
      (ExactStructure.split C).differentialModule
      (onePeriodicComplexEquivalence C).inverse := by
  have : (onePeriodicComplexEquivalence C).symm.functor.Additive :=
    inferInstanceAs (onePeriodicComplexEquivalence C).inverse.Additive
  exact (ExactStructure.split C).isConflationExact_onePeriodicComplexEquivalence_inverse
    |>.stableConflationExact_of_equivalence (e := (onePeriodicComplexEquivalence C).symm)
      (ExactStructure.split C).isConflationExact_onePeriodicComplexEquivalence_functor
      ExactStructure.differentialModule_split_isFrobenius

/-- The equivalence between the split stable categories of differential modules and of
one-periodic complexes induced by `TauCeti.DifferentialModule.onePeriodicComplexEquivalence`. -/
noncomputable abbrev stableOnePeriodicComplexEquivalence :
    (ExactStructure.split C).differentialModule.ProjectiveStableCategory ≌
      ((ExactStructure.split C).homologicalComplex
        (ComplexShape.up (ZMod 1))).ProjectiveStableCategory :=
  StableConflationExact.stableEquivalence (onePeriodicComplexEquivalence C)
    (stableConflationExact_onePeriodicComplexEquivalence_functor C)
    (stableConflationExact_onePeriodicComplexEquivalence_inverse C)
    ExactStructure.differentialModule_split_isFrobenius
    (ExactStructure.homologicalComplex_split_isFrobenius
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (fun i ↦ ⟨i + 1, rfl⟩))

/-- The canonical comparison from the split stable category of differential modules to the
homotopy category `K₁(C)` of one-periodic complexes, sending the stable class of a morphism of
differential modules to the homotopy class of the same morphism of one-periodic complexes. -/
noncomputable def stableToHomotopy :
    (ExactStructure.split C).differentialModule.ProjectiveStableCategory ⥤
      HomotopyCategory C (ComplexShape.up (ZMod 1)) :=
  (stableOnePeriodicComplexEquivalence C).functor ⋙
    ExactStructure.homologicalComplexSplitStableToHomotopy C (ComplexShape.up (ZMod 1))
      (fun i ↦ ⟨i + 1, rfl⟩)

/-- The comparison restricts to the homotopy quotient of one-periodic complexes on differential
modules. -/
theorem projectiveStableFunctor_comp_stableToHomotopy :
    (ExactStructure.split C).differentialModule.projectiveStableFunctor ⋙ stableToHomotopy C =
      toOnePeriodicComplex C ⋙ HomotopyCategory.quotient C (ComplexShape.up (ZMod 1)) := by
  rw [stableToHomotopy, StableConflationExact.stableEquivalence_functor,
    StableConflationExact.stableFunctor_eq_map, ← Functor.assoc,
    MorphismIdeal.quotientFunctor_comp_map, Functor.assoc,
    ExactStructure.projectiveStableFunctor_comp_homologicalComplexSplitStableToHomotopy,
    onePeriodicComplexEquivalence_functor]

/-- On objects, the comparison sends the stable class of a differential module to the homotopy
class of its one-periodic complex. -/
@[simp]
theorem stableToHomotopy_obj (M : DifferentialModule C) :
    (stableToHomotopy C).obj
        ((ExactStructure.split C).differentialModule.projectiveStableFunctor.obj M) =
      (HomotopyCategory.quotient C (ComplexShape.up (ZMod 1))).obj
        ((toOnePeriodicComplex C).obj M) :=
  Functor.congr_obj (projectiveStableFunctor_comp_stableToHomotopy C) M

/-- On morphisms, the comparison sends the stable class of a morphism of differential modules to
the homotopy class of the same morphism of one-periodic complexes. -/
@[simp]
theorem stableToHomotopy_map {M N : DifferentialModule C} (φ : M ⟶ N) :
    (stableToHomotopy C).map
        ((ExactStructure.split C).differentialModule.projectiveStableFunctor.map φ) ≫
        eqToHom (stableToHomotopy_obj C N) =
      eqToHom (stableToHomotopy_obj C M) ≫
        (HomotopyCategory.quotient C (ComplexShape.up (ZMod 1))).map
          ((toOnePeriodicComplex C).map φ) := by
  rw [← Functor.comp_map, Functor.congr_hom (projectiveStableFunctor_comp_stableToHomotopy C) φ]
  simp

/-- The stable-to-homotopy comparison preserves addition of morphisms. -/
instance : (stableToHomotopy C).Additive := by
  unfold stableToHomotopy
  rw [StableConflationExact.stableEquivalence_functor,
    StableConflationExact.stableFunctor_eq_map]
  infer_instance

/-- The comparison is an equivalence, as the composite of two equivalences. -/
instance : (stableToHomotopy C).IsEquivalence := by
  unfold stableToHomotopy
  infer_instance

/-- **The stable category of differential modules is `K₁(C)`.** The projective stable category
of differential modules with the componentwise split exact structure is equivalent to the
homotopy category of one-periodic complexes. -/
noncomputable def stableHomotopyEquivalence :
    (ExactStructure.split C).differentialModule.ProjectiveStableCategory ≌
      HomotopyCategory C (ComplexShape.up (ZMod 1)) :=
  (stableToHomotopy C).asEquivalence

/-- The functor of the stable/homotopy equivalence is the canonical comparison. -/
@[simp]
theorem stableHomotopyEquivalence_functor :
    (stableHomotopyEquivalence C).functor = stableToHomotopy C :=
  (rfl)

/-- The comparison commutes coherently with the integral shifts: Happel's stable suspension on
differential modules and the signed cyclic shift on one-periodic complexes. It is the composite
of the shift comparisons of `TauCeti.DifferentialModule.stableOnePeriodicComplexEquivalence` and
of `TauCeti.PeriodicComplex.stableToHomotopyCommShift`. -/
@[instance_reducible]
noncomputable def stableToHomotopyCommShift :
    letI := ExactStructure.differentialModule_split_isFrobenius (C := C) |>.stableHasShift
    (stableToHomotopy C).CommShift ℤ := by
  letI := ExactStructure.differentialModule_split_isFrobenius (C := C) |>.stableHasShift
  letI := ExactStructure.homologicalComplex_split_isFrobenius (C := C)
    (c := ComplexShape.up (ZMod 1)) (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩)
    (fun i ↦ ⟨i + 1, rfl⟩) |>.stableHasShift
  letI := StableConflationExact.stableEquivalenceFunctorCommShift
    (stableConflationExact_onePeriodicComplexEquivalence_functor C)
    (stableConflationExact_onePeriodicComplexEquivalence_inverse C)
    ExactStructure.differentialModule_split_isFrobenius
    (ExactStructure.homologicalComplex_split_isFrobenius
      (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (fun i ↦ ⟨i + 1, rfl⟩))
  letI := PeriodicComplex.stableToHomotopyCommShift C 1
  exact inferInstanceAs ((_ ⋙ _).CommShift ℤ)

/-- **Happel's triangulation of differential modules is the cone triangulation of `K₁(C)`.**
The comparison from the stable category of differential modules to the homotopy category of
one-periodic complexes is a triangle functor; it is an equivalence
(`TauCeti.DifferentialModule.stableHomotopyEquivalence`). -/
theorem stableToHomotopy_isTriangulated :
    letI hE := ExactStructure.differentialModule_split_isFrobenius (C := C)
    letI := hE.stableHasShift
    letI := hE.stableShiftFunctor_additive
    letI := hE.stablePretriangulated
    letI := stableToHomotopyCommShift C
    (stableToHomotopy C).IsTriangulated := by
  let hE := ExactStructure.differentialModule_split_isFrobenius (C := C)
  let hP := ExactStructure.homologicalComplex_split_isFrobenius (C := C)
    (c := ComplexShape.up (ZMod 1)) (fun j ↦ ⟨j - 1, sub_add_cancel j 1⟩) (fun i ↦ ⟨i + 1, rfl⟩)
  let hF := stableConflationExact_onePeriodicComplexEquivalence_functor C
  let hG := stableConflationExact_onePeriodicComplexEquivalence_inverse C
  -- Install the stable triangulations of both Frobenius categories and the shift comparisons of
  -- the two factors; each factor is a triangle functor, hence so is their composite.
  let := hE.stableHasShift
  let := hP.stableHasShift
  let := hE.stableShiftFunctor_additive
  let := hP.stableShiftFunctor_additive
  let := hE.stablePretriangulated
  let := hP.stablePretriangulated
  let := StableConflationExact.stableEquivalenceFunctorCommShift hF hG hE hP
  let := PeriodicComplex.stableToHomotopyCommShift C 1
  have := StableConflationExact.stableEquivalenceIsTriangulated hF hG hE hP
  have := PeriodicComplex.stableToHomotopy_isTriangulated C 1
  exact inferInstanceAs (Functor.IsTriangulated (_ ⋙ _))

/-- A triangle in the stable category of differential modules is distinguished for Happel's
triangulation exactly when its image in the homotopy category of one-periodic complexes is
distinguished for the mapping-cone triangulation. -/
theorem stableToHomotopy_mapTriangle_mem_distTriang_iff :
    letI hE := ExactStructure.differentialModule_split_isFrobenius (C := C)
    letI := hE.stableHasShift
    letI := hE.stableShiftFunctor_additive
    letI := hE.stablePretriangulated
    letI := stableToHomotopyCommShift C
    ∀ T : Triangle (ExactStructure.split C).differentialModule.ProjectiveStableCategory,
      (stableToHomotopy C).mapTriangle.obj T ∈ distTriang _ ↔ T ∈ distTriang _ := by
  let hE := ExactStructure.differentialModule_split_isFrobenius (C := C)
  let := hE.stableHasShift
  let := hE.stableShiftFunctor_additive
  let := hE.stablePretriangulated
  let := stableToHomotopyCommShift C
  have := stableToHomotopy_isTriangulated C
  exact (stableToHomotopy C).map_distinguished_iff

end TauCeti.DifferentialModule
