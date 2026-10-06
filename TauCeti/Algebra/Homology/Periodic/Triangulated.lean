/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.CommShift
public import TauCeti.CategoryTheory.Exact.Stable.Triangulated
public import TauCeti.CategoryTheory.Localization.Triangulated

/-!
# Periodic homotopy categories are triangulated

The componentwise split exact category of cyclic cochain complexes is Frobenius, and its
stable category is equivalent to Mathlib's homotopy category. The equivalence commutes with
all integral shifts, retaining the signed cyclic shift on the homotopy category. Transporting
Happel's triangulation along it makes the periodic homotopy category triangulated.

Its distinguished triangles are precisely the triangles isomorphic to images of distinguished
stable triangles. This description supplies the categorical structure for comparison with
explicit mapping-cone triangles. No abelianity or positive-period assumption is needed; period
zero gives integer indexing.

`HomotopyCategory.mem_distTriang_iff` characterizes distinguished triangles as images of
standard stable triangles of componentwise split conflations, up to isomorphism.
`HomotopyCategory.mk_distinguished_of_conflation` supplies the corresponding introduction rule.

The transport follows `TauCeti.CommutativeAlgebra.MatrixFactorization.Triangulated`, using
Mathlib's localization at isomorphisms.

## References

* D. Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, Chapter I, Section 2, Theorem 2.6.
* B. Keller, *Chain complexes and stable categories*, Manuscripta Mathematica **67**
  (1990), 379–417, Section 1.
* T. Stai, *The triangulated hull of periodic complexes*, Mathematical Research Letters **25**
  (2018), 199–236, Section 3.
-/

public section

universe v u

namespace TauCeti.PeriodicComplex

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryBiproducts C] (n : ℕ)

local notation "hE" => ExactStructure.homologicalComplex_split_isFrobenius
  (C := C) (c := ComplexShape.up (ZMod n))
  (fun j => Exists.intro (j - 1) (sub_add_cancel j 1))
  (fun i => Exists.intro (i + 1) rfl)
local notation "F" => ExactStructure.homologicalComplexSplitStableToHomotopy C
  (ComplexShape.up (ZMod n)) (fun i => Exists.intro (i + 1) rfl)
local notation "E" => ExactStructure.homologicalComplex (ExactStructure.split C)
  (ComplexShape.up (ZMod n))

/-- The periodic homotopy category is pretriangulated, with distinguished triangles transported
from the componentwise split stable category and the existing signed cyclic shift. -/
noncomputable instance HomotopyCategory.instPretriangulated :
    Pretriangulated (HomotopyCategory C (ComplexShape.up (ZMod n))) :=
  letI := (hE).stableHasShift
  letI := (hE).stableShiftFunctor_additive
  letI := (hE).stablePretriangulated
  letI := stableToHomotopyCommShift C n
  Triangulated.Localization.pretriangulated F (MorphismProperty.isomorphisms _)

/-- The canonical equivalence from the split stable category to the periodic homotopy category
is a triangle functor. -/
theorem stableToHomotopy_isTriangulated :
    letI := (hE).stableHasShift
    letI := (hE).stableShiftFunctor_additive
    letI := (hE).stablePretriangulated
    letI := stableToHomotopyCommShift C n
    (F).IsTriangulated :=
  letI := (hE).stableHasShift
  letI := (hE).stableShiftFunctor_additive
  letI := (hE).stablePretriangulated
  letI := stableToHomotopyCommShift C n
  Triangulated.Localization.isTriangulated_functor F (MorphismProperty.isomorphisms _)

/-- The periodic homotopy category with its signed cyclic shift is triangulated. -/
instance HomotopyCategory.instIsTriangulated :
    IsTriangulated (HomotopyCategory C (ComplexShape.up (ZMod n))) :=
  letI := (hE).stableHasShift
  letI := (hE).stableShiftFunctor_additive
  letI := (hE).stablePretriangulated
  letI := stableToHomotopyCommShift C n
  haveI := (hE).stableIsTriangulated
  haveI := stableToHomotopy_isTriangulated C n
  Triangulated.Localization.isTriangulated F (MorphismProperty.isomorphisms _)

/-- The image of the standard stable triangle of a componentwise split conflation is
distinguished in the periodic homotopy category. -/
theorem HomotopyCategory.mk_distinguished_of_conflation
    (S : ShortComplex (CochainComplex C (ZMod n))) (hS : (E).Conflation S) :
    letI := (hE).stableHasShift
    letI := stableToHomotopyCommShift C n
    (F).mapTriangle.obj ((hE).stableConflationTriangle S hS) ∈
      distTriang (HomotopyCategory C (ComplexShape.up (ZMod n))) := by
  let := (hE).stableHasShift
  let := (hE).stableShiftFunctor_additive
  let := (hE).stablePretriangulated
  let := stableToHomotopyCommShift C n
  have := stableToHomotopy_isTriangulated C n
  apply (F).map_distinguished
  rw [ExactStructure.IsFrobenius.stablePretriangulated_distinguishedTriangles]
  exact (hE).stableConflationTriangle_mem S hS

/-- A triangle in the periodic homotopy category is distinguished exactly when it is
isomorphic to the image of the standard stable triangle of a componentwise split conflation. -/
theorem HomotopyCategory.mem_distTriang_iff
    (T : Triangle (HomotopyCategory C (ComplexShape.up (ZMod n)))) :
    letI := (hE).stableHasShift
    letI := stableToHomotopyCommShift C n
    T ∈ distTriang (HomotopyCategory C (ComplexShape.up (ZMod n))) ↔
      ∃ (S : ShortComplex (CochainComplex C (ZMod n))) (hS : (E).Conflation S),
        Nonempty (T ≅ (F).mapTriangle.obj ((hE).stableConflationTriangle S hS)) := by
  let := (hE).stableHasShift
  let := (hE).stableShiftFunctor_additive
  let := (hE).stablePretriangulated
  let := stableToHomotopyCommShift C n
  have := stableToHomotopy_isTriangulated C n
  refine ⟨fun hT => ?_, fun ⟨S, hS, ⟨e⟩⟩ =>
    isomorphic_distinguished _ (HomotopyCategory.mk_distinguished_of_conflation C n S hS) _ e⟩
  obtain ⟨T', e, hT'⟩ := ((F).distTriang_iff T).1 hT
  rw [ExactStructure.IsFrobenius.stablePretriangulated_distinguishedTriangles] at hT'
  obtain ⟨S, hS, ⟨e'⟩⟩ := ((hE).mem_stableDistinguishedTriangles_iff T').1 hT'
  exact ⟨S, hS, ⟨e ≪≫ (F).mapTriangle.mapIso e'⟩⟩

end TauCeti.PeriodicComplex
