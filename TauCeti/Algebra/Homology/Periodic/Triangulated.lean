/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Periodic.CommShift
public import TauCeti.Algebra.Homology.Periodic.Connecting
public import TauCeti.CategoryTheory.Exact.Stable.Triangulated

/-!
# Periodic homotopy categories are triangulated

The componentwise split exact category of cyclic cochain complexes is Frobenius, and its
stable category is equivalent to Mathlib's homotopy category. The equivalence commutes with
all integral shifts, retaining the signed cyclic shift on the homotopy category. Transporting
Happel's triangulation along it makes the periodic homotopy category triangulated.

Its distinguished triangles are precisely the triangles isomorphic to images of distinguished
stable triangles. This description supplies the categorical structure for comparison with
explicit mapping-cone triangles. `mappingCone_mem_distTriang` proves the mapping-cone triangle
is distinguished, and `mem_distTriang_iff` shows every distinguished triangle is isomorphic to one.
No abelianity or positive-period assumption is needed; period
zero gives integer indexing.

`homotopyCategory_mem_distTriang_iff` characterizes distinguished triangles as images of
standard stable triangles of componentwise split conflations, up to isomorphism.
`homotopyCategory_map_stableConflationTriangle_mem_distTriang` supplies the corresponding
introduction rule.

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

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex

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
noncomputable instance homotopyCategoryPretriangulated :
    Pretriangulated (HomotopyCategory C (ComplexShape.up (ZMod n))) :=
  (hE).pretriangulatedOfCommShiftEquivalence F (stableToHomotopyCommShift C n)

/-- The canonical equivalence from the split stable category to the periodic homotopy category
is a triangle functor. -/
theorem stableToHomotopy_isTriangulated :
    letI := (hE).stableHasShift
    letI := (hE).stableShiftFunctor_additive
    letI := (hE).stablePretriangulated
    letI := stableToHomotopyCommShift C n
    (F).IsTriangulated :=
  (hE).isTriangulated_functor_ofCommShiftEquivalence F (stableToHomotopyCommShift C n)

/-- The periodic homotopy category with its signed cyclic shift is triangulated. -/
instance homotopyCategoryIsTriangulated :
    IsTriangulated (HomotopyCategory C (ComplexShape.up (ZMod n))) :=
  (hE).isTriangulated_ofCommShiftEquivalence F (stableToHomotopyCommShift C n)

/-- The image of the standard stable triangle of a componentwise split conflation is
distinguished in the periodic homotopy category. -/
theorem homotopyCategory_map_stableConflationTriangle_mem_distTriang
    (S : ShortComplex (CochainComplex C (ZMod n))) (hS : (E).Conflation S) :
    letI := (hE).stableHasShift
    letI := stableToHomotopyCommShift C n
    (F).mapTriangle.obj ((hE).stableConflationTriangle S hS) ∈
      distTriang (HomotopyCategory C (ComplexShape.up (ZMod n))) :=
  (hE).map_stableConflationTriangle_mem_distTriang F (stableToHomotopyCommShift C n) S hS

/-- A triangle in the periodic homotopy category is distinguished exactly when it is
isomorphic to the image of the standard stable triangle of a componentwise split conflation. -/
theorem homotopyCategory_mem_distTriang_iff
    (T : Triangle (HomotopyCategory C (ComplexShape.up (ZMod n)))) :
    letI := (hE).stableHasShift
    letI := stableToHomotopyCommShift C n
    T ∈ distTriang (HomotopyCategory C (ComplexShape.up (ZMod n))) ↔
      ∃ (S : ShortComplex (CochainComplex C (ZMod n))) (hS : (E).Conflation S),
        Nonempty (T ≅ (F).mapTriangle.obj ((hE).stableConflationTriangle S hS)) :=
  (hE).mem_distTriang_ofCommShiftEquivalence_iff F (stableToHomotopyCommShift C n) T

variable {C n}

section MappingCone

omit [HasZeroObject C]

/-- The mapping-cone triangle of a periodic chain map in the homotopy category. Its last
morphism is the negative cone projection, followed by the quotient's shift comparison. -/
@[expose, implicit_reducible]
noncomputable def mappingConeTriangle {X Y : CochainComplex C (ZMod n)} (f : X ⟶ Y) :
    Triangle (HomotopyCategory C (ComplexShape.up (ZMod n))) :=
  (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).mapTriangle.obj
    (Triangle.mk f (homotopyCofiber.inr f) (-coneProjection f))

/-- The first vertex of the mapping-cone triangle is the source's homotopy class. -/
@[simp]
theorem mappingConeTriangle_obj₁ {X Y : CochainComplex C (ZMod n)} (f : X ⟶ Y) :
    (mappingConeTriangle f).obj₁ =
      (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).obj X := rfl

/-- The second vertex of the mapping-cone triangle is the target's homotopy class. -/
@[simp]
theorem mappingConeTriangle_obj₂ {X Y : CochainComplex C (ZMod n)} (f : X ⟶ Y) :
    (mappingConeTriangle f).obj₂ =
      (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).obj Y := rfl

/-- The third vertex of the mapping-cone triangle is the cone's homotopy class. -/
@[simp]
theorem mappingConeTriangle_obj₃ {X Y : CochainComplex C (ZMod n)} (f : X ⟶ Y) :
    (mappingConeTriangle f).obj₃ =
      (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).obj (homotopyCofiber f) := rfl

/-- The first arrow of the mapping-cone triangle is the original chain map's homotopy class. -/
@[simp]
theorem mappingConeTriangle_mor₁ {X Y : CochainComplex C (ZMod n)} (f : X ⟶ Y) :
    (mappingConeTriangle f).mor₁ =
      (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).map f := rfl

/-- The second arrow of the mapping-cone triangle is the cone inclusion's homotopy class. -/
@[simp]
theorem mappingConeTriangle_mor₂ {X Y : CochainComplex C (ZMod n)} (f : X ⟶ Y) :
    (mappingConeTriangle f).mor₂ =
      (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).map (homotopyCofiber.inr f) := rfl

/-- The third arrow of the mapping-cone triangle is minus the cone projection, with the
quotient's shift comparison. -/
@[simp]
theorem mappingConeTriangle_mor₃ {X Y : CochainComplex C (ZMod n)} (f : X ⟶ Y) :
    (mappingConeTriangle f).mor₃ =
      (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).map (-coneProjection f) ≫
        ((HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).commShiftIso (1 : ℤ)).hom.app X :=
  rfl

end MappingCone

/-- **Mapping-cone triangles are distinguished.** For a morphism `f : X ⟶ Y` of periodic
complexes, the image in the homotopy category of the triangle
`X ⟶ Y ⟶ cone(f) ⟶ X⟦1⟧`, whose last map is minus the cone projection, is distinguished. -/
theorem mappingCone_mem_distTriang {X Y : CochainComplex C (ZMod n)} (f : X ⟶ Y) :
    mappingConeTriangle f ∈
      distTriang (HomotopyCategory C (ComplexShape.up (ZMod n))) := by
  dsimp only [mappingConeTriangle]
  let := (hE).stableHasShift
  let := (hE).stableShiftFunctor_additive
  let := (hE).stablePretriangulated
  let := stableToHomotopyCommShift C n
  have := stableToHomotopy_isTriangulated C n
  refine isomorphic_distinguished _ ((F).map_distinguished _ (mappingCone_distinguished f)) _ ?_
  refine Triangle.isoMk _ _ (eqToIso (by simp)) (eqToIso (by simp)) (eqToIso (by simp)) ?_ ?_ ?_
  · simp [← Functor.comp_map, Functor.congr_hom
      (ExactStructure.projectiveStableFunctor_comp_homologicalComplexSplitStableToHomotopy C _ _)]
  · simp [← Functor.comp_map, Functor.congr_hom
      (ExactStructure.projectiveStableFunctor_comp_homologicalComplexSplitStableToHomotopy C _ _)]
  · simp only [Triangle.mk_obj₁, Triangle.mk_obj₃, Functor.mapTriangle_obj, Triangle.mk_mor₃,
      eqToIso.hom, stableToHomotopyCommShift_iso_one, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, splitStableShiftObjIso_hom,
      Functor.map_comp, Functor.map_neg, Preadditive.neg_comp, Category.assoc]
    simp only [stableSuspensionCompStableToHomotopyIso_hom_app, ← Functor.map_comp_assoc,
      Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
    -- The identity is typed at the image of the shifted complex, which is the displayed codomain
    -- of the cone projection only definitionally.
    erw [Category.comp_id]
    simp [← Functor.comp_map, Functor.congr_hom
      (ExactStructure.projectiveStableFunctor_comp_homologicalComplexSplitStableToHomotopy
        C _ _), eqToHom_map]

/-- **The triangulation of the periodic homotopy category is the mapping-cone triangulation.**
A triangle is distinguished exactly when it is isomorphic to the image of a mapping-cone triangle
`X ⟶ Y ⟶ cone(f) ⟶ X⟦1⟧` of periodic complexes, whose last map is minus the cone projection. -/
theorem mem_distTriang_iff (T : Triangle (HomotopyCategory C (ComplexShape.up (ZMod n)))) :
    T ∈ distTriang (HomotopyCategory C (ComplexShape.up (ZMod n))) ↔
      ∃ (X Y : CochainComplex C (ZMod n)) (f : X ⟶ Y),
        Nonempty (T ≅ mappingConeTriangle f) := by
  refine ⟨fun hT ↦ ?_, fun ⟨X, Y, f, ⟨e⟩⟩ ↦
    isomorphic_distinguished _ (mappingCone_mem_distTriang f) _ e⟩
  obtain ⟨X, hX⟩ := HomotopyCategory.quotient_obj_surjective T.obj₁
  obtain ⟨Y, hY⟩ := HomotopyCategory.quotient_obj_surjective T.obj₂
  obtain ⟨f, hf⟩ := (HomotopyCategory.quotient C (ComplexShape.up (ZMod n))).map_surjective
    (eqToHom hX ≫ T.mor₁ ≫ eqToHom hY.symm)
  exact ⟨X, Y, f, ⟨(isoTriangleOfIso₁₂ _ _ (mappingCone_mem_distTriang f) hT
    (eqToIso hX) (eqToIso hY) (by simp [hf])).symm⟩⟩


end TauCeti.PeriodicComplex
