/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.CatCommSq

/-!
# Adjunctions on homological complexes and homotopy categories

An adjunction between functors preserving zero morphisms induces an adjunction on complexes
of any fixed shape. Its unit, counit and transposition of chain maps are computed degreewise.
In particular, applying this construction to extension and restriction of scalars gives the
adjunction on unbounded module complexes used to derive extension of scalars.

The construction uses Mathlib's `NatTrans.mapHomologicalComplex` for the unit and counit;
no exactness, boundedness or existence of homology is required. For additive functors between
preadditive categories, the unit and counit descend through the homotopy quotient, giving
`CategoryTheory.Adjunction.mapHomotopyCategory` for any complex shape.
-/

public section

namespace CategoryTheory.Adjunction

open Limits HomologicalComplex

variable {C D : Type*} [Category* C] [Category* D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  {F : C ⥤ D} {G : D ⥤ C} [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
  (adj : F ⊣ G) {ι : Type*} (c : ComplexShape ι)

/-- An adjunction of zero-preserving functors lifts degreewise to homological complexes. -/
def mapHomologicalComplex : F.mapHomologicalComplex c ⊣ G.mapHomologicalComplex c where
  unit := (Functor.mapHomologicalComplexIdIso C c).inv ≫
    adj.unit.mapHomologicalComplex c
  counit := adj.counit.mapHomologicalComplex c ≫
    (Functor.mapHomologicalComplexIdIso D c).hom
  left_triangle_components K := by
    ext i
    simp
  right_triangle_components K := by
    ext i
    simp

/-- The unit of the lifted adjunction is the original unit in each degree. -/
@[simp]
theorem mapHomologicalComplex_unit_app_f (K : HomologicalComplex C c) (i : ι) :
    ((adj.mapHomologicalComplex c).unit.app K).f i = adj.unit.app (K.X i) := by
  simp [mapHomologicalComplex]

/-- The counit of the lifted adjunction is the original counit in each degree. -/
@[simp]
theorem mapHomologicalComplex_counit_app_f (K : HomologicalComplex D c) (i : ι) :
    ((adj.mapHomologicalComplex c).counit.app K).f i = adj.counit.app (K.X i) := by
  simp [mapHomologicalComplex]

/-- Transposition of a chain map is transposition of its components. -/
@[simp]
theorem mapHomologicalComplex_homEquiv_f
    (K : HomologicalComplex C c) (L : HomologicalComplex D c)
    (f : (F.mapHomologicalComplex c).obj K ⟶ L) (i : ι) :
    ((adj.mapHomologicalComplex c).homEquiv K L f).f i =
      adj.homEquiv (K.X i) (L.X i) (f.f i) := by
  simp [homEquiv_unit]

/-- Inverse transposition of a chain map is inverse transposition of its components. -/
@[simp]
theorem mapHomologicalComplex_homEquiv_symm_f
    (K : HomologicalComplex C c) (L : HomologicalComplex D c)
    (f : K ⟶ (G.mapHomologicalComplex c).obj L) (i : ι) :
    (((adj.mapHomologicalComplex c).homEquiv K L).symm f).f i =
      (adj.homEquiv (K.X i) (L.X i)).symm (f.f i) := by
  simp [homEquiv_counit]

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

/-- The functor induced by an additive functor on homotopy categories commutes with the quotient
functors. -/
instance catCommSqMapHomotopyCategory {V W : Type*} [Category* V] [Preadditive V]
    [Category* W] [Preadditive W] (F : V ⥤ W) [F.Additive] {ι : Type*} (c : ComplexShape ι) :
    CatCommSq (F.mapHomologicalComplex c) (HomotopyCategory.quotient V c)
      (HomotopyCategory.quotient W c) (F.mapHomotopyCategory c) :=
  ⟨(F.mapHomotopyCategoryFactors c).symm⟩

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] (adj : F ⊣ G)
  {ι : Type*} (c : ComplexShape ι)

/-- An adjunction of additive functors descends to homotopy categories of any complex shape. -/
def mapHomotopyCategory : F.mapHomotopyCategory c ⊣ G.mapHomotopyCategory c where
  unit := Quotient.natTransLift _
    (Functor.whiskerRight (adj.mapHomologicalComplex c).unit (HomotopyCategory.quotient C c))
  counit := Quotient.natTransLift _
    (Functor.whiskerRight (adj.mapHomologicalComplex c).counit (HomotopyCategory.quotient D c))
  left_triangle_components K := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    -- The quotient lift computes componentwise; express both factors as quotient maps.
    change (HomotopyCategory.quotient D c).map _ ≫ (HomotopyCategory.quotient D c).map _ = _
    simp only [HomotopyCategory.quotient_obj_as]
    rw [← Functor.map_comp, (adj.mapHomologicalComplex c).left_triangle_components]
    exact (HomotopyCategory.quotient D c).map_id _
  right_triangle_components K := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    -- The quotient lift computes componentwise; express both factors as quotient maps.
    change (HomotopyCategory.quotient C c).map _ ≫ (HomotopyCategory.quotient C c).map _ = _
    simp only [HomotopyCategory.quotient_obj_as]
    rw [← Functor.map_comp, (adj.mapHomologicalComplex c).right_triangle_components]
    exact (HomotopyCategory.quotient C c).map_id _

/-- The unit on homotopy categories is the class of the degreewise unit on complexes. -/
@[simp]
lemma mapHomotopyCategory_unit_app (K : HomologicalComplex C c) :
    (adj.mapHomotopyCategory c).unit.app ((HomotopyCategory.quotient C c).obj K) =
      (HomotopyCategory.quotient C c).map ((adj.mapHomologicalComplex c).unit.app K) := (rfl)

/-- The counit on homotopy categories is the class of the degreewise counit on complexes. -/
@[simp]
lemma mapHomotopyCategory_counit_app (K : HomologicalComplex D c) :
    (adj.mapHomotopyCategory c).counit.app ((HomotopyCategory.quotient D c).obj K) =
      (HomotopyCategory.quotient D c).map ((adj.mapHomologicalComplex c).counit.app K) := (rfl)

end CategoryTheory.Adjunction
