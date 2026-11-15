/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Adjunctions on homological complexes

An adjunction between functors preserving zero morphisms induces an adjunction on complexes
of any fixed shape. Its unit, counit and transposition of chain maps are computed degreewise.
In particular, applying this construction to extension and restriction of scalars gives the
adjunction on unbounded module complexes used to derive extension of scalars.

The construction uses Mathlib's `NatTrans.mapHomologicalComplex` for the unit and counit;
no exactness, boundedness or existence of homology is required.
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
