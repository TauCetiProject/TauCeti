/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Embedding.Restriction

/-!
# Mapping restricted homological complexes

This file provides the comparison between first restricting a homological complex along an
embedding of complex shapes and then mapping it, and first mapping the complex and then
restricting it.

## Main result

* `ComplexShape.Embedding.mapRestrictionIso`: mapping homological complexes commutes with
  restriction along a shape embedding.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace ComplexShape.Embedding

/-- Mapping a restricted complex and restricting the mapped complex have the same objects. -/
private theorem mapRestriction_obj_X
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (e : c.Embedding c') [e.IsRelIff]
    (K : HomologicalComplex C c') (i : ι) :
    ((F.mapHomologicalComplex c).obj ((e.restrictionFunctor C).obj K)).X i =
      ((e.restrictionFunctor D).obj ((F.mapHomologicalComplex c').obj K)).X i := by
  rw [Functor.mapHomologicalComplex_obj_X,
    ComplexShape.Embedding.restrictionFunctor_obj, HomologicalComplex.restriction_X,
    ComplexShape.Embedding.restrictionFunctor_obj, HomologicalComplex.restriction_X,
    Functor.mapHomologicalComplex_obj_X]

/-- The objectwise identifications between mapping after restriction and restriction after
mapping intertwine the differentials. The two functor composites are definitionally equal, but
Mathlib does not currently provide a theorem expressing that equality. The implementation-level
reduction is isolated in this private compatibility lemma. -/
private theorem mapRestriction_hom_d
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (e : c.Embedding c') [e.IsRelIff]
    (K : HomologicalComplex C c') (i j : ι) :
    eqToHom (mapRestriction_obj_X F e K i) ≫
        ((e.restrictionFunctor D).obj ((F.mapHomologicalComplex c').obj K)).d i j =
      ((F.mapHomologicalComplex c).obj ((e.restrictionFunctor C).obj K)).d i j ≫
        eqToHom (mapRestriction_obj_X F e K j) := by
  have hi : mapRestriction_obj_X F e K i = rfl := Subsingleton.elim _ _
  have hj : mapRestriction_obj_X F e K j = rfl := Subsingleton.elim _ _
  rw [hi, hj]
  change 𝟙 _ ≫ F.map (K.d (e.f i) (e.f j)) = F.map (K.d (e.f i) (e.f j)) ≫ 𝟙 _
  simp

/-- Mapping homological complexes commutes with restriction along a shape embedding. -/
noncomputable def mapRestrictionIso
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (F : C ⥤ D) [F.PreservesZeroMorphisms] (e : c.Embedding c') [e.IsRelIff]
    (K : HomologicalComplex C c') :
    (F.mapHomologicalComplex c).obj ((e.restrictionFunctor C).obj K) ≅
      (e.restrictionFunctor D).obj ((F.mapHomologicalComplex c').obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => eqToIso (mapRestriction_obj_X F e K i)) (by
      intro i j _
      exact mapRestriction_hom_d F e K i j)

end ComplexShape.Embedding
