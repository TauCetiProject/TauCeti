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
restricting it. This transports mapped or forgotten complexes through shape reindexing, allowing
results about a restricted complex to be compared with the corresponding restriction of the
mapped complex.

## Main result

* `ComplexShape.Embedding.mapRestrictionIso`: mapping homological complexes commutes with
  restriction along a shape embedding.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace ComplexShape.Embedding

/-- Mapping homological complexes commutes with restriction along a shape embedding. The two
composites have definitionally equal objects, so each component is an identity morphism. -/
@[expose, simps!]
noncomputable def mapRestrictionIso
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (F : C ⥤ D) [F.PreservesZeroMorphisms] [e.IsRelIff]
    (K : HomologicalComplex C c') :
    (F.mapHomologicalComplex c).obj ((e.restrictionFunctor C).obj K) ≅
      (e.restrictionFunctor D).obj ((F.mapHomologicalComplex c').obj K) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j _
    -- Both differentials unfold to `F.map (K.d (e.f i) (e.f j))`; Mathlib has no lemma for this.
    change 𝟙 _ ≫ F.map (K.d (e.f i) (e.f j)) = F.map (K.d (e.f i) (e.f j)) ≫ 𝟙 _
    simp)

end ComplexShape.Embedding
