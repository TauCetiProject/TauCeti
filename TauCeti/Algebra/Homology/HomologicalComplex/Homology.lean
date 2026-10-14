/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Homology in the category of homological complexes

If a category with finite limits and finite colimits has homology, so does its category
of homological complexes. The comparison between left and right homology is an
isomorphism because it is an isomorphism after evaluation in every degree.

This permits categorical exactness statements about sequences of complexes even when
the coefficient category is not abelian, as for topological modules. Mathlib's
`ShortComplex.map_leftRightHomologyComparison'` transports the comparison to each degree,
and `HomologicalComplex.Hom.isIso_of_components` assembles the resulting isomorphisms.
-/

public section

open CategoryTheory Limits

namespace TauCeti.HomologicalComplex

variable {C ι : Type*} [Category* C] [HasZeroMorphisms C]
  [HasFiniteLimits C] [HasFiniteColimits C] [CategoryWithHomology C] (c : ComplexShape ι)

/-- Homological complexes in a category with homology and finite limits and colimits
again form a category with homology. This also applies to nonabelian categories. -/
instance (priority := 100) categoryWithHomology :
    CategoryWithHomology (HomologicalComplex C c) := by
  constructor
  intro S
  let h₁ := S.leftHomologyData
  let h₂ := S.rightHomologyData
  let f := ShortComplex.leftRightHomologyComparison' h₁ h₂
  have hf (i : ι) : IsIso (f.f i) := by
    let F := HomologicalComplex.eval C c i
    have hmap : F.map f = ShortComplex.leftRightHomologyComparison' (h₁.map F) (h₂.map F) :=
      ShortComplex.map_leftRightHomologyComparison' F h₁ h₂
    -- Evaluation of a complex morphism is its component by definition.
    rw [show f.f i = F.map f from rfl, hmap]
    exact ShortComplex.isIso_leftRightHomologyComparison' (h₁.map F) (h₂.map F)
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact ShortComplex.HasHomology.mk' (.ofIsIsoLeftRightHomologyComparison' h₁ h₂)

end TauCeti.HomologicalComplex
