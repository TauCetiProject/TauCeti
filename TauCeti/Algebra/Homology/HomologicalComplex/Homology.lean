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

If a category with equalizers and coequalizers has homology, so does its category
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
  [HasEqualizers C] [HasCoequalizers C] [CategoryWithHomology C] (c : ComplexShape ι)

/-- Homological complexes in a category with homology, equalizers and coequalizers
again form a category with homology. This also applies to nonabelian categories. -/
instance (priority := 100) categoryWithHomology :
    CategoryWithHomology (HomologicalComplex C c) where
  hasHomology S := by
    let h₁ := S.leftHomologyData
    let h₂ := S.rightHomologyData
    have (i : ι) : IsIso ((ShortComplex.leftRightHomologyComparison' h₁ h₂).f i) := by
      -- Evaluation preserves kernels and cokernels, as these are computed degreewise.
      have : (HomologicalComplex.eval C c i).PreservesHomology := {}
      rw [← HomologicalComplex.eval_map, ShortComplex.map_leftRightHomologyComparison']
      exact ShortComplex.isIso_leftRightHomologyComparison' _ _
    have : IsIso (ShortComplex.leftRightHomologyComparison' h₁ h₂) :=
      HomologicalComplex.Hom.isIso_of_components _
    exact .mk' (.ofIsIsoLeftRightHomologyComparison' h₁ h₂)

end TauCeti.HomologicalComplex
