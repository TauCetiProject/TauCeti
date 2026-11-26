/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Presentation.Perfect
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Mathieu
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Mathieu.TwentyFour.Presentation
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Mathieu.TwentyThree

/-!
# Perfectness of the five Mathieu presentations

The exact presentations of `M₁₁`, `M₁₂`, `M₂₂`, `M₂₃`, and `M₂₄` are perfect. For `M₂₄` the
relators `a²`, `b³` and `(ab)²³` have pairwise coprime exponents, so
`TauCeti.GroupPresentation.isPerfect_of_coprime` applies. For the other four, integer
combinations of the exponent-sum vectors of a few relators give `(1, 0)` and `(0, 1)`, and
`TauCeti.GroupPresentation.isPerfect_of_expSum_two` applies; each proof lists its coefficients.

Nothing here establishes finiteness, orders, or simplicity of the presented groups.
-/

public section

namespace TauCeti.Sporadic.Mathieu

/-- The exact transcribed `M₁₁` presentation equals its commutator subgroup. -/
theorem m11_isPerfect : Group.IsPerfect m11Presentation.Group :=
  -- The first two relators have exponent sums (-4, 5) and (1, -1).
  GroupPresentation.isPerfect_of_expSum_two _ m11Presentation_generatorCount [1, 5] [1, 4]
    (by simp) (by simp) (by simp) (by simp)

/-- The exact transcribed `M₁₂` presentation equals its commutator subgroup. -/
theorem m12_isPerfect : Group.IsPerfect m12Presentation.Group :=
  -- The three relators have exponent sums (3, -3), (5, 6) and (6, 4).
  GroupPresentation.isPerfect_of_expSum_two _ m12Presentation_generatorCount [6, 11, -12]
    [-5, -9, 10] (by simp) (by simp) (by simp) (by simp)

/-- The exact transcribed `M₂₂` presentation equals its commutator subgroup. -/
theorem m22_isPerfect : Group.IsPerfect m22Presentation.Group :=
  -- The first two relators have exponent sums (2, 3) and (1, 1).
  GroupPresentation.isPerfect_of_expSum_two _ m22Presentation_generatorCount [-1, 3] [1, -2]
    (by simp) (by simp) (by simp) (by simp)

/-- The exact transcribed `M₂₃` presentation equals its commutator subgroup. -/
theorem m23_isPerfect : Group.IsPerfect m23Presentation.Group :=
  -- Relators 0, 1, 2 and 6 have exponent sums (2, 0), (0, 4), (23, 23) and (15, 4).
  GroupPresentation.isPerfect_of_expSum_two _ m23Presentation_generatorCount
    [-7, -1, 0, 0, 0, 0, 1] [4, 5, -1, 0, 0, 0, 1] (by simp) (by simp) (by simp) (by simp)

/-- The exact transcribed `M₂₄` presentation equals its commutator subgroup. -/
theorem m24_isPerfect : Group.IsPerfect m24Presentation.Group :=
  GroupPresentation.isPerfect_of_coprime _ m24Presentation_generatorCount (a := 2) (b := 3)
    (c := 23) (by simp) (by simp) (by simp) (by norm_num) (by norm_num) (by norm_num)

end TauCeti.Sporadic.Mathieu
