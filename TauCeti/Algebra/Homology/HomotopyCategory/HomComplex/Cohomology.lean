/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-!
# Exactness of additive Hom complexes

Mathlib's cohomology-class equivalence identifies exactness of a Hom complex with the
subsingleton condition on its cohomology classes. No abelian hypothesis on the category is
needed.
-/

public section

open CategoryTheory Limits CochainComplex CochainComplex.HomComplex

namespace TauCeti

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K L : CochainComplex C ℤ}

/-- A Hom complex is exact in degree `n` precisely when its degree-`n` cohomology classes
form a subsingleton. -/
theorem exactAt_homComplex_iff_subsingleton_cohomologyClass (n : ℤ) :
    (HomComplex K L).ExactAt n ↔ Subsingleton (CohomologyClass K L n) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology,
    AddCommGrpCat.isZero_iff_subsingleton,
    (homologyAddEquiv K L n).toEquiv.subsingleton_congr]

end TauCeti
