/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-!
# Exactness of additive and linear Hom complexes

Mathlib's cohomology-class equivalences identify exactness of a Hom complex with the
subsingleton condition on its cohomology classes. In a linear preadditive category, this
also shows that the additive and linear Hom complexes are exact in the same degrees,
and hence are acyclic together. No abelian hypothesis on the category is needed.
-/

public section

open CategoryTheory Limits CochainComplex CochainComplex.HomComplex

namespace TauCeti

universe v u w

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K L : CochainComplex C ℤ}

/-- A Hom complex is exact in degree `n` precisely when its degree-`n` cohomology classes
form a subsingleton. -/
theorem exactAt_homComplex_iff_subsingleton_cohomologyClass (n : ℤ) :
    (HomComplex K L).ExactAt n ↔ Subsingleton (CohomologyClass K L n) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology,
    AddCommGrpCat.isZero_iff_subsingleton,
    (homologyAddEquiv K L n).toEquiv.subsingleton_congr]

variable (R : Type w) [Ring R] [Linear R C]

/-- The linear and additive Hom complexes are exact in the same integer degrees. -/
theorem exactAt_linearHomComplex_iff (n : ℤ) :
    (linearHomComplex R K L).ExactAt n ↔ (HomComplex K L).ExactAt n := by
  rw [exactAt_homComplex_iff_subsingleton_cohomologyClass,
    HomologicalComplex.exactAt_iff_isZero_homology,
    ModuleCat.isZero_iff_subsingleton,
    (homologyLinearEquiv R K L n).toEquiv.subsingleton_congr]

/-- The linear Hom complex is acyclic exactly when the additive Hom complex is acyclic. -/
theorem acyclic_linearHomComplex_iff :
    (linearHomComplex R K L).Acyclic ↔ (HomComplex K L).Acyclic :=
  forall_congr' fun n ↦ exactAt_linearHomComplex_iff R n

end TauCeti
