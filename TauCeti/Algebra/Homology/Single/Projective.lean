/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Projectivity of the homology of a single complex

The complex `(single C c i).obj P` concentrated in degree `i` has homology `P` in degree `i`
and zero in every other degree. So its homology is projective in every degree when `P` is
(`HomologicalComplex.projective_single_obj_homology`). This complements Mathlib's instance for
the terms of a single complex, in `Mathlib.Algebra.Homology.HomologicalComplexAbelian`.
-/

public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι)

/-- The homology of a complex concentrated in one degree on a projective object is projective in
every degree. -/
instance projective_single_obj_homology (i j : ι) (P : C) [Projective P] :
    Projective (((single C c i).obj P).homology j) := by
  by_cases hij : j = i
  · subst hij
    exact Projective.of_iso (singleObjHomologySelfIso c j P).symm inferInstance
  · exact (isZero_single_obj_homology c i P j hij).projective

end HomologicalComplex
