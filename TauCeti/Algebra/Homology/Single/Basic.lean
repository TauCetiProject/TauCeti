/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Single

/-!
# Chain maps into single complexes

The single complex `(HomologicalComplex.single C c j).obj A` is zero away from degree `j`, so
every chain map into it vanishes in the degrees `i ≠ j`
(`HomologicalComplex.Hom.to_single_f_eq_zero`). For instance, an augmentation
`K ⟶ (ChainComplex.single₀ C).obj A` vanishes in positive degrees.
-/

public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] {c : ComplexShape ι}

/-- Every chain map into the single complex on `A` in degree `j` vanishes in degrees `i ≠ j`,
since its target does. -/
@[simp]
lemma Hom.to_single_f_eq_zero {K : HomologicalComplex C c} {j : ι} {A : C}
    (f : K ⟶ (single C c j).obj A) {i : ι} (hi : i ≠ j) : f.f i = 0 :=
  (isZero_single_obj_X c j A i hi).eq_of_tgt _ _

end HomologicalComplex
