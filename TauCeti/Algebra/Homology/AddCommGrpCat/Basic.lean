/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.HomologicalComplex

/-!
# Homological complexes of abelian groups

Elementwise API for homological complexes in `AddCommGrpCat`: the square of the differential
vanishes on elements (`HomologicalComplex.addCommGrpCat_d_comp_d_apply`). This is the
`AddCommGrpCat` counterpart of `HomologicalComplex.d_comp_d_apply` for complexes of modules.
-/

public section

open CategoryTheory

namespace HomologicalComplex

/-- In a complex of abelian groups the differential of a differential vanishes, on elements. -/
@[simp]
theorem addCommGrpCat_d_comp_d_apply {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex AddCommGrpCat c) (i j k : ι) (x : K.X i) :
    (K.d j k).hom ((K.d i j).hom x) = 0 := by
  rw [← AddCommGrpCat.comp_apply, K.d_comp_d, AddCommGrpCat.zero_apply]

end HomologicalComplex
