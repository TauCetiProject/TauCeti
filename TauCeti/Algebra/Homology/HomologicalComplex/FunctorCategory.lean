/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Cycles of complexes of functors, elementwise

For a homological complex `K` in a functor category `C ⥤ D` with concrete `D`, for instance a
complex of presheaves of abelian groups, this file records how the cycles of `K` look on the
elements of the values `(K.X i).obj U`:

* `HomologicalComplex.iCycles_app_toCycles_app`: the cycle `toCycles x` of an element `x` is
  the element `d x`.
* `HomologicalComplex.exists_iCycles_app_eq`: when `D` is the category of abelian groups, an
  element killed by the differential comes from a cycle.
-/

public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {C : Type*} [Category* C] {ι : Type*} {c : ComplexShape ι}

section Concrete

variable {D : Type*} [Category* D] [HasZeroMorphisms D] {FD : D → D → Type*} {CD : D → Type*}
  [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
  (K : HomologicalComplex (C ⥤ D) c)

/-- The cycle `toCycles x` of an element `x` of a complex of functors is the element `d x`. -/
lemma iCycles_app_toCycles_app (i j : ι) [K.HasHomology j] {U : C} (x : ToType ((K.X i).obj U)) :
    (K.iCycles j).app U ((K.toCycles i j).app U x) = (K.d i j).app U x := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, toCycles_i]

end Concrete

/-- An element of a complex of functors to abelian groups that is killed by the differential comes
from a cycle. -/
lemma exists_iCycles_app_eq (K : HomologicalComplex (C ⥤ AddCommGrpCat) c) {i : ι} (j : ι)
    (hij : c.next i = j) [K.HasHomology i] {U : C} (s : (K.X i).obj U)
    (hs : (K.d i j).app U s = 0) :
    ∃ z, (K.iCycles i).app U z = s := by
  let S := ShortComplex.mk (K.iCycles i) (K.d i j) (K.iCycles_d i j)
  have hS : S.Exact := S.exact_of_f_is_kernel (K.cyclesIsKernel i j hij)
  exact (ShortComplex.ab_exact_iff _).1 (hS.map ((evaluation C AddCommGrpCat).obj U)) s hs

end HomologicalComplex
