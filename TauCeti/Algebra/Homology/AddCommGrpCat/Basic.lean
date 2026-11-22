/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Homological complexes of abelian groups

Elementwise API for homological complexes in `AddCommGrpCat`: the square of the differential
vanishes on elements (`HomologicalComplex.addCommGrpCat_d_comp_d_apply`). This is the
`AddCommGrpCat` counterpart of `HomologicalComplex.d_comp_d_apply` for complexes of modules.

It also passes between elements and the abstract cycles and homology of such a complex: an element
killed by the differential is a cycle (`HomologicalComplex.addCommGrpCat_exists_iCycles_eq`), and
a cycle with zero homology class is a boundary
(`HomologicalComplex.addCommGrpCat_exists_toCycles_eq`).
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

section Homology

variable {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex AddCommGrpCat c) {n m : ι}

/-- In a complex of abelian groups, an element of degree `n` killed by the differential to degree
`c.next n` is the underlying element of a cycle. -/
lemma addCommGrpCat_exists_iCycles_eq (hm : c.next n = m) (x : K.X n) (hx : (K.d n m).hom x = 0) :
    ∃ z : K.cycles n, (K.iCycles n).hom z = x :=
  (ShortComplex.ab_exact_iff _).1 ((ShortComplex.mk _ _ (K.iCycles_d n m)).exact_of_f_is_kernel
    (K.cyclesIsKernel n m hm)) x hx

/-- In a complex of abelian groups, a cycle of degree `n` whose homology class vanishes is a
boundary: the image under `K.toCycles m n` of an element of degree `m = c.prev n`. -/
lemma addCommGrpCat_exists_toCycles_eq (hm : c.prev n = m) (z : K.cycles n)
    (hz : (K.homologyπ n).hom z = 0) : ∃ y : K.X m, (K.toCycles m n).hom y = z := by
  have hS := (ShortComplex.mk _ _ (K.toCycles_comp_homologyπ m n)).exact_of_g_is_cokernel
    (K.homologyIsCokernel m n hm)
  rw [ShortComplex.ab_exact_iff] at hS
  exact hS z hz

end Homology

end HomologicalComplex
