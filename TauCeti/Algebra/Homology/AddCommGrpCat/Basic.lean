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

The cycles and homology of such a complex are described on elements as well: the inclusion of the
cycles is injective, an element killed by the differential is a cycle
(`HomologicalComplex.addCommGrpCat_exists_iCycles_eq`), the class map onto the homology is
surjective and commutes with homology maps
(`HomologicalComplex.addCommGrpCat_homologyMap_homologyπ_apply`), and a cycle has zero class
exactly when it is a boundary (`HomologicalComplex.addCommGrpCat_homologyπ_eq_zero_iff`). These
are the `AddCommGrpCat` counterparts of the corresponding lemmas for complexes of modules in
`TauCeti.Algebra.Homology.ModuleCat.Basic`.
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

variable {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex AddCommGrpCat c) (n : ι)

/-- The inclusion of the degree-`n` cycles of a complex of abelian groups into its degree-`n` term
is injective. -/
lemma addCommGrpCat_iCycles_injective : Function.Injective (K.iCycles n).hom :=
  (AddCommGrpCat.mono_iff_injective _).1 inferInstance

variable {n} in
/-- In a complex of abelian groups, an element of degree `n` killed by the differential to degree
`c.next n` is the underlying element of a cycle. -/
lemma addCommGrpCat_exists_iCycles_eq {m : ι} (hm : c.next n = m) (x : K.X n)
    (hx : (K.d n m).hom x = 0) : ∃ z : K.cycles n, (K.iCycles n).hom z = x :=
  (ShortComplex.ab_exact_iff _).1 ((ShortComplex.mk _ _ (K.iCycles_d n m)).exact_of_f_is_kernel
    (K.cyclesIsKernel n m hm)) x hx

/-- The class map from the degree-`n` cycles of a complex of abelian groups onto its degree-`n`
homology is surjective. -/
lemma addCommGrpCat_homologyπ_surjective : Function.Surjective (K.homologyπ n).hom :=
  (AddCommGrpCat.epi_iff_surjective _).1 inferInstance

/-- The differential out of degree `n` of a complex of abelian groups kills every cycle of
degree `n`, on elements. -/
@[simp]
lemma addCommGrpCat_d_iCycles_apply (m : ι) (z : K.cycles n) :
    (K.d n m).hom ((K.iCycles n).hom z) = 0 := by
  rw [← AddCommGrpCat.comp_apply, K.iCycles_d, AddCommGrpCat.zero_apply]

/-- The underlying element of the cycle `K.toCycles m n y` is the boundary `K.d m n y`, on
elements of complexes of abelian groups. -/
@[simp]
lemma addCommGrpCat_iCycles_toCycles_apply (m : ι) (y : K.X m) :
    (K.iCycles n).hom ((K.toCycles m n).hom y) = (K.d m n).hom y := by
  rw [← AddCommGrpCat.comp_apply, toCycles_i]

/-- A chain map of complexes of abelian groups acts on cycles as it does on the underlying
elements. -/
@[simp]
lemma addCommGrpCat_iCycles_cyclesMap_apply {L : HomologicalComplex AddCommGrpCat c} (φ : K ⟶ L)
    (z : K.cycles n) :
    (L.iCycles n).hom ((cyclesMap φ n).hom z) = (φ.f n).hom ((K.iCycles n).hom z) := by
  rw [← AddCommGrpCat.comp_apply, cyclesMap_i, AddCommGrpCat.comp_apply]

/-- Homology maps commute with the class map from cycles, on elements of complexes of abelian
groups. -/
@[simp]
lemma addCommGrpCat_homologyMap_homologyπ_apply {L : HomologicalComplex AddCommGrpCat c}
    (φ : K ⟶ L) (z : K.cycles n) :
    (homologyMap φ n).hom ((K.homologyπ n).hom z) =
      (L.homologyπ n).hom ((cyclesMap φ n).hom z) := by
  rw [← AddCommGrpCat.comp_apply, homologyπ_naturality, AddCommGrpCat.comp_apply]

variable {n} in
/-- A degree-`n` cycle of a complex of abelian groups has zero homology class exactly when it is a
boundary, the image of an element of the term of degree `c.prev n`. -/
lemma addCommGrpCat_homologyπ_eq_zero_iff {m : ι} (hm : c.prev n = m) (z : K.cycles n) :
    (K.homologyπ n).hom z = 0 ↔ ∃ y : K.X m, (K.d m n).hom y = (K.iCycles n).hom z := by
  have hS := ShortComplex.exact_of_g_is_cokernel
    (ShortComplex.mk (K.toCycles m n) (K.homologyπ n) (K.toCycles_comp_homologyπ m n))
    (K.homologyIsCokernel m n hm)
  rw [ShortComplex.ab_exact_iff] at hS
  refine ⟨fun hz ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩
  · obtain ⟨y, rfl⟩ := hS z hz
    exact ⟨y, (K.addCommGrpCat_iCycles_toCycles_apply n m y).symm⟩
  · rw [← K.addCommGrpCat_iCycles_toCycles_apply n m y,
      (K.addCommGrpCat_iCycles_injective n).eq_iff] at hy
    rw [← hy, ← AddCommGrpCat.comp_apply, toCycles_comp_homologyπ, AddCommGrpCat.zero_apply]

end Homology

end HomologicalComplex
