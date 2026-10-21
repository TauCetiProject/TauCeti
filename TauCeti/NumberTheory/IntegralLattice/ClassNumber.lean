/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Genus
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Class
public import Mathlib.SetTheory.Cardinal.Finite
import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Classes

/-!
# Class sets and class numbers of integral lattices

The classes in the genus of `L` form the subset `L.genusClasses` of the isometry classes
`IsometryQuotient V` of integral lattices in the ambient space `V` of `L`, and the class number
`h(L)` is its cardinality.

All lattices in one genus have the same rank, so they all live, up to isometry, in the ambient
space of `L`: every lattice in the genus of `L`, in any rational space, is isometric to one in
`V` (`TauCeti.IntegralLattice.SameGenus.exists_isometry`). Accordingly the class number depends
only on the genus and not on the ambient space used to count it
(`TauCeti.IntegralLattice.SameGenus.classNumber_eq`).

The class number is defined for every lattice, as a natural-number cardinality, and is `0`
exactly when the genus contains infinitely many classes. Finiteness has different proofs for
different kinds of lattices. This file proves it for definite lattices: for positive definite
ones it is a consequence of reduction theory
(`TauCeti.IntegralLattice.finite_of_pairwise_isEmpty_isometry`), and the negative definite case
follows by negating the form. It also computes the class set directly in rank at most one, where
the class number is `1` by the determinant classification
`TauCeti.IntegralLattice.nonempty_isometry_of_finrank_le_one`.

## Main definitions

* `TauCeti.IntegralLattice.genusClasses`: the classes in the genus of `L`.
* `TauCeti.IntegralLattice.classNumber`: the class number `h(L)`.

## Main results

* `TauCeti.IntegralLattice.isometryClass_mem_genusClasses_iff`: the class of `M` lies in the
  genus of `L` exactly when `M` has the same genus as `L`.
* `TauCeti.IntegralLattice.SameGenus.classNumber_eq`: lattices of the same genus, in possibly
  different ambient spaces, have the same class number.
* `TauCeti.IntegralLattice.IsPosDef.finite_genusClasses` and
  `TauCeti.IntegralLattice.IsNegDef.finite_genusClasses`: a definite genus contains finitely many
  classes.
* `TauCeti.IntegralLattice.classNumber_eq_one_of_finrank_le_one`: in rank at most one the genus is
  a single class.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §102A, for classes, genera and class numbers.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 9, §1.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} {W : Type v} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

section GenusClasses

/-- The classes in the genus of `L`: the isometry classes of the lattices in the ambient space of
`L` which have the same genus as `L`. -/
def genusClasses (L : IntegralLattice V) : Set (IsometryQuotient V) :=
  isometryClass '' {M | L.SameGenus M}

/-- The class of `M` lies in the genus of `L` exactly when `M` has the same genus as `L`. -/
@[simp]
theorem isometryClass_mem_genusClasses_iff {L M : IntegralLattice V} :
    M.isometryClass ∈ L.genusClasses ↔ L.SameGenus M := by
  refine ⟨?_, fun h ↦ ⟨M, h, rfl⟩⟩
  rintro ⟨N, hN, hNM⟩
  obtain ⟨e⟩ := isometryClass_eq_isometryClass_iff.mp hNM
  exact SameGenus.trans hN e.sameGenus

/-- The genus of `L` contains the class of `L`. -/
theorem isometryClass_mem_genusClasses (L : IntegralLattice V) :
    L.isometryClass ∈ L.genusClasses :=
  isometryClass_mem_genusClasses_iff.mpr (SameGenus.refl L)

/-- The genus of a lattice contains at least one class. -/
theorem genusClasses_nonempty (L : IntegralLattice V) : L.genusClasses.Nonempty :=
  ⟨_, L.isometryClass_mem_genusClasses⟩

/-- A class lies in the genus of `L` exactly when its chosen representative has the same genus
as `L`. -/
theorem mem_genusClasses_iff {L : IntegralLattice V} {c : IsometryQuotient V} :
    c ∈ L.genusClasses ↔ L.SameGenus c.out := by
  rw [← isometryClass_mem_genusClasses_iff, isometryClass_out]

/-- Two lattices in `V` have the same classes in their genus exactly when they have the same
genus. -/
theorem genusClasses_eq_genusClasses_iff {L M : IntegralLattice V} :
    L.genusClasses = M.genusClasses ↔ L.SameGenus M := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← isometryClass_mem_genusClasses_iff, h]
    exact M.isometryClass_mem_genusClasses
  · ext c
    obtain ⟨N, rfl⟩ := isometryClass_surjective c
    simp only [isometryClass_mem_genusClasses_iff]
    exact ⟨h.symm.trans, h.trans⟩

/-- Lattices of the same genus have the same classes in their genus. -/
theorem SameGenus.genusClasses_eq {L M : IntegralLattice V} (h : L.SameGenus M) :
    L.genusClasses = M.genusClasses :=
  genusClasses_eq_genusClasses_iff.mpr h

/-- Transport along `f : V ≃ W` carries the classes in the genus of `L` onto the classes in the
genus of any lattice in `W` with the same genus as `L`. -/
theorem isometryQuotientEquiv_mem_genusClasses_iff (f : V ≃ₗ[ℚ] W) {L : IntegralLattice V}
    {L' : IntegralLattice W} (h : L.SameGenus L') (c : IsometryQuotient V) :
    isometryQuotientEquiv f c ∈ L'.genusClasses ↔ c ∈ L.genusClasses := by
  obtain ⟨M, rfl⟩ := isometryClass_surjective c
  simp only [isometryQuotientEquiv_isometryClass, isometryClass_mem_genusClasses_iff]
  have hM : M.SameGenus (M.transport f) := (M.transportIsometry f).sameGenus
  exact ⟨fun h' ↦ (h.trans h').trans hM.symm, fun h' ↦ (h.symm.trans h').trans hM⟩

/-- Every lattice of the same genus as `L`, in any rational space, is isometric to a lattice in
the ambient space of `L` of that genus. So `L.genusClasses` accounts for every class in the genus
of `L`. -/
theorem SameGenus.exists_isometry {L : IntegralLattice V} {M : IntegralLattice W}
    (h : L.SameGenus M) : ∃ N : IntegralLattice V, L.SameGenus N ∧ Nonempty (Isometry M N) := by
  obtain ⟨f⟩ := h.symm.nonempty_linearEquiv
  exact ⟨M.transport f, h.trans (M.transportIsometry f).sameGenus, ⟨M.transportIsometry f⟩⟩

end GenusClasses

section ClassNumber

/-- The class number `h(L)`: the number of isometry classes in the genus of `L`. It is `0` when
the genus contains infinitely many classes. -/
noncomputable def classNumber (L : IntegralLattice V) : ℕ :=
  Nat.card L.genusClasses

/-- The class number is the cardinality of the set of classes in the genus. -/
theorem classNumber_def (L : IntegralLattice V) : L.classNumber = Nat.card L.genusClasses :=
  (rfl)

/-- The class number is positive exactly when the genus contains finitely many classes. -/
theorem classNumber_pos_iff {L : IntegralLattice V} :
    0 < L.classNumber ↔ L.genusClasses.Finite := by
  rw [classNumber_def, Nat.card_pos_iff, Set.finite_coe_iff]
  exact and_iff_right L.genusClasses_nonempty.to_subtype

/-- **The class number is an invariant of the genus.** Lattices of the same genus have the same
class number, even when they live in different ambient spaces. -/
theorem SameGenus.classNumber_eq {L : IntegralLattice V} {M : IntegralLattice W}
    (h : L.SameGenus M) : L.classNumber = M.classNumber := by
  obtain ⟨f⟩ := h.nonempty_linearEquiv
  exact Nat.card_congr <| (isometryQuotientEquiv f).subtypeEquiv fun c ↦
    (isometryQuotientEquiv_mem_genusClasses_iff f h c).symm

/-- Isometric lattices have the same class number. -/
theorem Isometry.classNumber_eq {L : IntegralLattice V} {M : IntegralLattice W}
    (e : Isometry L M) : L.classNumber = M.classNumber :=
  e.sameGenus.classNumber_eq

/-- **A positive definite genus contains finitely many classes.** The lattices of the genus all
have the rank and determinant of `L`, so this is the finiteness of positive definite classes of
given rank and bounded determinant. -/
theorem IsPosDef.finite_genusClasses {L : IntegralLattice V} (hL : L.IsPosDef) :
    L.genusClasses.Finite := by
  have hgen (c : L.genusClasses) : L.SameGenus c.1.out := mem_genusClasses_iff.mp c.2
  exact Set.finite_coe_iff.mp <| finite_of_pairwise_isEmpty_isometry
    (fun c : L.genusClasses ↦ c.1.out) (fun c ↦ (hgen c).isPosDef_iff.mp hL)
    (fun c ↦ (hgen c).finrank_eq.symm) (fun c ↦ (hgen c).determinant_eq.symm.le)
    fun c d hcd ↦ ⟨fun e ↦ hcd (Subtype.ext (IsometryQuotient.eq_of_isometry_out e))⟩

/-- A positive definite lattice has positive class number. -/
theorem IsPosDef.classNumber_pos {L : IntegralLattice V} (hL : L.IsPosDef) :
    0 < L.classNumber :=
  classNumber_pos_iff.mpr hL.finite_genusClasses

/-- **A negative definite genus contains finitely many classes.** Negating the form carries the
classes in the genus of `L` injectively into the classes in the positive definite genus of `-L`. -/
theorem IsNegDef.finite_genusClasses {L : IntegralLattice V} (hL : L.IsNegDef) :
    L.genusClasses.Finite := by
  have := ((isPosDef_neg_iff L).mpr hL).finite_genusClasses.to_subtype
  have hgen (c : L.genusClasses) : (-L).SameGenus (-c.1.out) :=
    (mem_genusClasses_iff.mp c.2).smul (by norm_num)
  refine Set.finite_coe_iff.mp <| Finite.of_injective
    (fun c : L.genusClasses ↦ (⟨(-c.1.out).isometryClass,
      isometryClass_mem_genusClasses_iff.mpr (hgen c)⟩ : (-L).genusClasses)) fun c d hcd ↦ ?_
  obtain ⟨e⟩ := isometryClass_eq_isometryClass_iff.mp (congrArg Subtype.val hcd)
  -- `-L` is `(-1 : ℤ) • L` by definition, so `e.smul (-1)` is an isometry of the negations.
  have e' : Isometry (-(-c.1.out)) (-(-d.1.out)) := e.smul (-1)
  exact Subtype.ext <| IsometryQuotient.eq_of_isometry_out <|
    (Isometry.ofEq (neg_neg c.1.out).symm).trans <| e'.trans (Isometry.ofEq (neg_neg d.1.out))

/-- A negative definite lattice has positive class number. -/
theorem IsNegDef.classNumber_pos {L : IntegralLattice V} (hL : L.IsNegDef) :
    0 < L.classNumber :=
  classNumber_pos_iff.mpr hL.finite_genusClasses

end ClassNumber

section RankLeOne

/-- In rank at most one the genus of `L` is the single class of `L`. -/
theorem genusClasses_eq_singleton_of_finrank_le_one {L : IntegralLattice V}
    (hle : finrank ℤ L ≤ 1) : L.genusClasses = {L.isometryClass} := by
  ext c
  obtain ⟨M, rfl⟩ := isometryClass_surjective c
  rw [isometryClass_mem_genusClasses_iff, Set.mem_singleton_iff,
    isometryClass_eq_isometryClass_iff]
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ e.symm.sameGenus⟩
  obtain ⟨e⟩ := nonempty_isometry_of_finrank_le_one h.finrank_eq hle h.determinant_eq
  exact ⟨e.symm⟩

/-- In rank at most one the class number is `1` by the determinant classification
`TauCeti.IntegralLattice.nonempty_isometry_of_finrank_le_one`. -/
theorem classNumber_eq_one_of_finrank_le_one {L : IntegralLattice V}
    (hle : finrank ℤ L ≤ 1) : L.classNumber = 1 := by
  rw [classNumber_def, genusClasses_eq_singleton_of_finrank_le_one hle, Nat.card_unique]

end RankLeOne

end TauCeti.IntegralLattice
