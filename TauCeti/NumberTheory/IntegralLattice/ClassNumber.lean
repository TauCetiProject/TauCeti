/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Genus
public import Mathlib.SetTheory.Cardinal.Finite
import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Classes

/-!
# Class sets and class numbers of integral lattices

The isometry classes of integral lattices in a rational vector space `V` form the quotient
`IsometryClass V` of `IntegralLattice V` by isometry. The classes in the genus of `L` form the
subset `L.genusClasses`, and the class number `h(L)` is its cardinality.

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
the class number is `1`.

## Main definitions

* `TauCeti.IntegralLattice.isometrySetoid`: isometry of integral lattices in `V`.
* `TauCeti.IntegralLattice.IsometryClass`: the isometry classes of integral lattices in `V`.
* `TauCeti.IntegralLattice.isometryClass`: the class `cls L` of a lattice.
* `TauCeti.IntegralLattice.isometryClassEquiv`: transport of classes along an ambient linear
  equivalence.
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

section IsometryClass

variable (V) in
/-- Isometry of integral lattices in a fixed rational space, as an equivalence relation. -/
def isometrySetoid : Setoid (IntegralLattice V) where
  r L M := Nonempty (Isometry L M)
  iseqv := ⟨fun L ↦ ⟨Isometry.refl L⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ ↦ ⟨e.trans f⟩⟩

/-- Two lattices are related by `isometrySetoid` exactly when they are isometric. -/
theorem isometrySetoid_apply {L M : IntegralLattice V} :
    isometrySetoid V L M ↔ Nonempty (Isometry L M) :=
  Iff.rfl

variable (V) in
/-- The isometry classes of integral lattices in a rational space `V`. -/
abbrev IsometryClass : Type u := Quotient (isometrySetoid V)

/-- The isometry class `cls L` of an integral lattice. -/
def isometryClass (L : IntegralLattice V) : IsometryClass V :=
  Quotient.mk _ L

/-- Two lattices have the same isometry class exactly when they are isometric. -/
@[simp]
theorem isometryClass_eq_isometryClass_iff {L M : IntegralLattice V} :
    L.isometryClass = M.isometryClass ↔ Nonempty (Isometry L M) :=
  Quotient.eq

/-- Isometric lattices have the same isometry class. -/
theorem Isometry.isometryClass_eq {L M : IntegralLattice V} (e : Isometry L M) :
    L.isometryClass = M.isometryClass :=
  isometryClass_eq_isometryClass_iff.mpr ⟨e⟩

/-- Every isometry class is the class of a lattice. -/
theorem isometryClass_surjective :
    Function.Surjective (isometryClass : IntegralLattice V → IsometryClass V) :=
  Quotient.mk_surjective

/-- A chosen representative of an isometry class has that class. -/
@[simp]
theorem isometryClass_out (c : IsometryClass V) : c.out.isometryClass = c :=
  Quotient.out_eq c

/-- Transport along a rational linear equivalence `V ≃ W` identifies the isometry classes of
integral lattices in `V` with those in `W`. -/
noncomputable def isometryClassEquiv (f : V ≃ₗ[ℚ] W) : IsometryClass V ≃ IsometryClass W where
  toFun := Quotient.map (·.transport f) fun M N ⟨e⟩ ↦
    ⟨((M.transportIsometry f).symm.trans e).trans (N.transportIsometry f)⟩
  invFun := Quotient.map (·.transport f.symm) fun M N ⟨e⟩ ↦
    ⟨((M.transportIsometry f.symm).symm.trans e).trans (N.transportIsometry f.symm)⟩
  left_inv c := by
    obtain ⟨M, rfl⟩ := isometryClass_surjective c
    exact (((M.transportIsometry f).trans
      ((M.transport f).transportIsometry f.symm)).isometryClass_eq).symm
  right_inv c := by
    obtain ⟨M, rfl⟩ := isometryClass_surjective c
    exact (((M.transportIsometry f.symm).trans
      ((M.transport f.symm).transportIsometry f)).isometryClass_eq).symm

/-- `isometryClassEquiv f` sends the class of `M` to the class of its transport along `f`. -/
@[simp]
theorem isometryClassEquiv_isometryClass (f : V ≃ₗ[ℚ] W) (M : IntegralLattice V) :
    isometryClassEquiv f M.isometryClass = (M.transport f).isometryClass :=
  (rfl)

/-- The inverse of `isometryClassEquiv f` sends the class of `M` to the class of its transport
along `f.symm`. -/
@[simp]
theorem isometryClassEquiv_symm_isometryClass (f : V ≃ₗ[ℚ] W) (M : IntegralLattice W) :
    (isometryClassEquiv f).symm M.isometryClass = (M.transport f.symm).isometryClass :=
  (rfl)

end IsometryClass

section GenusClasses

/-- The classes in the genus of `L`: the isometry classes of the lattices in the ambient space of
`L` which have the same genus as `L`. -/
def genusClasses (L : IntegralLattice V) : Set (IsometryClass V) :=
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
theorem mem_genusClasses_iff {L : IntegralLattice V} {c : IsometryClass V} :
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
theorem isometryClassEquiv_mem_genusClasses_iff (f : V ≃ₗ[ℚ] W) {L : IntegralLattice V}
    {L' : IntegralLattice W} (h : L.SameGenus L') (c : IsometryClass V) :
    isometryClassEquiv f c ∈ L'.genusClasses ↔ c ∈ L.genusClasses := by
  obtain ⟨M, rfl⟩ := isometryClass_surjective c
  simp only [isometryClassEquiv_isometryClass, isometryClass_mem_genusClasses_iff]
  have hM : M.SameGenus (M.transport f) := (M.transportIsometry f).sameGenus
  exact ⟨fun h' ↦ (h.trans h').trans hM.symm, fun h' ↦ (h.symm.trans h').trans hM⟩

/-- Lattices of the same genus have ambient spaces of the same dimension. -/
private theorem SameGenus.nonempty_linearEquiv {L : IntegralLattice V} {M : IntegralLattice W}
    (h : L.SameGenus M) : Nonempty (V ≃ₗ[ℚ] W) := by
  have := L.finiteDimensional
  have := M.finiteDimensional
  refine FiniteDimensional.nonempty_linearEquiv_of_finrank_eq ?_
  rw [← L.finrank_carrier, ← M.finrank_carrier, h.finrank_eq]

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
  exact Nat.card_congr <| (isometryClassEquiv f).subtypeEquiv fun c ↦
    (isometryClassEquiv_mem_genusClasses_iff f h c).symm

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
  refine Set.finite_coe_iff.mp <| finite_of_pairwise_isEmpty_isometry
    (fun c : L.genusClasses ↦ c.1.out) (fun c ↦ (hgen c).isPosDef_iff.mp hL)
    (fun c ↦ (hgen c).finrank_eq.symm) (fun c ↦ (hgen c).determinant_eq.symm.le)
    fun c d hcd ↦ ⟨fun e ↦ hcd (Subtype.ext ?_)⟩
  rw [← isometryClass_out c.1, ← isometryClass_out d.1]
  exact e.isometryClass_eq

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
  have e' := e.smul (-1)
  rw [← neg_def, ← neg_def, neg_neg, neg_neg] at e'
  apply Subtype.ext
  rw [← isometryClass_out c.1, ← isometryClass_out d.1]
  exact e'.isometryClass_eq

/-- A negative definite lattice has positive class number. -/
theorem IsNegDef.classNumber_pos {L : IntegralLattice V} (hL : L.IsNegDef) :
    0 < L.classNumber :=
  classNumber_pos_iff.mpr hL.finite_genusClasses

end ClassNumber

section RankLeOne

/-- **Lattices of rank at most one are classified by their determinant.** Two integral lattices of
equal rank at most one and equal determinant are isometric: in rank one the Gram matrix of any
basis is the `1 × 1` matrix of the determinant. -/
theorem nonempty_isometry_of_finrank_le_one {L : IntegralLattice V} {M : IntegralLattice W}
    (hrank : finrank ℤ L = finrank ℤ M) (hle : finrank ℤ L ≤ 1)
    (hdet : L.determinant = M.determinant) : Nonempty (Isometry L M) := by
  classical
  let b := finBasisOfFinrankEq ℤ L rfl
  let b' := finBasisOfFinrankEq ℤ M hrank.symm
  refine ⟨Isometry.ofGramMatrixEq b b' (Matrix.ext fun i j ↦ ?_)⟩
  let _ : Unique (Fin (finrank ℤ L)) := ⟨⟨i⟩, fun k ↦ Fin.ext (by omega)⟩
  obtain rfl : i = j := Subsingleton.elim i j
  have hL := L.determinant_eq_gramDet b
  have hM := M.determinant_eq_gramDet b'
  rw [gramDet_def, Matrix.det_unique] at hL hM
  exact hL.symm.trans (hdet.trans hM)

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

/-- In rank at most one the class number is `1`. -/
theorem classNumber_eq_one_of_finrank_le_one {L : IntegralLattice V}
    (hle : finrank ℤ L ≤ 1) : L.classNumber = 1 := by
  rw [classNumber_def, genusClasses_eq_singleton_of_finrank_le_one hle, Nat.card_unique]

end RankLeOne

end TauCeti.IntegralLattice
