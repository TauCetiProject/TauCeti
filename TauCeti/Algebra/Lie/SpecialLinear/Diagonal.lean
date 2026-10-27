/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.Algebra.Lie.GeneralLinear.DiagonalCartan
public import TauCeti.LinearAlgebra.Fin.PartialSums

/-!
# Simple-coroot coordinates on trace-zero diagonal matrices

The diagonal submodule of the native special linear Lie algebra has a basis of
adjacent diagonal differences over every commutative ring. Its coordinates are
nonempty initial sums of the diagonal entries. The construction includes rank zero
and uses the existing partial-sum linear equivalence.
-/

public section

namespace TauCeti

open LieAlgebra.SpecialLinear

attribute [local instance 100] LieRing.ofAssociativeRing

variable (r : ℕ) (A : Type*) [CommRing A]

/-- The diagonal matrices inside the native trace-zero matrix Lie algebra. -/
def specialLinearDiagonal : Submodule A (sl (Fin (r + 1)) A) :=
  (diagonalCartan A (Fin (r + 1))).toSubmodule.comap
    (sl (Fin (r + 1)) A).toSubmodule.subtype

/-- Membership in the special linear diagonal submodule is diagonality of the matrix. -/
@[simp]
theorem mem_specialLinearDiagonal_iff (X : sl (Fin (r + 1)) A) :
    X ∈ specialLinearDiagonal r A ↔ (X : Matrix (Fin (r + 1)) (Fin (r + 1)) A).IsDiag :=
  mem_diagonalCartan_iff_isDiag

/-- Reading the first diagonal entries identifies a trace-zero diagonal matrix with a tuple.
The final diagonal entry is minus the sum of that tuple. -/
def specialLinearDiagonalEquiv : specialLinearDiagonal r A ≃ₗ[A] (Fin r → A) where
  toFun X i := X.val.val i.castSucc i.castSucc
  invFun d := ⟨⟨Matrix.diagonal (Fin.snoc d (-∑ i, d i)), by
    simp [sl, Matrix.traceLinearMap, Matrix.trace, Fin.sum_univ_castSucc]⟩,
    (mem_specialLinearDiagonal_iff r A _).mpr (Matrix.isDiag_diagonal _)⟩
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    have hz : ∑ i : Fin (r + 1), X.val.val i i = 0 := X.val.property
    rw [Fin.sum_univ_castSucc] at hz
    have hl : X.val.val (Fin.last r) (Fin.last r) =
        -∑ i : Fin r, X.val.val i.castSucc i.castSucc := by
      apply eq_neg_iff_add_eq_zero.mpr
      simpa [add_comm] using hz
    have hd : X.val.val.IsDiag := (mem_specialLinearDiagonal_iff r A _).mp X.property
    ext i j
    by_cases hij : i = j
    · subst j
      induction i using Fin.lastCases with
      | last => simpa using hl.symm
      | cast i => simp
    · simp [Matrix.diagonal_apply_ne _ hij, hd hij]
  right_inv d := by
    funext i
    simp
  map_add' X Y := by
    funext i
    rfl
  map_smul' a X := by
    funext i
    (rfl)

/-- The first-entry coordinates are the corresponding matrix entries. -/
@[simp]
theorem specialLinearDiagonalEquiv_apply (X : specialLinearDiagonal r A) (i : Fin r) :
    specialLinearDiagonalEquiv r A X i = X.val.val i.castSucc i.castSucc :=
  (rfl)

/-- The inverse coordinate map appends the entry forced by trace zero. -/
@[simp]
theorem specialLinearDiagonalEquiv_symm_apply (d : Fin r → A) :
    ((specialLinearDiagonalEquiv r A).symm d).val.val =
      Matrix.diagonal (Fin.snoc d (-∑ i, d i)) :=
  (rfl)

/-- Simple-coroot coordinates are the nonempty initial sums of the diagonal entries. -/
noncomputable def specialLinearCorootEquiv :
    specialLinearDiagonal r A ≃ₗ[A] (Fin r → A) :=
  (specialLinearDiagonalEquiv r A).trans (partialSumsLinearEquiv A r)

/-- The coordinate at a simple coroot is the corresponding initial diagonal sum. -/
@[simp]
theorem specialLinearCorootEquiv_apply (X : specialLinearDiagonal r A) (i : Fin r) :
    specialLinearCorootEquiv r A X i =
      Fin.partialSum (fun j : Fin r ↦ X.val.val j.castSucc j.castSucc) i.succ := by
  simpa only [specialLinearCorootEquiv, LinearEquiv.trans_apply,
    partialSumsLinearEquiv_apply] using
    congrArg (fun d : Fin r → A ↦ Fin.partialSum d i.succ)
      (funext (specialLinearDiagonalEquiv_apply r A X))

/-- Every difference of two diagonal matrix units belongs to the diagonal submodule. -/
theorem singleSubSingle_mem_specialLinearDiagonal (i j : Fin (r + 1)) (a : A) :
    singleSubSingle i j a ∈ specialLinearDiagonal r A := by
  rw [mem_specialLinearDiagonal_iff, val_singleSubSingle]
  exact mem_diagonalCartan_iff_isDiag.mp
    ((diagonalCartan A (Fin (r + 1))).sub_mem
      (single_self_mem_diagonalCartan i a) (single_self_mem_diagonalCartan j a))

private theorem specialLinearDiagonalEquiv_singleSubSingle (i : Fin r) :
    specialLinearDiagonalEquiv r A
        ⟨singleSubSingle i.castSucc i.succ 1,
          singleSubSingle_mem_specialLinearDiagonal r A _ _ _⟩ =
      (partialSumsLinearEquiv A r).symm (Pi.single i 1) := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ r =>
    ext j
    induction j using Fin.cases with
    | zero =>
      simp [specialLinearDiagonalEquiv_apply, val_singleSubSingle, Matrix.single_apply,
        Pi.single_apply, eq_comm]
    | succ j =>
      simp [specialLinearDiagonalEquiv_apply, val_singleSubSingle, Matrix.single_apply,
        Fin.castSucc_succ, Pi.single_apply, eq_comm]
      simp only [← Fin.castSucc_succ, Fin.castSucc_inj]

/-- The adjacent diagonal differences form a basis of the trace-zero diagonal submodule. -/
noncomputable def specialLinearCorootBasis :
    Module.Basis (Fin r) A (specialLinearDiagonal r A) :=
  Module.Basis.ofEquivFun (specialLinearCorootEquiv r A)

/-- Simple-coroot basis coordinates are nonempty initial diagonal sums. -/
@[simp]
theorem specialLinearCorootBasis_repr (X : specialLinearDiagonal r A) (i : Fin r) :
    (specialLinearCorootBasis r A).repr X i =
      Fin.partialSum (fun j : Fin r ↦ X.val.val j.castSucc j.castSucc) i.succ := by
  rw [specialLinearCorootBasis, Module.Basis.ofEquivFun_repr_apply,
    specialLinearCorootEquiv_apply]

/-- The simple-coroot basis consists of the native adjacent diagonal differences. -/
@[simp]
theorem specialLinearCorootBasis_apply (i : Fin r) :
    (specialLinearCorootBasis r A i).val = singleSubSingle i.castSucc i.succ 1 := by
  have h : specialLinearCorootBasis r A i =
      ⟨singleSubSingle i.castSucc i.succ 1,
        singleSubSingle_mem_specialLinearDiagonal r A _ _ _⟩ := by
    apply (specialLinearCorootEquiv r A).injective
    have hb : specialLinearCorootEquiv r A (specialLinearCorootBasis r A i) =
        Pi.single i 1 := by
      ext j
      rw [specialLinearCorootEquiv_apply]
      have h := specialLinearCorootBasis_repr r A (specialLinearCorootBasis r A i) j
      simpa only [Module.Basis.repr_self, Finsupp.single_apply, Pi.single_apply, eq_comm]
        using h.symm
    rw [hb, specialLinearCorootEquiv, LinearEquiv.trans_apply,
      specialLinearDiagonalEquiv_singleSubSingle, LinearEquiv.apply_symm_apply]
  exact congrArg Subtype.val h

/-- Simple coroots commute over every coefficient ring. -/
theorem lie_specialLinearCoroot_eq_zero (s t : Fin r) :
    ⁅(specialLinearCorootBasis r A s).val, (specialLinearCorootBasis r A t).val⁆ = 0 := by
  apply Subtype.ext
  rw [LieSubalgebra.coe_bracket]
  exact lie_eq_zero_of_isDiag
    ((mem_specialLinearDiagonal_iff r A _).mp (specialLinearCorootBasis r A s).property)
    ((mem_specialLinearDiagonal_iff r A _).mp (specialLinearCorootBasis r A t).property)

/-- Summing adjacent coroots over an interval gives its endpoint difference. -/
theorem sum_Icc_specialLinearCoroot (i j : Fin r) (hij : i ≤ j) :
    ∑ t ∈ Finset.Icc i j, (specialLinearCorootBasis r A t).val =
      singleSubSingle i.castSucc j.succ (1 : A) := by
  apply Subtype.ext
  -- View the coercion as the additive inclusion so that `map_sum` applies.
  change (sl (Fin (r + 1)) A).incl _ = _
  simp only [map_sum, LieSubalgebra.coe_incl, specialLinearCorootBasis_apply,
    val_singleSubSingle]
  simpa only [neg_sub_neg] using
    (Fin.sum_Icc_sub hij (fun k : Fin (r + 1) ↦ -Matrix.single k k (1 : A)))

/-- Inverse simple-coroot coordinates reconstruct the corresponding linear combination of
adjacent diagonal differences. -/
theorem specialLinearCorootEquiv_symm_val (c : Fin r → A) :
    ((specialLinearCorootEquiv r A).symm c).val =
      ∑ i, c i • singleSubSingle i.castSucc i.succ 1 := by
  have hc (i : Fin r) :
      (specialLinearCorootBasis r A).repr ((specialLinearCorootEquiv r A).symm c) i =
        c i := by
    rw [specialLinearCorootBasis_repr, ← specialLinearCorootEquiv_apply,
      LinearEquiv.apply_symm_apply]
  have h := congrArg (fun X : specialLinearDiagonal r A ↦ X.val)
    ((specialLinearCorootBasis r A).sum_repr ((specialLinearCorootEquiv r A).symm c))
  simpa only [Submodule.coe_sum, Submodule.coe_smul, hc, specialLinearCorootBasis_apply]
    using h.symm

end TauCeti
